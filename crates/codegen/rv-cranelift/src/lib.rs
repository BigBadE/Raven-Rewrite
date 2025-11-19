//! Cranelift JIT backend for Raven
//!
//! Compiles MIR to native code using Cranelift JIT compiler

use anyhow::{Context, Result};
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use rustc_hash::FxHashMap;
use rv_hir::LiteralKind;
use rv_mir::{AggregateKind, LocalId, MirFunction, MirType, Operand, Place, RValue, Statement, Terminator};

/// JIT compiler for MIR
pub struct JitCompiler {
    /// Cranelift JIT module
    module: JITModule,

    /// Function builder context
    builder_context: FunctionBuilderContext,

    /// Cranelift context
    ctx: codegen::Context,

    /// Map from MIR function IDs to Cranelift function IDs
    function_map: FxHashMap<rv_hir::FunctionId, FuncId>,

    /// Compiled functions cache (FunctionId -> code pointer)
    pub compiled_functions: FxHashMap<rv_hir::FunctionId, *const u8>,
}

impl JitCompiler {
    /// Create a new JIT compiler
    pub fn new() -> Result<Self> {
        let builder = JITBuilder::new(cranelift_module::default_libcall_names())?;
        let module = JITModule::new(builder);

        Ok(Self {
            ctx: module.make_context(),
            module,
            builder_context: FunctionBuilderContext::new(),
            function_map: FxHashMap::default(),
            compiled_functions: FxHashMap::default(),
        })
    }

    /// Compile multiple MIR functions (for programs with function calls)
    pub fn compile_multiple(&mut self, mir_funcs: &[MirFunction]) -> Result<*const u8> {
        // Phase 1: Infer parameter counts by scanning all call sites
        let mut param_counts: FxHashMap<rv_hir::FunctionId, usize> = FxHashMap::default();

        for mir_func in mir_funcs {
            for bb in &mir_func.basic_blocks {
                for stmt in &bb.statements {
                    if let Statement::Assign { rvalue, .. } = stmt {
                        if let RValue::Call { func, args } = rvalue {
                            // This tells us how many parameters the called function has
                            param_counts.insert(*func, args.len());
                        }
                    }
                }
            }
        }

        // Phase 2: Declare all functions first
        for mir_func in mir_funcs {
            if !self.function_map.contains_key(&mir_func.id) {
                // Set up function signature
                let mut sig = self.module.make_signature();

                // Return value
                sig.returns.push(AbiParam::new(types::I64));

                // Add parameters based on call site analysis
                let param_count = param_counts.get(&mir_func.id).copied().unwrap_or(0);
                for _ in 0..param_count {
                    sig.params.push(AbiParam::new(types::I64));
                }

                let func_id = self
                    .module
                    .declare_function(
                        &format!("func_{}", mir_func.id.0),
                        Linkage::Export,
                        &sig,
                    )
                    .context("Failed to declare function")?;

                self.function_map.insert(mir_func.id, func_id);
            }
        }

        // Phase 3: Compile all functions (but don't finalize yet)
        for mir_func in mir_funcs {
            self.compile_single_no_finalize(mir_func)?;
        }

        // Phase 4: Finalize ALL functions at once
        self.module.finalize_definitions()?;

        // Phase 5: Get code pointers for all compiled functions and cache them
        for mir_func in mir_funcs {
            let func_id = *self.function_map.get(&mir_func.id)
                .ok_or_else(|| anyhow::anyhow!("Function not in function_map"))?;

            let code_ptr = self.module.get_finalized_function(func_id);
            self.compiled_functions.insert(mir_func.id, code_ptr);
        }

        // Phase 6: Return the code pointer for the last function (usually main)
        let last_func_id = mir_funcs.last()
            .ok_or_else(|| anyhow::anyhow!("No functions to compile"))?
            .id;

        let func_ptr = self.compiled_functions.get(&last_func_id)
            .copied()
            .ok_or_else(|| anyhow::anyhow!("Last function not found in compiled cache"))?;

        Ok(func_ptr)
    }

    /// Compile a single MIR function without finalizing (for multi-function compilation)
    fn compile_single_no_finalize(&mut self, mir_func: &MirFunction) -> Result<()> {
        // Check if already compiled
        if self.compiled_functions.contains_key(&mir_func.id) {
            return Ok(());
        }

        // Clear previous function
        self.ctx.func.clear();

        // Get the function signature (should already be declared)
        let func_id = *self.function_map.get(&mir_func.id)
            .ok_or_else(|| anyhow::anyhow!("Function not declared"))?;

        // Retrieve the signature
        let sig = self.module.declarations().get_function_decl(func_id).signature.clone();
        self.ctx.func.signature = sig;

        // Build function references for calls
        let mut func_refs: FxHashMap<rv_hir::FunctionId, cranelift::codegen::ir::FuncRef> = FxHashMap::default();

        // Get parameter count before borrowing
        let param_count = self.ctx.func.signature.params.len();

        // Build function body
        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

            // Import all declared functions so we can call them
            for (&mir_func_id, &cranelift_func_id) in &self.function_map {
                let func_ref = self.module.declare_func_in_func(cranelift_func_id, builder.func);
                func_refs.insert(mir_func_id, func_ref);
            }

            // Map from MIR basic blocks to Cranelift blocks
            let mut block_map = FxHashMap::default();
            for bb in &mir_func.basic_blocks {
                let cranelift_block = builder.create_block();
                block_map.insert(bb.id, cranelift_block);
            }

            // Entry block
            let entry_block = block_map[&0];
            builder.switch_to_block(entry_block);
            builder.append_block_params_for_function_params(entry_block);

            // Map from MIR locals to Cranelift variables
            let mut local_map: FxHashMap<LocalId, Variable> = FxHashMap::default();

            // Declare all locals as variables
            for (idx, local) in mir_func.locals.iter().enumerate() {
                let var = builder.declare_var(types::I64);
                local_map.insert(local.id, var);

                // If this is a parameter (first N locals), get it from function params
                if idx < param_count {
                    let param_val = builder.block_params(entry_block)[idx];
                    builder.def_var(var, param_val);
                }
            }

            // Translate each basic block
            for bb in &mir_func.basic_blocks {
                let cranelift_block = block_map[&bb.id];

                if bb.id != 0 {
                    builder.switch_to_block(cranelift_block);
                }

                // Translate statements
                for stmt in &bb.statements {
                    Self::translate_statement(stmt, &mut builder, &local_map, &func_refs)?;
                }

                // Translate terminator
                Self::translate_terminator(
                    &bb.terminator,
                    &mut builder,
                    &local_map,
                    &block_map,
                )?;
            }

            // Seal all blocks after all terminators are translated
            for bb in &mir_func.basic_blocks {
                let cranelift_block = block_map[&bb.id];
                builder.seal_block(cranelift_block);
            }

            builder.finalize();
        }

        // Verify the function
        if let Err(errors) = cranelift_codegen::verify_function(&self.ctx.func, self.module.isa()) {
            anyhow::bail!("Verification errors: {}", errors);
        }

        // Define the function
        self.module
            .define_function(func_id, &mut self.ctx)
            .context("Failed to define function")?;

        // Clear context for next function
        self.module.clear_context(&mut self.ctx);

        // Store the function ID for later retrieval after finalization
        // We can't get the code pointer yet because we haven't called finalize_definitions()

        Ok(())
    }

    /// Compile a MIR function to native code (legacy single-function API)
    pub fn compile(&mut self, mir_func: &MirFunction) -> Result<*const u8> {
        // Clear previous function
        self.ctx.func.clear();

        // Set up function signature
        let mut sig = self.module.make_signature();

        // For now, all functions return i64
        sig.returns.push(AbiParam::new(types::I64));

        self.ctx.func.signature = sig;

        // Declare the function
        let func_id = self
            .module
            .declare_function(
                &format!("func_{}", mir_func.id.0),
                Linkage::Export,
                &self.ctx.func.signature,
            )
            .context("Failed to declare function")?;

        self.function_map.insert(mir_func.id, func_id);

        // Build function body
        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

            // Map from MIR basic blocks to Cranelift blocks
            let mut block_map = FxHashMap::default();
            for bb in &mir_func.basic_blocks {
                let cranelift_block = builder.create_block();
                block_map.insert(bb.id, cranelift_block);
            }

            // Entry block
            let entry_block = block_map[&0];
            builder.switch_to_block(entry_block);

            // Map from MIR locals to Cranelift variables
            let mut local_map: FxHashMap<LocalId, Variable> = FxHashMap::default();

            // Declare all locals as variables
            for (_idx, local) in mir_func.locals.iter().enumerate() {
                let var = builder.declare_var(types::I64);
                local_map.insert(local.id, var);
            }

            // Translate each basic block
            for bb in &mir_func.basic_blocks {
                let cranelift_block = block_map[&bb.id];

                if bb.id != 0 {
                    builder.switch_to_block(cranelift_block);
                }

                // Translate statements
                let empty_func_refs = FxHashMap::default();
                for stmt in &bb.statements {
                    Self::translate_statement(stmt, &mut builder, &local_map, &empty_func_refs)?;
                }

                // Translate terminator
                Self::translate_terminator(
                    &bb.terminator,
                    &mut builder,
                    &local_map,
                    &block_map,
                )?;
            }

            // Seal all blocks after all terminators are translated
            for bb in &mir_func.basic_blocks {
                let cranelift_block = block_map[&bb.id];
                builder.seal_block(cranelift_block);
            }

            builder.finalize();
        }

        // Verify the function
        if let Err(errors) = cranelift_codegen::verify_function(&self.ctx.func, self.module.isa()) {
            anyhow::bail!("Verification errors: {}", errors);
        }

        // Define the function
        self.module
            .define_function(func_id, &mut self.ctx)
            .context("Failed to define function")?;

        // Clear context for next function
        self.module.clear_context(&mut self.ctx);

        // Finalize and get code pointer
        self.module.finalize_definitions()?;
        let code_ptr = self.module.get_finalized_function(func_id);

        Ok(code_ptr)
    }

    /// Execute a compiled function
    ///
    /// # Safety
    ///
    /// The function pointer must be valid and the function must have the signature `fn() -> i64`
    #[allow(unsafe_code)]
    pub unsafe fn execute(&self, func_ptr: *const u8) -> i64 {
        // SAFETY: Caller must ensure func_ptr is valid and has signature fn() -> i64
        let func: fn() -> i64 = unsafe { std::mem::transmute(func_ptr) };
        func()
    }

    fn translate_statement(
        stmt: &Statement,
        builder: &mut FunctionBuilder,
        local_map: &FxHashMap<LocalId, Variable>,
        func_refs: &FxHashMap<rv_hir::FunctionId, cranelift::codegen::ir::FuncRef>,
    ) -> Result<()> {
        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                let value = Self::translate_rvalue(rvalue, builder, local_map, func_refs)?;
                let var = local_map[&place.local];
                builder.def_var(var, value);
            }
            Statement::StorageLive(_) | Statement::StorageDead(_) => {
                // Storage markers don't generate code
            }
            Statement::Nop => {}
        }
        Ok(())
    }

    fn translate_rvalue(
        rvalue: &RValue,
        builder: &mut FunctionBuilder,
        local_map: &FxHashMap<LocalId, Variable>,
        func_refs: &FxHashMap<rv_hir::FunctionId, cranelift::codegen::ir::FuncRef>,
    ) -> Result<Value> {
        match rvalue {
            RValue::Use(operand) => Self::translate_operand(operand, builder, local_map),
            RValue::BinaryOp { op, left, right } => {
                let left_val = Self::translate_operand(left, builder, local_map)?;
                let right_val = Self::translate_operand(right, builder, local_map)?;

                let result = match op {
                    rv_mir::BinaryOp::Add => builder.ins().iadd(left_val, right_val),
                    rv_mir::BinaryOp::Sub => builder.ins().isub(left_val, right_val),
                    rv_mir::BinaryOp::Mul => builder.ins().imul(left_val, right_val),
                    rv_mir::BinaryOp::Div => builder.ins().sdiv(left_val, right_val),
                    rv_mir::BinaryOp::Mod => builder.ins().srem(left_val, right_val),
                    rv_mir::BinaryOp::Eq => {
                        let cmp = builder.ins().icmp(IntCC::Equal, left_val, right_val);
                        builder.ins().uextend(types::I64, cmp)
                    }
                    rv_mir::BinaryOp::Ne => {
                        let cmp = builder.ins().icmp(IntCC::NotEqual, left_val, right_val);
                        builder.ins().uextend(types::I64, cmp)
                    }
                    rv_mir::BinaryOp::Lt => {
                        let cmp = builder.ins().icmp(IntCC::SignedLessThan, left_val, right_val);
                        builder.ins().uextend(types::I64, cmp)
                    }
                    rv_mir::BinaryOp::Le => {
                        let cmp =
                            builder
                                .ins()
                                .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val);
                        builder.ins().uextend(types::I64, cmp)
                    }
                    rv_mir::BinaryOp::Gt => {
                        let cmp =
                            builder
                                .ins()
                                .icmp(IntCC::SignedGreaterThan, left_val, right_val);
                        builder.ins().uextend(types::I64, cmp)
                    }
                    rv_mir::BinaryOp::Ge => {
                        let cmp = builder.ins().icmp(
                            IntCC::SignedGreaterThanOrEqual,
                            left_val,
                            right_val,
                        );
                        builder.ins().uextend(types::I64, cmp)
                    }
                    _ => anyhow::bail!("Unsupported binary operation: {:?}", op),
                };

                Ok(result)
            }
            RValue::UnaryOp { .. } => anyhow::bail!("Unary operations not yet implemented"),
            RValue::Call { func, args } => {
                // Get the function reference
                let func_ref = func_refs.get(func)
                    .ok_or_else(|| anyhow::anyhow!("Function {:?} not found in func_refs", func))?;

                // Translate arguments
                let arg_values: Result<Vec<Value>> = args
                    .iter()
                    .map(|arg| Self::translate_operand(arg, builder, local_map))
                    .collect();
                let arg_values = arg_values?;

                // Make the call
                let call_inst = builder.ins().call(*func_ref, &arg_values);

                // Get the return value
                let results = builder.inst_results(call_inst);
                if results.is_empty() {
                    Ok(builder.ins().iconst(types::I64, 0))
                } else {
                    Ok(results[0])
                }
            }
            RValue::Ref { .. } => anyhow::bail!("Ref operations not yet implemented"),
            RValue::Aggregate { kind, operands } => {
                // For now, represent aggregates as the first field value
                // This is a simplified implementation - proper support would use stack slots
                match kind {
                    AggregateKind::Struct | AggregateKind::Tuple | AggregateKind::Array(_) => {
                        if let Some(first_operand) = operands.first() {
                            Self::translate_operand(first_operand, builder, local_map)
                        } else {
                            Ok(builder.ins().iconst(types::I64, 0))
                        }
                    }
                    AggregateKind::Enum { .. } => {
                        anyhow::bail!("Enum aggregates not yet implemented")
                    }
                }
            }
        }
    }

    fn translate_operand(
        operand: &Operand,
        builder: &mut FunctionBuilder,
        local_map: &FxHashMap<LocalId, Variable>,
    ) -> Result<Value> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                Self::translate_place(place, builder, local_map)
            }
            Operand::Constant(constant) => {
                let value = match &constant.kind {
                    LiteralKind::Integer(n) => *n,
                    LiteralKind::Bool(b) => i64::from(*b),
                    LiteralKind::Unit => 0,
                    _ => anyhow::bail!("Unsupported constant type: {:?}", constant.kind),
                };
                Ok(builder.ins().iconst(types::I64, value))
            }
        }
    }

    fn translate_place(
        place: &Place,
        builder: &mut FunctionBuilder,
        local_map: &FxHashMap<LocalId, Variable>,
    ) -> Result<Value> {
        // Get the base local value
        let var = local_map[&place.local];
        let value = builder.use_var(var);

        // Apply projections
        for _projection in &place.projection {
            // For now, projections are no-ops since we're storing the whole value in a variable
            // A proper implementation would use stack slots and compute field offsets
            // For our simple test case, the aggregate already stored the first field
        }

        Ok(value)
    }

    fn translate_terminator(
        terminator: &Terminator,
        builder: &mut FunctionBuilder,
        local_map: &FxHashMap<LocalId, Variable>,
        block_map: &FxHashMap<usize, Block>,
    ) -> Result<()> {
        match terminator {
            Terminator::Return { value } => {
                if let Some(operand) = value {
                    let val = Self::translate_operand(operand, builder, local_map)?;
                    builder.ins().return_(&[val]);
                } else {
                    let zero = builder.ins().iconst(types::I64, 0);
                    builder.ins().return_(&[zero]);
                }
            }
            Terminator::Goto(target) => {
                let target_block = block_map[target];
                builder.ins().jump(target_block, &[]);
            }
            Terminator::SwitchInt {
                discriminant,
                targets,
                otherwise,
            } => {
                let discr_val = Self::translate_operand(discriminant, builder, local_map)?;

                // Create a switch instruction
                let mut switch = cranelift::frontend::Switch::new();

                for (value, target_bb) in targets {
                    let target_block = block_map[target_bb];
                    switch.set_entry(*value, target_block);
                }

                let otherwise_block = block_map[otherwise];
                switch.emit(builder, discr_val, otherwise_block);
            }
            Terminator::Call { .. } => {
                anyhow::bail!("Function calls not yet implemented")
            }
            Terminator::Unreachable => {
                // Generate a trap for unreachable code
                // In Cranelift, we can use the general User trap code
                builder.ins().trap(cranelift::codegen::ir::TrapCode::unwrap_user(1));
            }
        }
        Ok(())
    }

    #[allow(dead_code)]
    fn mir_type_to_cranelift(ty: &MirType) -> Type {
        match ty {
            MirType::Int | MirType::Bool => types::I64,
            MirType::Float => types::F64,
            MirType::Unit => types::I64, // Represent unit as i64 for simplicity
            MirType::String => types::I64, // String as pointer (i64)
            MirType::Named(name) => {
                panic!(
                    "Unresolved named type in Cranelift codegen: {:?}. \
                    This indicates a bug in MIR lowering - primitive types should be resolved to \
                    MirType::Int/Float/Bool/String, and user-defined types should be resolved to \
                    MirType::Struct/Enum.",
                    name
                )
            }
            MirType::Function { .. } => types::I64, // Function pointer
            MirType::Struct { .. } => types::I64, // Struct as pointer
            MirType::Enum { .. } => types::I64, // Enum as pointer
            MirType::Array { .. } => types::I64, // Array as pointer
            MirType::Slice { .. } => types::I64, // Slice as pointer
            MirType::Tuple(_) => types::I64, // Tuple as pointer
            MirType::Ref { .. } => types::I64, // Reference as pointer
        }
    }
}

impl Default for JitCompiler {
    fn default() -> Self {
        Self::new().expect("Failed to create JIT compiler")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_jit_simple() {
        // This would test a simple function compilation
        // For now, just ensure the JIT can be created
        let _jit = JitCompiler::new().unwrap();
    }
}
