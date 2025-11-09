//! LLVM code generation from MIR

use crate::types::TypeLowering;
use crate::OptLevel;
use anyhow::Result;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine,
};
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum};
use inkwell::values::{BasicValueEnum, FunctionValue};
use inkwell::IntPredicate;
use rv_hir::{ExternalFunction, FunctionId, LiteralKind};
use rv_mir::{
    AggregateKind, BasicBlock, BinaryOp, Constant, LocalId, MirFunction, Operand, Place, RValue,
    Statement, Terminator, UnaryOp,
};
use std::collections::HashMap;
use std::path::Path;

pub struct LLVMBackend {
    context: Context,
}

impl LLVMBackend {
    pub fn new(_module_name: &str, _opt_level: OptLevel) -> Result<Self> {
        use std::sync::Once;
        static INIT: Once = Once::new();

        // Initialize LLVM targets once
        INIT.call_once(|| {
            Target::initialize_all(&InitializationConfig::default());
        });

        // Create context that will be owned by this struct
        let context = Context::create();

        Ok(Self {
            context,
        })
    }

    /// Compile functions and write to object file
    /// This method takes ownership of parameters to ensure proper scoping
    pub fn compile_and_write(
        &self,
        module_name: &str,
        functions: &[MirFunction],
        external_functions: &HashMap<FunctionId, ExternalFunction>,
        output_path: &Path,
        opt_level: OptLevel,
    ) -> Result<()> {
        // Create compiler with borrowed context
        let compiler = Compiler::new(&self.context, module_name, opt_level);

        // Compile all functions
        compiler.compile_functions_with_externals(functions, external_functions)?;

        // Debug: Write LLVM IR to file
        if std::env::var("DEBUG_LLVM_IR").is_ok() {
            let ir_path = output_path.with_extension("ll");
            std::fs::write(&ir_path, compiler.module.print_to_string().to_string())?;
            eprintln!("DEBUG: LLVM IR written to {}", ir_path.display());
        }

        // Write object file
        compiler.write_object_file(output_path)?;

        Ok(())
    }

}

// Internal compiler struct that borrows from the backend
struct Compiler<'a> {
    context: &'a Context,
    module: Module<'a>,
    builder: Builder<'a>,
    type_lowering: TypeLowering<'a>,
    opt_level: OptLevel,
    fpm: PassManager<FunctionValue<'a>>,
}

impl<'ctx> Compiler<'ctx> {
    fn new(context: &'ctx Context, module_name: &str, opt_level: OptLevel) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();
        let type_lowering = TypeLowering::new(context);
        let fpm = PassManager::create(&module);
        fpm.initialize();

        Self {
            context,
            module,
            builder,
            type_lowering,
            opt_level,
            fpm,
        }
    }

    /// Declare external functions in LLVM module
    fn declare_external_functions(
        &self,
        external_funcs: &HashMap<FunctionId, ExternalFunction>,
    ) -> HashMap<FunctionId, FunctionValue<'ctx>> {
        let mut llvm_functions = HashMap::new();

        for (func_id, ext_func) in external_funcs {
            // Determine parameter types (all i64 for simplicity)
            let param_types: Vec<BasicMetadataTypeEnum> = ext_func
                .parameters
                .iter()
                .map(|_| self.context.i64_type().into())
                .collect();

            // Determine return type
            let fn_type = if ext_func.return_type.is_some() {
                self.context.i64_type().fn_type(&param_types, false)
            } else {
                self.context.void_type().fn_type(&param_types, false)
            };

            // The mangled_name field contains the correct symbol name to use
            // (either mangled for Rust ABI or unmangled for C ABI)
            let fn_name = ext_func
                .mangled_name
                .as_ref()
                .map(|s| s.clone())
                .unwrap_or_else(|| format!("extern_func_{}", func_id.0));

            // Declare the external function
            let function = self.module.add_function(&fn_name, fn_type, None);
            llvm_functions.insert(*func_id, function);
        }

        llvm_functions
    }

    /// Compile multiple MIR functions to LLVM IR (supports function calls)
    pub fn compile_functions(&self, mir_funcs: &[MirFunction]) -> Result<()> {
        self.compile_functions_with_externals(mir_funcs, &HashMap::new())
    }

    /// Compile multiple MIR functions with external function support
    pub fn compile_functions_with_externals(
        &self,
        mir_funcs: &[MirFunction],
        external_funcs: &HashMap<FunctionId, ExternalFunction>,
    ) -> Result<()> {
        use std::collections::HashMap;

        // Phase 0: Declare all external functions
        let mut llvm_functions = self.declare_external_functions(external_funcs);

        // Phase 1: Scan all functions to infer parameter counts from call sites
        let mut param_counts: HashMap<FunctionId, usize> = HashMap::new();

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

        // Phase 2: Declare all regular functions (external functions already declared)

        for mir_func in mir_funcs {
            let param_count = param_counts.get(&mir_func.id).copied().unwrap_or(0);

            // Create function signature with parameters
            let param_types: Vec<_> = (0..param_count)
                .map(|_| self.context.i32_type().into())
                .collect();
            let fn_type = self.context.i32_type().fn_type(&param_types, false);

            // Use function ID as name to allow multiple functions
            let fn_name = format!("func_{}", mir_func.id.0);
            let function = self.module.add_function(&fn_name, fn_type, None);

            llvm_functions.insert(mir_func.id, function);
        }

        // Phase 3: Compile function bodies
        for mir_func in mir_funcs {
            let function = llvm_functions[&mir_func.id];

            // Build function body
            let mut func_codegen = FunctionCodegen::new(self, function, mir_func, &llvm_functions);
            func_codegen.build()?;

            // Run optimization passes
            self.fpm.run_on(&function);
        }

        Ok(())
    }

    /// Compile a single MIR function to LLVM IR (legacy API)
    pub fn compile_function(&self, mir_func: &MirFunction) -> Result<FunctionValue<'ctx>> {
        use std::collections::HashMap;

        // For single-function compilation, assume no parameters
        let fn_type = self.context.i32_type().fn_type(&[], false);

        // Use function ID as name
        let fn_name = format!("func_{}", mir_func.id.0);
        let function = self.module.add_function(&fn_name, fn_type, None);

        // Build function body (no cross-function calls in single-function mode)
        let empty_functions = HashMap::new();
        let mut func_codegen = FunctionCodegen::new(self, function, mir_func, &empty_functions);
        func_codegen.build()?;

        // Run optimization passes
        self.fpm.run_on(&function);

        Ok(function)
    }

    /// Get LLVM IR as string
    pub fn to_llvm_ir(&self) -> String {
        self.module.print_to_string().to_string()
    }

    /// Write object file to disk
    pub fn write_object_file(&self, output_path: &Path) -> Result<()> {
        // Target initialization is handled in new() via Once::call_once
        let target_triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&target_triple)
            .map_err(|e| anyhow::anyhow!("Failed to create target: {}", e))?;

        let target_machine = target
            .create_target_machine(
                &target_triple,
                "generic",
                "",
                self.opt_level.to_inkwell(),
                RelocMode::Default,
                CodeModel::Default,
            )
            .ok_or_else(|| anyhow::anyhow!("Failed to create target machine"))?;

        target_machine
            .write_to_file(&self.module, FileType::Object, output_path)
            .map_err(|e| anyhow::anyhow!("Failed to write object file: {}", e))?;

        Ok(())
    }
}

struct FunctionCodegen<'a, 'ctx> {
    backend: &'a LLVMBackend<'ctx>,
    function: FunctionValue<'ctx>,
    mir_func: &'a MirFunction,
    locals: HashMap<LocalId, BasicValueEnum<'ctx>>,
    blocks: HashMap<usize, inkwell::basic_block::BasicBlock<'ctx>>,
    llvm_functions: &'a HashMap<rv_hir::FunctionId, FunctionValue<'ctx>>,
}

impl<'a, 'ctx> FunctionCodegen<'a, 'ctx> {
    fn new(
        backend: &'a LLVMBackend<'ctx>,
        function: FunctionValue<'ctx>,
        mir_func: &'a MirFunction,
        llvm_functions: &'a HashMap<rv_hir::FunctionId, FunctionValue<'ctx>>,
    ) -> Self {
        Self {
            backend,
            function,
            mir_func,
            locals: HashMap::new(),
            blocks: HashMap::new(),
            llvm_functions,
        }
    }

    fn build(&mut self) -> Result<()> {
        let context = self.context;

        // Create all basic blocks
        for (idx, _) in self.mir_func.basic_blocks.iter().enumerate() {
            let bb_name = format!("bb{}", idx);
            let bb = context.append_basic_block(self.function, &bb_name);
            self.blocks.insert(idx, bb);
        }

        // Position at entry block
        if let Some(entry_bb) = self.blocks.get(&self.mir_func.entry_block) {
            self.builder.position_at_end(*entry_bb);
        }

        // Allocate space for all locals
        for local in &self.mir_func.locals {
            let llvm_type = self.type_lowering.lower_type(&local.ty);
            let alloca = self.builder.build_alloca(llvm_type, &format!("local_{}", local.id.0))
                .map_err(|e| anyhow::anyhow!("Failed to create alloca: {}", e))?;
            self.locals.insert(local.id, alloca.into());
        }

        // Compile each basic block
        for (idx, bb) in self.mir_func.basic_blocks.iter().enumerate() {
            self.compile_basic_block(idx, bb)?;
        }

        Ok(())
    }

    fn compile_basic_block(&mut self, _idx: usize, bb: &BasicBlock) -> Result<()> {
        // Position builder at this block
        if let Some(llvm_bb) = self.blocks.get(&bb.id) {
            self.builder.position_at_end(*llvm_bb);
        }

        // Compile statements
        for stmt in &bb.statements {
            self.compile_statement(stmt)?;
        }

        // Compile terminator
        self.compile_terminator(&bb.terminator)?;

        Ok(())
    }

    fn compile_statement(&mut self, stmt: &Statement) -> Result<()> {
        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                let mut value = self.compile_rvalue(rvalue)?;
                let dest = self.get_place(place)?;

                if let BasicValueEnum::PointerValue(ptr) = dest {
                    // Check if we need to convert the value type to match the destination
                    // This handles cases where MIR has type mismatches (e.g., storing i1 to i32)
                    if value.is_int_value() {
                        let value_int = value.into_int_value();
                        let value_width = value_int.get_type().get_bit_width();

                        // Get the expected type from the local
                        let local_ty = self.mir_func.locals
                            .iter()
                            .find(|l| l.id == place.local)
                            .map(|l| &l.ty);

                        if let Some(ty) = local_ty {
                            let expected_type = self.type_lowering.lower_type(ty);
                            if let BasicTypeEnum::IntType(expected_int_type) = expected_type {
                                let expected_width = expected_int_type.get_bit_width();

                                // Convert if widths don't match
                                if value_width < expected_width {
                                    // Zero-extend smaller values (e.g., i1 -> i32)
                                    value = self.builder.build_int_z_extend(
                                        value_int,
                                        expected_int_type,
                                        "zext"
                                    ).map_err(|e| anyhow::anyhow!("Failed to zero-extend: {}", e))?.into();
                                } else if value_width > expected_width {
                                    // Truncate larger values
                                    value = self.builder.build_int_truncate(
                                        value_int,
                                        expected_int_type,
                                        "trunc"
                                    ).map_err(|e| anyhow::anyhow!("Failed to truncate: {}", e))?.into();
                                }
                            }
                        }
                    }

                    self.builder.build_store(ptr, value)
                        .map_err(|e| anyhow::anyhow!("Failed to build store: {}", e))?;
                }
            }
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {
                // These are hints, no code generation needed
            }
        }
        Ok(())
    }

    fn compile_rvalue(&mut self, rvalue: &RValue) -> Result<BasicValueEnum<'ctx>> {
        match rvalue {
            RValue::Use(operand) => self.compile_operand(operand),

            RValue::BinaryOp { op, left, right } => {
                let lhs = self.compile_operand(left)?;
                let rhs = self.compile_operand(right)?;
                self.compile_binary_op(*op, lhs, rhs)
            }

            RValue::UnaryOp { op, operand } => {
                let val = self.compile_operand(operand)?;
                self.compile_unary_op(*op, val)
            }

            RValue::Call { func, args } => {
                // Get the LLVM function
                let callee = self.llvm_functions.get(func)
                    .ok_or_else(|| anyhow::anyhow!("Function not found: {:?}", func))?;

                // Compile arguments
                let arg_values: Result<Vec<_>> = args
                    .iter()
                    .map(|arg| self.compile_operand(arg))
                    .collect();
                let arg_values = arg_values?;

                // Convert BasicValueEnum to BasicMetadataValueEnum
                let args_metadata: Vec<_> = arg_values
                    .into_iter()
                    .map(|v| v.into())
                    .collect();

                // Call the function
                let call_site = self.builder
                    .build_call(*callee, &args_metadata, "call")
                    .map_err(|e| anyhow::anyhow!("Failed to build call: {}", e))?;

                // Get return value
                let return_value = call_site.try_as_basic_value().left()
                    .unwrap_or_else(|| self.context.i32_type().const_int(0, false).into());

                Ok(return_value)
            }

            RValue::Ref { .. } => {
                // TODO: Implement references
                Ok(self.context.i32_type().const_int(0, false).into())
            }

            RValue::Aggregate { kind, operands } => {
                // For now, represent aggregates as the first field value
                // This is a simplified implementation - proper support would create struct types
                match kind {
                    AggregateKind::Struct | AggregateKind::Tuple | AggregateKind::Array(_) => {
                        if let Some(first_operand) = operands.first() {
                            self.compile_operand(first_operand)
                        } else {
                            Ok(self.context.i32_type().const_int(0, false).into())
                        }
                    }
                    AggregateKind::Enum { .. } => {
                        // TODO: Implement enum aggregates
                        Ok(self.context.i32_type().const_int(0, false).into())
                    }
                }
            }
        }
    }

    fn compile_operand(&mut self, operand: &Operand) -> Result<BasicValueEnum<'ctx>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let ptr = self.get_place(place)?;
                if let BasicValueEnum::PointerValue(ptr_val) = ptr {
                    // Get the type after applying all projections
                    let place_ty = self.get_place_type(place)?;

                    // Get the LLVM type for this place
                    let llvm_type = self.type_lowering.lower_type(&place_ty);

                    // Load value from place
                    self.builder.build_load(llvm_type, ptr_val, "load")
                        .map_err(|e| anyhow::anyhow!("Failed to build load: {}", e))
                } else {
                    Ok(ptr)
                }
            }

            Operand::Constant(constant) => self.compile_constant(constant),
        }
    }

    /// Get the type of a place after applying all projections
    fn get_place_type(&self, place: &Place) -> Result<rv_mir::MirType> {
        use rv_mir::PlaceElem;

        // Start with the base local's type
        let local_info = self.mir_func.locals
            .iter()
            .find(|l| l.id == place.local)
            .ok_or_else(|| anyhow::anyhow!("Unknown local: {:?}", place.local))?;

        let mut current_type = local_info.ty.clone();

        // Apply projections to get the final type
        for projection in &place.projection {
            match projection {
                PlaceElem::Field { field_idx } => {
                    if let rv_mir::MirType::Struct { fields, .. } = &current_type {
                        if let Some(field_type) = fields.get(*field_idx) {
                            current_type = field_type.clone();
                        } else {
                            anyhow::bail!("Field index out of bounds: {}", field_idx);
                        }
                    } else {
                        anyhow::bail!("Cannot access field on non-struct type");
                    }
                }
                PlaceElem::Deref => {
                    // TODO: Implement dereference type resolution
                    anyhow::bail!("Deref not implemented");
                }
                PlaceElem::Index(_) => {
                    // TODO: Implement array indexing type resolution
                    anyhow::bail!("Index not implemented");
                }
            }
        }

        Ok(current_type)
    }

    fn compile_constant(&self, constant: &Constant) -> Result<BasicValueEnum<'ctx>> {
        match &constant.kind {
            LiteralKind::Integer(val) => {
                Ok(self.context.i32_type().const_int(*val as u64, false).into())
            }
            LiteralKind::Float(val) => {
                Ok(self.context.f64_type().const_float(*val).into())
            }
            LiteralKind::Bool(val) => {
                Ok(self.context.bool_type().const_int(*val as u64, false).into())
            }
            LiteralKind::String(_) => {
                // TODO: Implement string constants
                Ok(self.context.i32_type().const_int(0, false).into())
            }
            LiteralKind::Unit => {
                Ok(self.context.i32_type().const_int(0, false).into())
            }
        }
    }

    fn compile_binary_op(
        &self,
        op: BinaryOp,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>> {
        // Check if operands are integers (struct fields should have been loaded as ints)
        if !lhs.is_int_value() {
            anyhow::bail!("Left operand is not an integer: {:?}", lhs);
        }
        if !rhs.is_int_value() {
            anyhow::bail!("Right operand is not an integer: {:?}", rhs);
        }

        let lhs_int = lhs.into_int_value();
        let rhs_int = rhs.into_int_value();

        let result = match op {
            BinaryOp::Add => self.builder.build_int_add(lhs_int, rhs_int, "add"),
            BinaryOp::Sub => self.builder.build_int_sub(lhs_int, rhs_int, "sub"),
            BinaryOp::Mul => self.builder.build_int_mul(lhs_int, rhs_int, "mul"),
            BinaryOp::Div => self.builder.build_int_signed_div(lhs_int, rhs_int, "div"),
            BinaryOp::Mod => self.builder.build_int_signed_rem(lhs_int, rhs_int, "mod"),
            BinaryOp::Eq => {
                let cmp = self.builder.build_int_compare(IntPredicate::EQ, lhs_int, rhs_int, "eq")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                return Ok(cmp.into());
            }
            BinaryOp::Ne => {
                let cmp = self.builder.build_int_compare(IntPredicate::NE, lhs_int, rhs_int, "ne")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                return Ok(cmp.into());
            }
            BinaryOp::Lt => {
                let cmp = self.builder.build_int_compare(IntPredicate::SLT, lhs_int, rhs_int, "lt")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                return Ok(cmp.into());
            }
            BinaryOp::Le => {
                let cmp = self.builder.build_int_compare(IntPredicate::SLE, lhs_int, rhs_int, "le")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                return Ok(cmp.into());
            }
            BinaryOp::Gt => {
                let cmp = self.builder.build_int_compare(IntPredicate::SGT, lhs_int, rhs_int, "gt")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                return Ok(cmp.into());
            }
            BinaryOp::Ge => {
                let cmp = self.builder.build_int_compare(IntPredicate::SGE, lhs_int, rhs_int, "ge")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                return Ok(cmp.into());
            }
            BinaryOp::BitAnd => self.builder.build_and(lhs_int, rhs_int, "and"),
            BinaryOp::BitOr => self.builder.build_or(lhs_int, rhs_int, "or"),
            BinaryOp::BitXor => self.builder.build_xor(lhs_int, rhs_int, "xor"),
            BinaryOp::Shl => self.builder.build_left_shift(lhs_int, rhs_int, "shl"),
            BinaryOp::Shr => self.builder.build_right_shift(lhs_int, rhs_int, false, "shr"),
        }
        .map_err(|e| anyhow::anyhow!("Failed to build binary op: {}", e))?;

        Ok(result.into())
    }

    fn compile_unary_op(
        &self,
        op: UnaryOp,
        val: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>> {
        let val_int = val.into_int_value();

        let result = match op {
            UnaryOp::Neg => {
                self.builder.build_int_neg(val_int, "neg")
                    .map_err(|e| anyhow::anyhow!("Failed to build negation: {}", e))?
            }
            UnaryOp::Not => {
                self.builder.build_not(val_int, "not")
                    .map_err(|e| anyhow::anyhow!("Failed to build not: {}", e))?
            }
        };

        Ok(result.into())
    }

    fn compile_terminator(&mut self, terminator: &Terminator) -> Result<()> {
        match terminator {
            Terminator::Return { value } => {
                if let Some(ret_val) = value {
                    let val = self.compile_operand(ret_val)?;

                    // Convert boolean (i1) to i32 if needed
                    let ret_val = if val.is_int_value() && val.into_int_value().get_type().get_bit_width() == 1 {
                        // Zero-extend i1 to i32
                        self.builder.build_int_z_extend(
                            val.into_int_value(),
                            self.context.i32_type(),
                            "bool_to_i32"
                        ).map_err(|e| anyhow::anyhow!("Failed to extend bool to i32: {}", e))?.into()
                    } else {
                        val
                    };

                    self.builder.build_return(Some(&ret_val))
                        .map_err(|e| anyhow::anyhow!("Failed to build return: {}", e))?;
                } else {
                    // Return void/unit
                    let zero = self.context.i32_type().const_int(0, false);
                    self.builder.build_return(Some(&zero))
                        .map_err(|e| anyhow::anyhow!("Failed to build return: {}", e))?;
                }
            }

            Terminator::Goto(target) => {
                if let Some(target_bb) = self.blocks.get(target) {
                    self.builder.build_unconditional_branch(*target_bb)
                        .map_err(|e| anyhow::anyhow!("Failed to build branch: {}", e))?;
                }
            }

            Terminator::SwitchInt {
                discriminant,
                targets,
                otherwise,
            } => {
                // Compile the discriminant value
                let discr_val = self.compile_operand(discriminant)?;

                // For boolean (i1) values, we can use a simple conditional branch
                // For now, we'll handle the simple case of checking if value == 1 (true)
                if targets.len() == 1 && targets.contains_key(&1) {
                    // This is a boolean if/else: if (condition) then else
                    let then_bb = self.blocks.get(&targets[&1]).ok_or_else(|| {
                        anyhow::anyhow!("Target block not found")
                    })?;
                    let else_bb = self.blocks.get(otherwise).ok_or_else(|| {
                        anyhow::anyhow!("Otherwise block not found")
                    })?;

                    // Compare discriminant with 1 (true)
                    let discr_int = if discr_val.is_int_value() {
                        discr_val.into_int_value()
                    } else {
                        anyhow::bail!("Discriminant is not an integer value");
                    };

                    // Create comparison: discr_val != 0
                    let zero = if discr_int.get_type().get_bit_width() == 1 {
                        discr_int.get_type().const_int(0, false)
                    } else {
                        self.context.i32_type().const_int(0, false)
                    };

                    let condition = self.builder.build_int_compare(
                        IntPredicate::NE,
                        discr_int,
                        zero,
                        "switchcond"
                    ).map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;

                    // Build conditional branch
                    self.builder.build_conditional_branch(condition, *then_bb, *else_bb)
                        .map_err(|e| anyhow::anyhow!("Failed to build conditional branch: {}", e))?;
                } else {
                    // More complex switch - not implemented yet
                    // For now, just jump to otherwise
                    if let Some(else_bb) = self.blocks.get(otherwise) {
                        self.builder.build_unconditional_branch(*else_bb)
                            .map_err(|e| anyhow::anyhow!("Failed to build branch: {}", e))?;
                    }
                }
            }

            Terminator::Call { .. } => {
                // TODO: Implement call terminator
            }

            Terminator::Unreachable => {
                self.builder.build_unreachable()
                    .map_err(|e| anyhow::anyhow!("Failed to build unreachable: {}", e))?;
            }
        }

        Ok(())
    }

    fn get_place(&self, place: &Place) -> Result<BasicValueEnum<'ctx>> {
        use rv_mir::PlaceElem;

        // Get the base local
        if let Some(mut local_val) = self.locals.get(&place.local).copied() {
            // Get the type of the base local for tracking through projections
            let local_info = self.mir_func.locals
                .iter()
                .find(|l| l.id == place.local)
                .ok_or_else(|| anyhow::anyhow!("Unknown local: {:?}", place.local))?;

            let mut current_type = &local_info.ty;

            // Handle projections (field access, array indexing, etc.)
            for projection in &place.projection {
                match projection {
                    PlaceElem::Field { field_idx } => {
                        // Use GEP (GetElementPtr) to access struct field
                        if let BasicValueEnum::PointerValue(ptr_val) = local_val {
                            // Get the LLVM type from the MIR type
                            let basic_type = self.type_lowering.lower_type(current_type);

                            // Extract the actual struct type from BasicTypeEnum
                            if let BasicTypeEnum::StructType(struct_type) = basic_type {
                                // GEP with struct_gep for type-safe field access
                                let field_ptr = self.builder.build_struct_gep(
                                    struct_type,
                                    ptr_val,
                                    *field_idx as u32,
                                    "field_ptr"
                                ).map_err(|e| anyhow::anyhow!("Failed to build struct GEP: {}", e))?;

                                local_val = field_ptr.into();

                                // Update current_type to the field's type
                                if let rv_mir::MirType::Struct { fields, .. } = current_type {
                                    if let Some(field_type) = fields.get(*field_idx) {
                                        current_type = field_type;
                                    }
                                }
                            } else {
                                anyhow::bail!(
                                    "Expected struct type for field access but got {:?}",
                                    basic_type
                                );
                            }
                        } else {
                            anyhow::bail!("Cannot access field on non-pointer value");
                        }
                    }
                    PlaceElem::Deref => {
                        // TODO: Implement dereference
                    }
                    PlaceElem::Index(_) => {
                        // TODO: Implement array indexing
                    }
                }
            }
            Ok(local_val)
        } else {
            anyhow::bail!("Unknown local: {:?}", place.local)
        }
    }
}
