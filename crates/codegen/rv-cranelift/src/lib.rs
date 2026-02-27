//! Cranelift JIT backend for Raven
//!
//! Compiles MIR to native code using Cranelift JIT compiler

use anyhow::{Context, Result};
use cranelift::codegen::ir::StackSlot;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use rustc_hash::FxHashMap;
use rv_hir::LiteralKind;
use rv_mir::{
    AggregateKind, LocalId, MirFunction, MirType, Operand, Place, PlaceElem, RValue, Statement,
    Terminator,
};

/// JIT compiler for MIR
pub struct JitCompiler {
    /// Cranelift JIT module
    module: JITModule,

    /// Cranelift context
    ctx: codegen::Context,

    /// Map from MIR function IDs to Cranelift function IDs
    function_map: FxHashMap<rv_hir::FunctionId, FuncId>,

    /// Compiled functions cache (FunctionId -> code pointer)
    pub compiled_functions: FxHashMap<rv_hir::FunctionId, *const u8>,
}

/// Storage for a MIR local in Cranelift.
///
/// Scalar types (i64, f64, bool) are stored in Cranelift SSA variables.
/// Struct types are stored in stack slots so individual fields can be accessed.
/// How a Var-stored local should handle Deref projections.
#[derive(Clone, Copy, PartialEq, Eq)]
enum VarKind {
    /// Plain scalar value. Deref projections are no-ops (stripped).
    Plain,
    /// Reference to a multi-field struct (from `RValue::Ref`). Deref is handled
    /// implicitly via pointer arithmetic on field access.
    Ref,
    /// Raw pointer (`*const T` / `*mut T`). Deref must perform an actual
    /// memory load/store through the pointer value.
    RawPtr,
}

#[derive(Clone)]
enum LocalStorage {
    /// Scalar value stored in a Cranelift variable, with its declared Cranelift type
    /// and indirection kind.
    Var(Variable, Type, VarKind),
    /// Composite type stored in a stack slot, with field count for bounds checking.
    /// For enums, is_enum=true means slot[0] is discriminant and data fields start at slot[1].
    StackSlot {
        slot: StackSlot,
        field_count: usize,
        is_enum: bool,
    },
}

impl JitCompiler {
    /// Map a MIR type to a Cranelift scalar type.
    fn cranelift_type(mir_ty: &MirType) -> Type {
        match mir_ty {
            MirType::Float(rv_hir::FloatWidth::F32) => types::F32,
            MirType::Float(rv_hir::FloatWidth::F64) => types::F64,
            MirType::Int(rv_hir::IntWidth::I8, _) | MirType::Char => types::I8,
            MirType::Int(rv_hir::IntWidth::I16, _) => types::I16,
            MirType::Int(rv_hir::IntWidth::I32, _) => types::I32,
            MirType::Int(rv_hir::IntWidth::I128, _) => types::I128,
            // I64, Isize, and everything else maps to I64
            _ => types::I64,
        }
    }

    /// Convert a Cranelift value to a target type, inserting extend/reduce as needed.
    /// This handles the mismatch between operation result types and variable/ABI types.
    fn convert_to_type(builder: &mut FunctionBuilder, val: Value, target: Type) -> Value {
        let actual = builder.func.dfg.value_type(val);
        if actual == target {
            return val;
        }
        // Float types cannot be extended/reduced with integer ops
        if actual.is_float() || target.is_float() {
            // Float-to-float conversion
            if actual.is_float() && target.is_float() {
                if actual.bits() < target.bits() {
                    return builder.ins().fpromote(target, val);
                } else {
                    return builder.ins().fdemote(target, val);
                }
            }
            // Mixed float/int — should use cast path, not this helper
            return val;
        }
        // Integer extend or reduce
        if actual.bits() < target.bits() {
            builder.ins().sextend(target, val)
        } else {
            builder.ins().ireduce(target, val)
        }
    }

    /// Create a new JIT compiler
    pub fn new() -> Result<Self> {
        let builder = JITBuilder::new(cranelift_module::default_libcall_names())?;
        let module = JITModule::new(builder);

        Ok(Self {
            ctx: module.make_context(),
            module,
            function_map: FxHashMap::default(),
            compiled_functions: FxHashMap::default(),
        })
    }

    /// Count the number of flattened i64 ABI parameters for a MIR function.
    ///
    /// Struct parameters are flattened: each field becomes a separate i64 param.
    /// Enum parameters are flattened: 1 (discriminant) + max variant fields.
    /// Scalar parameters remain a single i64 param each.
    fn abi_param_count(mir_func: &MirFunction) -> usize {
        let mut count = 0;
        for idx in 0..mir_func.param_count {
            let local = &mir_func.locals[idx];
            match &local.ty {
                MirType::Struct { fields, .. } => count += fields.len(),
                MirType::Enum { variants, .. } => {
                    // Enum: 1 for discriminant + max variant fields
                    let max_fields = variants.iter().map(|v| v.fields.len()).max().unwrap_or(0);
                    count += 1 + max_fields;
                }
                _ => count += 1,
            }
        }
        count
    }

    /// Compile multiple MIR functions (for programs with function calls)
    pub fn compile_multiple(&mut self, mir_funcs: &[MirFunction]) -> Result<*const u8> {
        // Phase 1: Declare all functions using param_count from MIR
        for mir_func in mir_funcs {
            if !self.function_map.contains_key(&mir_func.id) {
                let mut sig = self.module.make_signature();
                sig.returns.push(AbiParam::new(types::I64));

                // Flatten struct params: each struct field becomes a separate i64 param
                for _ in 0..Self::abi_param_count(mir_func) {
                    sig.params.push(AbiParam::new(types::I64));
                }

                let func_id = self
                    .module
                    .declare_function(&format!("func_{}", mir_func.id.0), Linkage::Export, &sig)
                    .context("Failed to declare function")?;

                self.function_map.insert(mir_func.id, func_id);
            }
        }

        // Phase 2: Compile all functions (but don't finalize yet)
        for mir_func in mir_funcs {
            self.compile_single_no_finalize(mir_func)?;
        }

        // Phase 3: Finalize ALL functions at once
        self.module.finalize_definitions()?;

        // Phase 4: Get code pointers for all compiled functions and cache them
        for mir_func in mir_funcs {
            let func_id = *self
                .function_map
                .get(&mir_func.id)
                .ok_or_else(|| anyhow::anyhow!("Function not in function_map"))?;

            let code_ptr = self.module.get_finalized_function(func_id);
            self.compiled_functions.insert(mir_func.id, code_ptr);
        }

        // Phase 5: Return the code pointer for the last function (usually main)
        let last_func_id = mir_funcs
            .last()
            .ok_or_else(|| anyhow::anyhow!("No functions to compile"))?
            .id;

        let func_ptr = self
            .compiled_functions
            .get(&last_func_id)
            .copied()
            .ok_or_else(|| anyhow::anyhow!("Last function not found in compiled cache"))?;

        Ok(func_ptr)
    }

    /// Compile a single MIR function without finalizing (for multi-function compilation)
    fn compile_single_no_finalize(&mut self, mir_func: &MirFunction) -> Result<()> {
        if self.compiled_functions.contains_key(&mir_func.id) {
            return Ok(());
        }

        self.ctx.func.clear();

        let func_id = *self
            .function_map
            .get(&mir_func.id)
            .ok_or_else(|| anyhow::anyhow!("Function not declared"))?;

        let sig = self
            .module
            .declarations()
            .get_function_decl(func_id)
            .signature
            .clone();
        self.ctx.func.signature = sig;

        let mut builder_context = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut builder_context);

            // Import all declared functions so we can call them
            let mut func_refs: FxHashMap<rv_hir::FunctionId, cranelift::codegen::ir::FuncRef> =
                FxHashMap::default();
            for (&mir_func_id, &cranelift_func_id) in &self.function_map {
                let func_ref = self
                    .module
                    .declare_func_in_func(cranelift_func_id, builder.func);
                func_refs.insert(mir_func_id, func_ref);
            }

            // Create blocks
            let mut block_map = FxHashMap::default();
            for bb in &mir_func.basic_blocks {
                let cranelift_block = builder.create_block();
                block_map.insert(bb.id, cranelift_block);
            }

            let entry_block = block_map[&0];
            builder.switch_to_block(entry_block);
            builder.append_block_params_for_function_params(entry_block);

            // Allocate storage for each local based on its MIR type.
            // Pass the MIR param count (not the flattened ABI count) — allocate_locals
            // tracks the ABI param index internally via abi_idx.
            let local_storage = Self::allocate_locals(
                &mir_func.locals,
                mir_func.param_count,
                entry_block,
                &mut builder,
            );

            // Translate each basic block
            for bb in &mir_func.basic_blocks {
                let cranelift_block = block_map[&bb.id];
                if bb.id != 0 {
                    builder.switch_to_block(cranelift_block);
                }

                for stmt in &bb.statements {
                    Self::translate_statement(stmt, &mut builder, &local_storage, &func_refs)?;
                }

                Self::translate_terminator(
                    &bb.terminator,
                    &mut builder,
                    &local_storage,
                    &block_map,
                )?;
            }

            for bb in &mir_func.basic_blocks {
                let cranelift_block = block_map[&bb.id];
                builder.seal_block(cranelift_block);
            }

            builder.finalize();
        }

        if let Err(errors) = cranelift_codegen::verify_function(&self.ctx.func, self.module.isa()) {
            anyhow::bail!("Verification errors: {}", errors);
        }

        self.module
            .define_function(func_id, &mut self.ctx)
            .context("Failed to define function")?;

        self.module.clear_context(&mut self.ctx);

        Ok(())
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

    /// Allocate Cranelift storage for each MIR local.
    ///
    /// Scalar types get SSA variables. Struct types get stack slots so that
    /// individual fields can be read/written via Place projections.
    ///
    /// For parameters, struct types are flattened in the ABI: each field becomes
    /// a separate i64 parameter. This method tracks a separate ABI parameter index
    /// to correctly map flattened ABI params back into struct stack slots.
    fn allocate_locals(
        locals: &[rv_mir::Local],
        param_count: usize,
        entry_block: Block,
        builder: &mut FunctionBuilder,
    ) -> FxHashMap<LocalId, LocalStorage> {
        let mut storage = FxHashMap::default();
        // ABI param index — advances by field_count for struct params, by 1 for scalars.
        // This diverges from the MIR local index because structs are flattened in the ABI.
        let mut abi_idx = 0usize;

        for (idx, local) in locals.iter().enumerate() {
            // Determine if this local needs a stack slot (structs, tuples, arrays, enums)
            // Returns (field_count, is_enum)
            let slot_info = match &local.ty {
                MirType::Struct { fields, .. } => Some((fields.len(), false)),
                MirType::Tuple(elements) => Some((elements.len(), false)),
                MirType::Array { size, .. } => Some((*size, false)),
                MirType::Enum { variants, .. } => {
                    // Enum: 1 slot for discriminant + max variant fields
                    let max_fields = variants.iter().map(|v| v.fields.len()).max().unwrap_or(0);
                    Some((1 + max_fields, true))
                }
                _ => None,
            };

            if let Some((field_count, is_enum)) = slot_info {
                if field_count > 0 {
                    // Composite locals get a stack slot: one i64 per field/element
                    let size = (field_count * 8) as u32;
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        size,
                        0, // default alignment
                    ));

                    // If this is a struct/enum parameter, the caller passes one i64 per field.
                    // Store each flattened ABI param into the correct stack slot offset.
                    if idx < param_count {
                        match &local.ty {
                            MirType::Struct { fields, .. } => {
                                let param_vals: Vec<Value> = (0..fields.len())
                                    .map(|fi| builder.block_params(entry_block)[abi_idx + fi])
                                    .collect();
                                for (field_idx, param_val) in param_vals.into_iter().enumerate() {
                                    let offset = (field_idx * 8) as i32;
                                    builder.ins().stack_store(param_val, slot, offset);
                                }
                                abi_idx += fields.len();
                            }
                            MirType::Enum { variants, .. } => {
                                // Enum: 1 (discriminant) + max variant fields
                                let max_fields = variants.iter().map(|v| v.fields.len()).max().unwrap_or(0);
                                let flattened_count = 1 + max_fields;
                                let param_vals: Vec<Value> = (0..flattened_count)
                                    .map(|fi| builder.block_params(entry_block)[abi_idx + fi])
                                    .collect();
                                for (field_idx, param_val) in param_vals.into_iter().enumerate() {
                                    let offset = (field_idx * 8) as i32;
                                    builder.ins().stack_store(param_val, slot, offset);
                                }
                                abi_idx += flattened_count;
                            }
                            _ => {
                                // Non-struct/enum composite params: single ABI param (not flattened)
                                let param_val = builder.block_params(entry_block)[abi_idx];
                                builder.ins().stack_store(param_val, slot, 0);
                                abi_idx += 1;
                            }
                        }
                    }

                    storage.insert(
                        local.id,
                        LocalStorage::StackSlot {
                            slot,
                            field_count,
                            is_enum,
                        },
                    );
                } else {
                    // Zero-element composite: treat as scalar
                    let cl_type = Self::cranelift_type(&local.ty);
                    let var = builder.declare_var(cl_type);
                    if idx < param_count {
                        let param_val = builder.block_params(entry_block)[abi_idx];
                        // ABI params are i64 — reduce to local's declared type if needed
                        let param_val = Self::convert_to_type(builder, param_val, cl_type);
                        builder.def_var(var, param_val);
                        abi_idx += 1;
                    }
                    storage.insert(local.id, LocalStorage::Var(var, cl_type, VarKind::Plain));
                }
            } else {
                // Scalar types use SSA variables
                let cl_type = Self::cranelift_type(&local.ty);
                let var = builder.declare_var(cl_type);
                if idx < param_count {
                    let param_val = builder.block_params(entry_block)[abi_idx];
                    // ABI params are i64 — reduce to local's declared type if needed
                    let param_val = Self::convert_to_type(builder, param_val, cl_type);
                    builder.def_var(var, param_val);
                    abi_idx += 1;
                }
                // Determine VarKind based on MIR type:
                // - Ref to multi-field struct: pointer-based field access
                // - Raw pointer: actual memory load/store on Deref
                // - Everything else: plain scalar
                let var_kind = if matches!(&local.ty, MirType::Pointer { .. }) {
                    VarKind::RawPtr
                } else if matches!(
                    &local.ty,
                    MirType::Ref { inner, .. }
                        if matches!(inner.as_ref(), MirType::Struct { fields, .. } if fields.len() > 1)
                ) {
                    VarKind::Ref
                } else {
                    VarKind::Plain
                };
                storage.insert(local.id, LocalStorage::Var(var, cl_type, var_kind));
            }
        }

        storage
    }

    fn translate_statement(
        stmt: &Statement,
        builder: &mut FunctionBuilder,
        local_storage: &FxHashMap<LocalId, LocalStorage>,
        func_refs: &FxHashMap<rv_hir::FunctionId, cranelift::codegen::ir::FuncRef>,
    ) -> Result<()> {
        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                if place.projection.is_empty() {
                    // Simple assignment to base local
                    let value = Self::translate_rvalue(rvalue, builder, local_storage, func_refs)?;
                    match local_storage.get(&place.local) {
                        Some(LocalStorage::Var(var, var_type, _)) => {
                            // Convert value to match variable's declared type
                            let value = Self::convert_to_type(builder, value, *var_type);
                            builder.def_var(*var, value);
                        }
                        Some(LocalStorage::StackSlot {
                            slot,
                            field_count,
                            is_enum: _,
                        }) => {
                            // Assigning an rvalue to a composite-typed local (struct, tuple, array, enum).
                            if let RValue::Aggregate {
                                kind: AggregateKind::Enum { variant_idx, .. },
                                operands,
                            } = rvalue
                            {
                                // Enum aggregate: write discriminant at slot[0], fields at slot[1..]
                                let discr_val =
                                    builder.ins().iconst(types::I64, *variant_idx as i64);
                                builder.ins().stack_store(discr_val, *slot, 0);
                                for (field_idx, operand) in operands.iter().enumerate() {
                                    if field_idx + 1 >= *field_count {
                                        break;
                                    }
                                    let field_val =
                                        Self::translate_operand(operand, builder, local_storage)?;
                                    let offset = ((field_idx + 1) * 8) as i32;
                                    builder.ins().stack_store(field_val, *slot, offset);
                                }
                            } else if let RValue::Aggregate {
                                kind:
                                    AggregateKind::Struct { .. }
                                    | AggregateKind::Tuple
                                    | AggregateKind::Array(_),
                                operands,
                            } = rvalue
                            {
                                // Struct/Tuple/Array aggregate: write each field individually
                                for (field_idx, operand) in operands.iter().enumerate() {
                                    if field_idx >= *field_count {
                                        break;
                                    }
                                    let field_val =
                                        Self::translate_operand(operand, builder, local_storage)?;
                                    let offset = (field_idx * 8) as i32;
                                    builder.ins().stack_store(field_val, *slot, offset);
                                }
                            } else if let Some(src_slot) =
                                Self::get_source_stack_slot(rvalue, local_storage)
                            {
                                // Whole-struct copy: source is also a StackSlot,
                                // copy all fields from source to destination.
                                for field_idx in 0..*field_count {
                                    let offset = (field_idx * 8) as i32;
                                    let field_val =
                                        builder.ins().stack_load(types::I64, src_slot, offset);
                                    builder.ins().stack_store(field_val, *slot, offset);
                                }
                            } else {
                                // Scalar value assigned to struct slot (e.g., single-field struct
                                // from a function return). Store as field 0.
                                builder.ins().stack_store(value, *slot, 0);
                            }
                        }
                        None => {
                            anyhow::bail!("ICE: No storage allocated for local {:?}", place.local);
                        }
                    }
                } else {
                    // Assignment with projection (e.g., struct field write)
                    let value = Self::translate_rvalue(rvalue, builder, local_storage, func_refs)?;
                    Self::write_place(place, value, builder, local_storage)?;
                }
            }
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {}
        }
        Ok(())
    }

    /// If the rvalue is a Use(Copy/Move) of a whole struct local stored in a StackSlot,
    /// return that source StackSlot so the caller can copy all fields.
    fn get_source_stack_slot(
        rvalue: &RValue,
        local_storage: &FxHashMap<LocalId, LocalStorage>,
    ) -> Option<StackSlot> {
        if let RValue::Use(Operand::Copy(place) | Operand::Move(place)) = rvalue {
            if place.projection.is_empty() {
                if let Some(LocalStorage::StackSlot { slot, .. }) = local_storage.get(&place.local)
                {
                    return Some(*slot);
                }
            }
        }
        None
    }

    /// Write a value to a Place (handles projections)
    fn write_place(
        place: &Place,
        value: Value,
        builder: &mut FunctionBuilder,
        local_storage: &FxHashMap<LocalId, LocalStorage>,
    ) -> Result<()> {
        // Check for raw pointer dereference first — must perform actual memory store
        if let Some(LocalStorage::Var(var, _, VarKind::RawPtr)) = local_storage.get(&place.local) {
            if place.projection.first() == Some(&PlaceElem::Deref) {
                let ptr_val = builder.use_var(*var);
                builder.ins().store(MemFlags::new(), value, ptr_val, 0);
                return Ok(());
            }
        }

        // Strip leading Deref projections for references (no-op in Cranelift JIT)
        let projections: Vec<_> = place
            .projection
            .iter()
            .filter(|p| !matches!(p, PlaceElem::Deref))
            .collect();

        match &projections[..] {
            [PlaceElem::Field { field_idx }] => {
                // Write to a struct/enum field
                match local_storage.get(&place.local) {
                    Some(LocalStorage::StackSlot {
                        slot,
                        field_count,
                        is_enum,
                    }) => {
                        // For enums, slot[0] is discriminant, data fields start at slot[1].
                        // MIR field_idx 0 means "first data field", so offset by 1 for enums.
                        let actual_idx = if *is_enum { field_idx + 1 } else { *field_idx };
                        if actual_idx >= *field_count {
                            anyhow::bail!(
                                "Field index {} out of bounds for composite with {} fields",
                                actual_idx,
                                field_count
                            );
                        }
                        let offset = (actual_idx * 8) as i32;
                        builder.ins().stack_store(value, *slot, offset);
                    }
                    _ => {
                        anyhow::bail!("Field projection on non-composite local {:?}", place.local);
                    }
                }
            }
            [PlaceElem::Index(index_local)] => {
                // Write to an array element
                match local_storage.get(&place.local) {
                    Some(LocalStorage::StackSlot { slot, .. }) => {
                        let index_val = match local_storage.get(index_local) {
                            Some(LocalStorage::Var(var, _, _)) => builder.use_var(*var),
                            Some(LocalStorage::StackSlot { slot: idx_slot, .. }) => {
                                builder.ins().stack_load(types::I64, *idx_slot, 0)
                            }
                            None => anyhow::bail!("Index local {:?} not found", index_local),
                        };
                        // Pointer arithmetic always uses I64
                        let index_val = Self::convert_to_type(builder, index_val, types::I64);
                        let eight = builder.ins().iconst(types::I64, 8);
                        let byte_offset = builder.ins().imul(index_val, eight);
                        let base_addr = builder.ins().stack_addr(types::I64, *slot, 0);
                        let elem_addr = builder.ins().iadd(base_addr, byte_offset);
                        builder.ins().store(MemFlags::new(), value, elem_addr, 0);
                    }
                    _ => {
                        anyhow::bail!("Index projection on non-stack local {:?}", place.local);
                    }
                }
            }
            _ => {
                anyhow::bail!("Unsupported projection in write: {:?}", place.projection);
            }
        }
        Ok(())
    }

    fn translate_rvalue(
        rvalue: &RValue,
        builder: &mut FunctionBuilder,
        local_storage: &FxHashMap<LocalId, LocalStorage>,
        func_refs: &FxHashMap<rv_hir::FunctionId, cranelift::codegen::ir::FuncRef>,
    ) -> Result<Value> {
        match rvalue {
            RValue::Use(operand) => Self::translate_operand(operand, builder, local_storage),
            RValue::BinaryOp { op, left, right } => {
                let left_val = Self::translate_operand(left, builder, local_storage)?;
                let right_val = Self::translate_operand(right, builder, local_storage)?;

                // Check if operands are floats by inspecting the Cranelift value type
                let left_type = builder.func.dfg.value_type(left_val);
                let right_type = builder.func.dfg.value_type(right_val);
                let is_float = left_type == types::F64 || left_type == types::F32;

                // Ensure both operands have the same type — promote narrower to wider
                let (left_val, right_val) = if left_type != right_type
                    && !is_float
                    && left_type.is_int()
                    && right_type.is_int()
                {
                    let wider = if left_type.bits() > right_type.bits() {
                        left_type
                    } else {
                        right_type
                    };
                    (
                        Self::convert_to_type(builder, left_val, wider),
                        Self::convert_to_type(builder, right_val, wider),
                    )
                } else {
                    (left_val, right_val)
                };

                let result = if is_float {
                    match op {
                        rv_mir::BinaryOp::Add => builder.ins().fadd(left_val, right_val),
                        rv_mir::BinaryOp::Sub => builder.ins().fsub(left_val, right_val),
                        rv_mir::BinaryOp::Mul => builder.ins().fmul(left_val, right_val),
                        rv_mir::BinaryOp::Div => builder.ins().fdiv(left_val, right_val),
                        rv_mir::BinaryOp::Mod => {
                            // Cranelift doesn't have fmod; compute a % b = a - floor(a/b) * b
                            let div = builder.ins().fdiv(left_val, right_val);
                            let floored = builder.ins().floor(div);
                            let prod = builder.ins().fmul(floored, right_val);
                            builder.ins().fsub(left_val, prod)
                        }
                        rv_mir::BinaryOp::Eq => {
                            let cmp = builder.ins().fcmp(FloatCC::Equal, left_val, right_val);
                            builder.ins().uextend(types::I64, cmp)
                        }
                        rv_mir::BinaryOp::Ne => {
                            let cmp = builder.ins().fcmp(FloatCC::NotEqual, left_val, right_val);
                            builder.ins().uextend(types::I64, cmp)
                        }
                        rv_mir::BinaryOp::Lt => {
                            let cmp = builder.ins().fcmp(FloatCC::LessThan, left_val, right_val);
                            builder.ins().uextend(types::I64, cmp)
                        }
                        rv_mir::BinaryOp::Le => {
                            let cmp =
                                builder
                                    .ins()
                                    .fcmp(FloatCC::LessThanOrEqual, left_val, right_val);
                            builder.ins().uextend(types::I64, cmp)
                        }
                        rv_mir::BinaryOp::Gt => {
                            let cmp = builder
                                .ins()
                                .fcmp(FloatCC::GreaterThan, left_val, right_val);
                            builder.ins().uextend(types::I64, cmp)
                        }
                        rv_mir::BinaryOp::Ge => {
                            let cmp = builder.ins().fcmp(
                                FloatCC::GreaterThanOrEqual,
                                left_val,
                                right_val,
                            );
                            builder.ins().uextend(types::I64, cmp)
                        }
                        _ => anyhow::bail!("Unsupported float binary op: {:?}", op),
                    }
                } else {
                    match op {
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
                            let cmp =
                                builder
                                    .ins()
                                    .icmp(IntCC::SignedLessThan, left_val, right_val);
                            builder.ins().uextend(types::I64, cmp)
                        }
                        rv_mir::BinaryOp::Le => {
                            let cmp = builder.ins().icmp(
                                IntCC::SignedLessThanOrEqual,
                                left_val,
                                right_val,
                            );
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
                        rv_mir::BinaryOp::And | rv_mir::BinaryOp::BitAnd => {
                            builder.ins().band(left_val, right_val)
                        }
                        rv_mir::BinaryOp::Or | rv_mir::BinaryOp::BitOr => {
                            builder.ins().bor(left_val, right_val)
                        }
                        rv_mir::BinaryOp::BitXor => builder.ins().bxor(left_val, right_val),
                        rv_mir::BinaryOp::Shl => builder.ins().ishl(left_val, right_val),
                        rv_mir::BinaryOp::Shr => builder.ins().sshr(left_val, right_val),
                    }
                };

                Ok(result)
            }
            RValue::UnaryOp { op, operand } => {
                let val = Self::translate_operand(operand, builder, local_storage)?;
                let val_type = builder.func.dfg.value_type(val);
                let is_float = val_type == types::F64 || val_type == types::F32;
                match op {
                    rv_mir::UnaryOp::Neg => {
                        if is_float {
                            Ok(builder.ins().fneg(val))
                        } else {
                            Ok(builder.ins().ineg(val))
                        }
                    }
                    rv_mir::UnaryOp::Not => {
                        // Bitwise NOT (only valid for integers)
                        Ok(builder.ins().bnot(val))
                    }
                }
            }
            RValue::Call { func, args } => {
                let func_ref = func_refs
                    .get(func)
                    .ok_or_else(|| anyhow::anyhow!("Function {:?} not found in func_refs", func))?;

                // Flatten struct/enum arguments: each field becomes a separate i64 arg
                let mut arg_values = Vec::new();
                for arg in args {
                    match arg {
                        Operand::Copy(place) | Operand::Move(place) => {
                            if let Some(LocalStorage::StackSlot {
                                slot,
                                field_count,
                                is_enum: _,
                            }) = local_storage.get(&place.local)
                            {
                                if place.projection.is_empty() {
                                    // Whole struct/enum passed as argument — flatten all fields
                                    // (for enums, this includes discriminant at slot[0] and data fields)
                                    for field_idx in 0..*field_count {
                                        let offset = (field_idx * 8) as i32;
                                        let val =
                                            builder.ins().stack_load(types::I64, *slot, offset);
                                        arg_values.push(val);
                                    }
                                } else {
                                    // Projected place (e.g., field access) — single value
                                    arg_values.push(Self::translate_place(
                                        place,
                                        builder,
                                        local_storage,
                                    )?);
                                }
                            } else {
                                // Scalar local — single value
                                arg_values.push(Self::translate_place(
                                    place,
                                    builder,
                                    local_storage,
                                )?);
                            }
                        }
                        Operand::Constant(_) => {
                            arg_values.push(Self::translate_operand(arg, builder, local_storage)?);
                        }
                    }
                }

                // ABI requires all params to be i64 — extend if needed
                let arg_values: Vec<Value> = arg_values
                    .into_iter()
                    .map(|v| Self::convert_to_type(builder, v, types::I64))
                    .collect();

                let call_inst = builder.ins().call(*func_ref, &arg_values);
                let results = builder.inst_results(call_inst);

                // All functions in our ABI return exactly one i64
                Ok(results[0])
            }
            RValue::Ref { place, .. } => {
                // For references to stack-allocated structs/enums, return the stack address
                // so the receiver can dereference fields via pointer arithmetic.
                // For scalar variables, the value IS the reference representation.
                if place.projection.is_empty() {
                    match local_storage.get(&place.local) {
                        Some(LocalStorage::StackSlot { slot, field_count, .. })
                            if *field_count > 1 =>
                        {
                            return Ok(builder.ins().stack_addr(types::I64, *slot, 0));
                        }
                        _ => {}
                    }
                }
                Self::translate_place(place, builder, local_storage)
            }
            RValue::Aggregate { kind, operands } => {
                // Aggregates produce a single i64 value for assignment.
                // When assigned to a struct-typed local, translate_statement
                // handles writing individual fields to the stack slot.
                // Here we return field 0's value as the "representative" scalar.
                match kind {
                    AggregateKind::Struct { .. }
                    | AggregateKind::Tuple
                    | AggregateKind::Array(_) => {
                        if let Some(first_operand) = operands.first() {
                            Self::translate_operand(first_operand, builder, local_storage)
                        } else {
                            Ok(builder.ins().iconst(types::I64, 0))
                        }
                    }
                    AggregateKind::Enum { variant_idx, .. } => {
                        Ok(builder.ins().iconst(types::I64, *variant_idx as i64))
                    }
                }
            }
            RValue::Discriminant(place) => {
                // Read the discriminant (slot[0]) from an enum's stack storage.
                // We access directly rather than through translate_place to avoid
                // the is_enum field offset that applies to data field access.
                match local_storage.get(&place.local) {
                    Some(LocalStorage::StackSlot { slot, .. }) => {
                        Ok(builder.ins().stack_load(types::I64, *slot, 0))
                    }
                    _ => anyhow::bail!(
                        "Discriminant access on non-enum local {:?}",
                        place.local
                    ),
                }
            }
            RValue::VtableCall { .. } => {
                // VtableCall requires fat pointer infrastructure (data_ptr + vtable_ptr)
                // and indirect function calls through vtable entries.
                // This is deferred until trait object coercion is implemented in Tier 6.
                panic!(
                    "ICE: VtableCall not yet supported in Cranelift backend. \
                     Trait object coercion (&T → &dyn Trait) is required first."
                );
            }
            RValue::Cast { operand, from, to } => {
                let val = Self::translate_operand(operand, builder, local_storage)?;
                let to_cl = Self::cranelift_type(to);
                match (from, to) {
                    // Int → Float
                    (rv_mir::MirType::Int(..), rv_mir::MirType::Float(..)) => {
                        Ok(builder.ins().fcvt_from_sint(to_cl, val))
                    }
                    // Float → Int (truncate)
                    (rv_mir::MirType::Float(..), rv_mir::MirType::Int(..)) => {
                        Ok(builder.ins().fcvt_to_sint(to_cl, val))
                    }
                    // Bool → Int (already integer representation)
                    (rv_mir::MirType::Bool, rv_mir::MirType::Int(..)) => Ok(val),
                    // Int → Bool (nonzero check)
                    (rv_mir::MirType::Int(..), rv_mir::MirType::Bool) => {
                        let from_cl = Self::cranelift_type(from);
                        let zero = builder.ins().iconst(from_cl, 0);
                        let cmp = builder.ins().icmp(IntCC::NotEqual, val, zero);
                        Ok(builder.ins().uextend(to_cl, cmp))
                    }
                    // Pointer casts: all pointers are I64 in Cranelift, so these are
                    // identity operations (with possible int width conversion)
                    (rv_mir::MirType::Int(..), rv_mir::MirType::Pointer { .. })
                    | (rv_mir::MirType::Pointer { .. }, rv_mir::MirType::Int(..))
                    | (rv_mir::MirType::Pointer { .. }, rv_mir::MirType::Pointer { .. })
                    | (rv_mir::MirType::Ref { .. }, rv_mir::MirType::Pointer { .. })
                    | (rv_mir::MirType::Pointer { .. }, rv_mir::MirType::Ref { .. }) => {
                        Ok(Self::convert_to_type(builder, val, to_cl))
                    }
                    // Same type or unsupported: pass through
                    _ => Ok(val),
                }
            }
            RValue::Intrinsic {
                intrinsic,
                args,
                type_args,
            } => {
                Self::translate_intrinsic(intrinsic, args, type_args, builder, local_storage)
            }
            RValue::BoxNew { operand, .. } => {
                // Box allocation: allocate stack slot and store the value
                // For JIT compilation, we use stack allocation (similar to alloca in LLVM)
                let value = Self::translate_operand(operand, builder, local_storage)?;

                // Create a stack slot to hold the boxed value (8 bytes for i64)
                let slot = builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    8, // size in bytes
                    0, // default alignment
                ));

                // Store the value into the stack slot
                builder.ins().stack_store(value, slot, 0);

                // Get the address of the stack slot to return as the "pointer"
                let addr = builder.ins().stack_addr(types::I64, slot, 0);
                Ok(addr)
            }
            RValue::BoxFree { .. } => {
                // Box deallocation: no-op for stack-allocated boxes in JIT
                // The stack slot is automatically freed when the function returns
                Ok(builder.ins().iconst(types::I64, 0))
            }
        }
    }

    /// Translate a compiler intrinsic to Cranelift IR
    fn translate_intrinsic(
        intrinsic: &rv_mir::Intrinsic,
        args: &[Operand],
        type_args: &[MirType],
        builder: &mut FunctionBuilder,
        local_storage: &FxHashMap<LocalId, LocalStorage>,
    ) -> Result<Value> {
        // Get the intrinsic name - we need to pattern match on it
        // Since we don't have access to the interner here, we match on the symbol's debug repr
        let name_str = format!("{:?}", intrinsic.name);

        // Helper to get argument values
        let mut get_arg = |idx: usize| -> Result<Value> {
            args.get(idx)
                .ok_or_else(|| anyhow::anyhow!("Intrinsic missing argument {}", idx))
                .and_then(|arg| Self::translate_operand(arg, builder, local_storage))
        };

        // The symbol debug output includes quotes, extract the name
        // Format is typically Symbol(...) or just the number, so we check for known patterns
        // For a more robust solution, we'd need the interner, but we can work with common cases
        match name_str.as_str() {
            // Memory intrinsics - these need type_args
            s if s.contains("size_of") && !s.contains("val") => {
                let size = type_args
                    .first()
                    .map(Self::calculate_size_of)
                    .unwrap_or(8);
                Ok(builder.ins().iconst(types::I64, size as i64))
            }
            s if s.contains("align_of") && !s.contains("val") => {
                let align = type_args
                    .first()
                    .map(Self::calculate_align_of)
                    .unwrap_or(8);
                Ok(builder.ins().iconst(types::I64, align as i64))
            }
            s if s.contains("size_of_val") => {
                let size = type_args
                    .first()
                    .map(Self::calculate_size_of)
                    .unwrap_or(8);
                Ok(builder.ins().iconst(types::I64, size as i64))
            }
            s if s.contains("align_of_val") => {
                let align = type_args
                    .first()
                    .map(Self::calculate_align_of)
                    .unwrap_or(8);
                Ok(builder.ins().iconst(types::I64, align as i64))
            }
            s if s.contains("transmute") => {
                // Transmute is a no-op at the bit level
                get_arg(0)
            }
            s if s.contains("forget") => {
                // forget is a no-op
                Ok(builder.ins().iconst(types::I64, 0))
            }
            s if s.contains("needs_drop") => {
                let needs = type_args.first().map(Self::type_needs_drop).unwrap_or(true);
                Ok(builder.ins().iconst(types::I64, i64::from(needs)))
            }

            // Arithmetic intrinsics
            s if s.contains("add_with_overflow") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                // Cranelift doesn't have overflow-detecting add directly
                // We compute result and check if it overflowed
                let result = builder.ins().iadd(a, b);
                // Overflow detection: if signs of inputs are same but result sign differs
                // For simplicity, just return the result (caller can check separately)
                // This is a tuple (result, overflow) - return result for now
                Ok(result)
            }
            s if s.contains("sub_with_overflow") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                Ok(builder.ins().isub(a, b))
            }
            s if s.contains("mul_with_overflow") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                Ok(builder.ins().imul(a, b))
            }
            s if s.contains("wrapping_add") | s.contains("unchecked_add") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                Ok(builder.ins().iadd(a, b))
            }
            s if s.contains("wrapping_sub") | s.contains("unchecked_sub") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                Ok(builder.ins().isub(a, b))
            }
            s if s.contains("wrapping_mul") | s.contains("unchecked_mul") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                Ok(builder.ins().imul(a, b))
            }
            s if s.contains("saturating_add") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                Ok(builder.ins().sadd_sat(a, b))
            }
            s if s.contains("saturating_sub") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                Ok(builder.ins().ssub_sat(a, b))
            }
            s if s.contains("unchecked_div") | s.contains("exact_div") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                Ok(builder.ins().sdiv(a, b))
            }
            s if s.contains("rotate_left") => {
                let val = get_arg(0)?;
                let shift = get_arg(1)?;
                Ok(builder.ins().rotl(val, shift))
            }
            s if s.contains("rotate_right") => {
                let val = get_arg(0)?;
                let shift = get_arg(1)?;
                Ok(builder.ins().rotr(val, shift))
            }
            s if s.contains("ctlz") => {
                let val = get_arg(0)?;
                Ok(builder.ins().clz(val))
            }
            s if s.contains("cttz") => {
                let val = get_arg(0)?;
                Ok(builder.ins().ctz(val))
            }
            s if s.contains("ctpop") => {
                let val = get_arg(0)?;
                Ok(builder.ins().popcnt(val))
            }
            s if s.contains("bitreverse") => {
                let val = get_arg(0)?;
                Ok(builder.ins().bitrev(val))
            }
            s if s.contains("bswap") => {
                let val = get_arg(0)?;
                Ok(builder.ins().bswap(val))
            }

            // Float intrinsics
            s if s.contains("sqrtf32") => {
                let val = get_arg(0)?;
                Ok(builder.ins().sqrt(val))
            }
            s if s.contains("sqrtf64") => {
                let val = get_arg(0)?;
                Ok(builder.ins().sqrt(val))
            }
            s if s.contains("floorf32") | s.contains("floorf64") => {
                let val = get_arg(0)?;
                Ok(builder.ins().floor(val))
            }
            s if s.contains("ceilf32") | s.contains("ceilf64") => {
                let val = get_arg(0)?;
                Ok(builder.ins().ceil(val))
            }
            s if s.contains("truncf32") | s.contains("truncf64") => {
                let val = get_arg(0)?;
                Ok(builder.ins().trunc(val))
            }
            s if s.contains("fmaf32") | s.contains("fmaf64") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                let c = get_arg(2)?;
                Ok(builder.ins().fma(a, b, c))
            }
            s if s.contains("float_to_int") => {
                let val = get_arg(0)?;
                Ok(builder.ins().fcvt_to_sint(types::I64, val))
            }

            // Control intrinsics
            s if s.contains("unreachable") => {
                // Use user trap code 100 for unreachable (user codes start at 1)
                builder.ins().trap(TrapCode::unwrap_user(100));
                // Return a dummy value since this is unreachable
                Ok(builder.ins().iconst(types::I64, 0))
            }
            s if s.contains("assume") => {
                // assume is a no-op hint
                Ok(builder.ins().iconst(types::I64, 0))
            }
            s if s.contains("likely") | s.contains("unlikely") => {
                // Branch hints - just pass through the boolean
                get_arg(0)
            }
            s if s.contains("abort") => {
                // Use unwrap_user for user-defined trap codes
                builder.ins().trap(TrapCode::unwrap_user(1));
                Ok(builder.ins().iconst(types::I64, 0))
            }
            s if s.contains("type_id") => {
                // Return a hash of the type
                let hash = type_args.first().map(Self::type_hash).unwrap_or(0);
                Ok(builder.ins().iconst(types::I64, hash as i64))
            }

            // Pointer intrinsics
            s if s.contains("offset") | s.contains("arith_offset") => {
                let ptr = get_arg(0)?;
                let offset = get_arg(1)?;
                let elem_size = type_args
                    .first()
                    .map(Self::calculate_size_of)
                    .unwrap_or(1);
                let scaled = builder.ins().imul_imm(offset, elem_size as i64);
                Ok(builder.ins().iadd(ptr, scaled))
            }
            s if s.contains("ptr_offset_from") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                let diff = builder.ins().isub(a, b);
                let elem_size = type_args
                    .first()
                    .map(Self::calculate_size_of)
                    .unwrap_or(1);
                if elem_size > 1 {
                    Ok(builder.ins().sdiv_imm(diff, elem_size as i64))
                } else {
                    Ok(diff)
                }
            }
            s if s.contains("raw_eq") => {
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                let cmp = builder.ins().icmp(IntCC::Equal, a, b);
                Ok(builder.ins().uextend(types::I64, cmp))
            }

            // Default fallback: return first argument or zero
            _ => {
                if args.is_empty() {
                    Ok(builder.ins().iconst(types::I64, 0))
                } else {
                    get_arg(0)
                }
            }
        }
    }

    /// Calculate the size of a MIR type in bytes (for intrinsics)
    fn calculate_size_of(ty: &MirType) -> usize {
        match ty {
            MirType::Unit | MirType::Never => 0,
            MirType::Bool => 1,
            MirType::Char => 4,
            MirType::Int(width, _) => match width {
                rv_hir::IntWidth::I8 => 1,
                rv_hir::IntWidth::I16 => 2,
                rv_hir::IntWidth::I32 => 4,
                rv_hir::IntWidth::I64 => 8,
                rv_hir::IntWidth::I128 => 16,
                rv_hir::IntWidth::Isize => 8,
            },
            MirType::Float(width) => match width {
                rv_hir::FloatWidth::F32 => 4,
                rv_hir::FloatWidth::F64 => 8,
            },
            MirType::String | MirType::Slice { .. } => 16, // Fat pointer
            MirType::Ref { inner, .. } | MirType::Pointer { inner, .. } | MirType::Box { inner } => {
                if inner.is_unsized() { 16 } else { 8 }
            }
            MirType::Tuple(elements) => {
                let mut size = 0;
                for elem in elements {
                    let align = Self::calculate_align_of(elem);
                    size = (size + align - 1) & !(align - 1);
                    size += Self::calculate_size_of(elem);
                }
                let total_align = Self::calculate_align_of(ty);
                (size + total_align - 1) & !(total_align - 1)
            }
            MirType::Array { element, size } => Self::calculate_size_of(element) * size,
            MirType::Struct { fields, .. } => {
                let mut size = 0;
                for field in fields {
                    let align = Self::calculate_align_of(field);
                    size = (size + align - 1) & !(align - 1);
                    size += Self::calculate_size_of(field);
                }
                let total_align = Self::calculate_align_of(ty);
                (size + total_align - 1) & !(total_align - 1)
            }
            MirType::Enum { variants, .. } => {
                let discriminant_size = if variants.len() <= 256 { 1 } else { 4 };
                let max_payload: usize = variants
                    .iter()
                    .map(|v| v.fields.iter().map(Self::calculate_size_of).sum::<usize>())
                    .max()
                    .unwrap_or(0);
                let total_align = Self::calculate_align_of(ty);
                let size = discriminant_size + max_payload;
                (size + total_align - 1) & !(total_align - 1)
            }
            MirType::Named(_) | MirType::ImplTrait { .. } | MirType::DynTrait { .. } => 8,
            MirType::Function { .. } | MirType::FunctionPointer { .. } => 8,
        }
    }

    /// Calculate the alignment of a MIR type in bytes (for intrinsics)
    fn calculate_align_of(ty: &MirType) -> usize {
        match ty {
            MirType::Unit | MirType::Never => 1,
            MirType::Bool => 1,
            MirType::Char => 4,
            MirType::Int(width, _) => match width {
                rv_hir::IntWidth::I8 => 1,
                rv_hir::IntWidth::I16 => 2,
                rv_hir::IntWidth::I32 => 4,
                rv_hir::IntWidth::I64 => 8,
                rv_hir::IntWidth::I128 => 16,
                rv_hir::IntWidth::Isize => 8,
            },
            MirType::Float(width) => match width {
                rv_hir::FloatWidth::F32 => 4,
                rv_hir::FloatWidth::F64 => 8,
            },
            MirType::String | MirType::Slice { .. } => 8,
            MirType::Ref { .. } | MirType::Pointer { .. } | MirType::Box { .. } | MirType::DynTrait { .. } => 8,
            MirType::Tuple(elements) => elements.iter().map(Self::calculate_align_of).max().unwrap_or(1),
            MirType::Array { element, .. } => Self::calculate_align_of(element),
            MirType::Struct { fields, .. } => fields.iter().map(Self::calculate_align_of).max().unwrap_or(1),
            MirType::Enum { variants, .. } => {
                variants.iter().flat_map(|v| v.fields.iter()).map(Self::calculate_align_of).max().unwrap_or(1).max(1)
            }
            MirType::Named(_) | MirType::ImplTrait { .. } => 8,
            MirType::Function { .. } | MirType::FunctionPointer { .. } => 8,
        }
    }

    /// Check if a type needs drop (for needs_drop intrinsic)
    fn type_needs_drop(ty: &MirType) -> bool {
        match ty {
            MirType::Unit | MirType::Bool | MirType::Char | MirType::Int(_, _)
            | MirType::Float(_) | MirType::Never => false,
            MirType::Pointer { .. } | MirType::FunctionPointer { .. } | MirType::Function { .. } => false,
            MirType::Ref { .. } => false,
            MirType::Box { .. } | MirType::String => true,
            MirType::Tuple(elements) => elements.iter().any(Self::type_needs_drop),
            MirType::Array { element, .. } => Self::type_needs_drop(element),
            MirType::Struct { fields, .. } => fields.iter().any(Self::type_needs_drop),
            MirType::Enum { variants, .. } => variants.iter().any(|v| v.fields.iter().any(Self::type_needs_drop)),
            MirType::Slice { element } => Self::type_needs_drop(element),
            MirType::DynTrait { .. } => true,
            MirType::Named(_) | MirType::ImplTrait { .. } => true,
        }
    }

    /// Compute a simple hash for a type (for type_id intrinsic)
    fn type_hash(ty: &MirType) -> u64 {
        use std::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        // Simple discriminant-based hash
        std::mem::discriminant(ty).hash(&mut hasher);
        hasher.finish()
    }

    fn translate_operand(
        operand: &Operand,
        builder: &mut FunctionBuilder,
        local_storage: &FxHashMap<LocalId, LocalStorage>,
    ) -> Result<Value> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                Self::translate_place(place, builder, local_storage)
            }
            Operand::Constant(constant) => {
                let cl_type = Self::cranelift_type(&constant.ty);
                match &constant.kind {
                    LiteralKind::Integer(n, _) => Ok(builder.ins().iconst(cl_type, *n)),
                    LiteralKind::Bool(b) => Ok(builder.ins().iconst(cl_type, i64::from(*b))),
                    LiteralKind::Unit => Ok(builder.ins().iconst(cl_type, 0)),
                    LiteralKind::Char(c) => Ok(builder.ins().iconst(cl_type, *c as i64)),
                    LiteralKind::Float(f, Some(rv_hir::FloatWidth::F32)) => {
                        Ok(builder.ins().f32const(*f as f32))
                    }
                    LiteralKind::Float(f, _) => Ok(builder.ins().f64const(*f)),
                    LiteralKind::String(s) => {
                        // Store the string data in a leaked heap allocation and return the
                        // pointer as an i64. This is safe because the JIT runs in-process
                        // and the string data lives for the duration of the JIT execution.
                        let ptr = Box::leak(s.clone().into_boxed_str()).as_ptr();
                        Ok(builder.ins().iconst(types::I64, ptr as i64))
                    }
                }
            }
        }
    }

    /// Read a value from a Place, handling field projections on stack-slot structs.
    fn translate_place(
        place: &Place,
        builder: &mut FunctionBuilder,
        local_storage: &FxHashMap<LocalId, LocalStorage>,
    ) -> Result<Value> {
        let storage = local_storage
            .get(&place.local)
            .ok_or_else(|| anyhow::anyhow!("No storage for local {:?}", place.local))?;

        if place.projection.is_empty() {
            // No projection — read the base value
            match storage {
                LocalStorage::Var(var, _, _) => Ok(builder.use_var(*var)),
                LocalStorage::StackSlot { slot, .. } => {
                    // Reading a whole struct — return field 0 as the scalar representation.
                    // This is used when passing a struct to a function call as a single i64.
                    Ok(builder.ins().stack_load(types::I64, *slot, 0))
                }
            }
        } else {
            // Check for raw pointer dereference first — must perform actual memory load
            if let Some(LocalStorage::Var(var, _, VarKind::RawPtr)) =
                local_storage.get(&place.local)
            {
                if place.projection.first() == Some(&PlaceElem::Deref) {
                    let ptr_val = builder.use_var(*var);
                    // Load the value at the pointer address
                    return Ok(builder.ins().load(types::I64, MemFlags::new(), ptr_val, 0));
                }
            }

            // Strip Deref projections for references — in the Cranelift JIT, references
            // are either stack addresses (VarKind::Ref) or direct values. Deref is handled
            // by the VarKind flag on LocalStorage::Var, not as a runtime operation.
            let projections: Vec<_> = place
                .projection
                .iter()
                .filter(|p| !matches!(p, PlaceElem::Deref))
                .collect();

            match (&projections[..], storage) {
                (
                    [PlaceElem::Field { field_idx }],
                    LocalStorage::StackSlot {
                        slot,
                        field_count,
                        is_enum,
                    },
                ) => {
                    // For enums, slot[0] is discriminant, data fields start at slot[1].
                    // MIR field_idx 0 means "first data field", so offset by 1 for enums.
                    let actual_idx = if *is_enum { field_idx + 1 } else { *field_idx };
                    if actual_idx >= *field_count {
                        anyhow::bail!(
                            "Field index {} out of bounds for composite with {} fields",
                            actual_idx,
                            field_count
                        );
                    }
                    let offset = (actual_idx * 8) as i32;
                    Ok(builder.ins().stack_load(types::I64, *slot, offset))
                }
                ([PlaceElem::Field { field_idx }], LocalStorage::Var(var, _, var_kind)) => {
                    if *var_kind == VarKind::Ref {
                        // Var holds a pointer to a struct (set by RValue::Ref on a
                        // multi-field StackSlot). Load field via pointer arithmetic.
                        let base_ptr = builder.use_var(*var);
                        let offset = builder.ins().iconst(types::I64, (*field_idx * 8) as i64);
                        let field_addr = builder.ins().iadd(base_ptr, offset);
                        Ok(builder
                            .ins()
                            .load(types::I64, MemFlags::new(), field_addr, 0))
                    } else if *field_idx == 0 {
                        // Var holds a scalar value (single-field struct passed by value,
                        // or a direct value). Field 0 IS the value itself.
                        Ok(builder.use_var(*var))
                    } else {
                        anyhow::bail!(
                            "Field index {} on non-reference Var {:?}",
                            field_idx,
                            place.local
                        )
                    }
                }
                ([PlaceElem::Index(index_local)], LocalStorage::StackSlot { slot, .. }) => {
                    // Array indexing: load index from local, compute offset, load element
                    let index_val = match local_storage.get(index_local) {
                        Some(LocalStorage::Var(var, _, _)) => builder.use_var(*var),
                        Some(LocalStorage::StackSlot { slot: idx_slot, .. }) => {
                            builder.ins().stack_load(types::I64, *idx_slot, 0)
                        }
                        None => anyhow::bail!("Index local {:?} not found", index_local),
                    };
                    // Pointer arithmetic always uses I64
                    let index_val = Self::convert_to_type(builder, index_val, types::I64);
                    // offset = index * 8
                    let eight = builder.ins().iconst(types::I64, 8);
                    let byte_offset = builder.ins().imul(index_val, eight);
                    // Load from stack slot base + dynamic offset using stack_addr + load
                    let base_addr = builder.ins().stack_addr(types::I64, *slot, 0);
                    let elem_addr = builder.ins().iadd(base_addr, byte_offset);
                    Ok(builder
                        .ins()
                        .load(types::I64, MemFlags::new(), elem_addr, 0))
                }
                _ => {
                    anyhow::bail!(
                        "Unsupported projection {:?} on local {:?}",
                        projections,
                        place.local
                    );
                }
            }
        }
    }

    fn translate_terminator(
        terminator: &Terminator,
        builder: &mut FunctionBuilder,
        local_storage: &FxHashMap<LocalId, LocalStorage>,
        block_map: &FxHashMap<usize, Block>,
    ) -> Result<()> {
        match terminator {
            Terminator::Return { value, .. } => {
                if let Some(operand) = value {
                    let val = Self::translate_operand(operand, builder, local_storage)?;
                    // ABI always returns i64 — extend if needed
                    let val = Self::convert_to_type(builder, val, types::I64);
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
                ..
            } => {
                let discr_val = Self::translate_operand(discriminant, builder, local_storage)?;

                let mut switch = cranelift::frontend::Switch::new();
                for (value, target_bb) in targets {
                    let target_block = block_map[target_bb];
                    switch.set_entry(*value, target_block);
                }

                let otherwise_block = block_map[otherwise];
                switch.emit(builder, discr_val, otherwise_block);
            }
            Terminator::Call { .. } => {
                anyhow::bail!(
                    "Terminator::Call is not supported in the Cranelift backend. \
                     Function calls should be lowered as RValue::Call statements."
                )
            }
            Terminator::Drop { target, .. } => {
                // Box drop: No-op for stack-allocated boxes (using create_sized_stack_slot)
                // The stack memory is automatically freed when the function returns.
                // TODO(tier4): Emit call to Drop::drop if the type implements Drop.
                // For now, just jump to the continuation block.
                let target_block = block_map[target];
                builder.ins().jump(target_block, &[]);
            }
            Terminator::Unreachable => {
                builder
                    .ins()
                    .trap(cranelift::codegen::ir::TrapCode::unwrap_user(1));
            }
            Terminator::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                let cond_val = Self::translate_operand(cond, builder, local_storage)?;
                let target_block = block_map[target];

                // Create a trap block for assertion failure
                let trap_block = builder.create_block();

                if *expected {
                    // Expected true: branch to target if cond is non-zero, trap otherwise
                    builder.ins().brif(cond_val, target_block, &[], trap_block, &[]);
                } else {
                    // Expected false: branch to target if cond is zero, trap otherwise
                    builder.ins().brif(cond_val, trap_block, &[], target_block, &[]);
                }

                // Emit trap block
                builder.switch_to_block(trap_block);
                builder.seal_block(trap_block);
                builder
                    .ins()
                    .trap(cranelift::codegen::ir::TrapCode::unwrap_user(2));
            }
        }
        Ok(())
    }
}

impl Default for JitCompiler {
    fn default() -> Self {
        Self::new().expect("Failed to create JIT compiler")
    }
}
