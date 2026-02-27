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
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum};
use inkwell::values::{BasicValueEnum, FunctionValue};
use inkwell::IntPredicate;
use rv_hir::{FunctionId, LiteralKind};
use rv_lir::LirExternalFunction;
use rv_lir::{
    AggregateKind, BasicBlock, BinaryOp, Constant, LirFunction, LocalId, Operand, Place, PlaceElem,
    RValue, Statement, Terminator, UnaryOp,
};
use std::collections::HashMap;
use std::path::Path;

pub struct LLVMBackend {
    context: Context,
    module_name: String,
    opt_level: OptLevel,
    // Store compiled module and compiler state
    // SAFETY: This uses unsafe code to work around self-referential struct limitations
    // The compiler borrows from context with a lifetime, but we ensure the context
    // lives as long as the LLVMBackend, making this safe.
    compiled_state: std::cell::RefCell<Option<CompiledState>>,
}

struct CompiledState {
    ir: String,
}

impl LLVMBackend {
    pub fn new(module_name: &str, opt_level: OptLevel) -> Result<Self> {
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
            module_name: module_name.to_string(),
            opt_level,
            compiled_state: std::cell::RefCell::new(None),
        })
    }

    pub fn compile_and_write_object(
        &self,
        functions: &[LirFunction],
        external_functions: &HashMap<FunctionId, LirExternalFunction>,
        output_path: &Path,
    ) -> Result<()> {
        let compiler = Compiler::new(&self.context, &self.module_name, self.opt_level);
        compiler.compile_functions_with_externals(functions, external_functions)?;

        // Store IR for debugging
        let ir = compiler.module.print_to_string().to_string();
        *self.compiled_state.borrow_mut() = Some(CompiledState { ir });

        // Write object file directly from the compiler's module
        compiler.write_object_file(output_path)?;

        Ok(())
    }

    pub fn compile_functions_with_externals(
        &self,
        functions: &[LirFunction],
        external_functions: &HashMap<FunctionId, LirExternalFunction>,
    ) -> Result<()> {
        let compiler = Compiler::new(&self.context, &self.module_name, self.opt_level);
        compiler.compile_functions_with_externals(functions, external_functions)?;

        // Get IR string for later use
        let ir = compiler.module.print_to_string().to_string();

        *self.compiled_state.borrow_mut() = Some(CompiledState { ir });

        Ok(())
    }

    pub fn compile_functions(&self, functions: &[LirFunction]) -> Result<()> {
        self.compile_functions_with_externals(functions, &HashMap::new())
    }

    pub fn to_llvm_ir(&self) -> String {
        self.compiled_state
            .borrow()
            .as_ref()
            .map(|state| state.ir.clone())
            .unwrap_or_else(|| "".to_string())
    }

    pub fn write_object_file(&self, output_path: &Path) -> Result<()> {
        if let Some(state) = self.compiled_state.borrow().as_ref() {
            // Create a new module from the IR string
            let memory_buffer = inkwell::memory_buffer::MemoryBuffer::create_from_memory_range(
                state.ir.as_bytes(),
                &self.module_name,
            );
            let module = self
                .context
                .create_module_from_ir(memory_buffer)
                .map_err(|e| anyhow::anyhow!("Failed to parse IR: {}", e))?;

            // Write object file
            self.write_module_to_object(&module, output_path)
        } else {
            anyhow::bail!("No compiled IR available. Call compile_functions_with_externals first.")
        }
    }

    fn write_module_to_object(&self, module: &Module, output_path: &Path) -> Result<()> {
        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple)
            .map_err(|e| anyhow::anyhow!("Failed to create target from triple: {}", e))?;

        let cpu = TargetMachine::get_host_cpu_name();
        let features = TargetMachine::get_host_cpu_features();

        let target_machine = target
            .create_target_machine(
                &triple,
                cpu.to_str().unwrap_or("generic"),
                features.to_str().unwrap_or(""),
                self.opt_level.to_inkwell(),
                RelocMode::PIC,
                CodeModel::Default,
            )
            .ok_or_else(|| anyhow::anyhow!("Failed to create target machine"))?;

        target_machine
            .write_to_file(module, FileType::Object, output_path)
            .map_err(|e| anyhow::anyhow!("Failed to write object file: {}", e))?;

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
        external_funcs: &HashMap<FunctionId, LirExternalFunction>,
    ) -> HashMap<FunctionId, FunctionValue<'ctx>> {
        let mut llvm_functions = HashMap::new();

        for (func_id, ext_func) in external_funcs {
            // Determine parameter types from resolved LIR types
            let param_types: Vec<BasicMetadataTypeEnum> = ext_func
                .param_types
                .iter()
                .map(|lir_ty| self.type_lowering.lower_type(lir_ty).into())
                .collect();

            // Determine return type from resolved LIR type
            let fn_type = if let Some(ref ret_lir_ty) = ext_func.return_type {
                let ret_llvm_ty = self.type_lowering.lower_type(ret_lir_ty);
                ret_llvm_ty.fn_type(&param_types, false)
            } else {
                self.context.void_type().fn_type(&param_types, false)
            };

            // The mangled_name field contains the correct symbol name to use
            // (either mangled for Rust ABI or unmangled for C ABI)
            let fn_name = ext_func
                .mangled_name
                .clone()
                .unwrap_or_else(|| format!("extern_func_{}", func_id.0));

            // Declare the external function
            let function = self.module.add_function(&fn_name, fn_type, None);
            llvm_functions.insert(*func_id, function);
        }

        llvm_functions
    }

    /// Compile multiple MIR functions with external function support
    pub fn compile_functions_with_externals(
        &self,
        mir_funcs: &[LirFunction],
        external_funcs: &HashMap<FunctionId, LirExternalFunction>,
    ) -> Result<()> {
        // Phase 0: Declare all external functions
        let mut llvm_functions = self.declare_external_functions(external_funcs);

        // Phase 1: Declare all regular functions (external functions already declared)

        for mir_func in mir_funcs {
            // Use the param_count field from LirFunction directly
            let param_count = mir_func.param_count;

            // Create function signature using actual parameter types from MIR locals
            // Parameters are the first N locals in MIR (LocalId(0), LocalId(1), ...)
            use inkwell::types::BasicMetadataTypeEnum;
            use rv_lir::LocalId;
            let param_types: Vec<BasicMetadataTypeEnum> = (0..param_count)
                .map(|i| {
                    // Find the local with this LocalId
                    let local_id = LocalId(i as u32);
                    if let Some(local) = mir_func.locals.iter().find(|local| local.id == local_id) {
                        let basic_type = self.type_lowering.lower_type(&local.ty);
                        basic_type.into()
                    } else {
                        self.context.i64_type().into()
                    }
                })
                .collect();
            let ret_type = self.type_lowering.lower_type(&mir_func.return_type);
            let fn_type = ret_type.fn_type(&param_types, false);

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

        // Phase 4: Create main() wrapper that calls first function and exits
        if !mir_funcs.is_empty() {
            self.create_main_wrapper(&llvm_functions, &mir_funcs[0])?;
        }

        Ok(())
    }

    /// Create a main() wrapper function that calls the entry point and exits.
    ///
    /// The wrapper calls the user's entry function and uses its return value
    /// (truncated to i32) as the process exit code.
    fn create_main_wrapper(
        &self,
        llvm_functions: &HashMap<FunctionId, FunctionValue>,
        entry_func: &LirFunction,
    ) -> Result<()> {
        // Create main() function with signature: int main()
        let main_fn_type = self.context.i32_type().fn_type(&[], false);
        let main_function = self.module.add_function("main", main_fn_type, None);

        // Create entry basic block
        let entry_block = self.context.append_basic_block(main_function, "entry");
        self.builder.position_at_end(entry_block);

        // Call the entry function
        if let Some(&entry_fn_value) = llvm_functions.get(&entry_func.id) {
            let call_site = self.builder.build_call(entry_fn_value, &[], "call_entry")?;

            // Use the entry function's return value as the exit code
            if let Some(return_value) = call_site.try_as_basic_value().left() {
                // Truncate/extend to i32 for the exit code
                let exit_code = if return_value.is_int_value() {
                    let int_val = return_value.into_int_value();
                    let bit_width = int_val.get_type().get_bit_width();
                    if bit_width > 32 {
                        self.builder
                            .build_int_truncate(int_val, self.context.i32_type(), "trunc_exit")
                            .map_err(|e| anyhow::anyhow!("Failed to truncate exit code: {}", e))?
                    } else if bit_width < 32 {
                        self.builder
                            .build_int_z_extend(int_val, self.context.i32_type(), "zext_exit")
                            .map_err(|e| anyhow::anyhow!("Failed to extend exit code: {}", e))?
                    } else {
                        int_val
                    }
                } else {
                    // Non-integer return (struct, float, etc.) — exit 0
                    self.context.i32_type().const_int(0, false)
                };

                self.builder.build_return(Some(&exit_code))?;
            } else {
                // Void return — exit 0
                self.builder
                    .build_return(Some(&self.context.i32_type().const_int(0, false)))?;
            }
        } else {
            // Entry function not found — exit 1
            self.builder
                .build_return(Some(&self.context.i32_type().const_int(1, false)))?;
        }

        Ok(())
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
                RelocMode::PIC,
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
    compiler: &'a Compiler<'ctx>,
    function: FunctionValue<'ctx>,
    mir_func: &'a LirFunction,
    locals: HashMap<LocalId, BasicValueEnum<'ctx>>,
    blocks: HashMap<usize, inkwell::basic_block::BasicBlock<'ctx>>,
    llvm_functions: &'a HashMap<rv_hir::FunctionId, FunctionValue<'ctx>>,
}

impl<'a, 'ctx> FunctionCodegen<'a, 'ctx> {
    fn new(
        compiler: &'a Compiler<'ctx>,
        function: FunctionValue<'ctx>,
        mir_func: &'a LirFunction,
        llvm_functions: &'a HashMap<rv_hir::FunctionId, FunctionValue<'ctx>>,
    ) -> Self {
        Self {
            compiler,
            function,
            mir_func,
            locals: HashMap::new(),
            blocks: HashMap::new(),
            llvm_functions,
        }
    }

    // Helper methods to access compiler fields
    fn context(&self) -> &'ctx Context {
        self.compiler.context
    }

    fn builder(&self) -> &Builder<'ctx> {
        &self.compiler.builder
    }

    fn type_lowering(&self) -> &TypeLowering<'ctx> {
        &self.compiler.type_lowering
    }

    fn build(&mut self) -> Result<()> {
        let context = self.compiler.context;

        // Create all basic blocks
        for (idx, _) in self.mir_func.basic_blocks.iter().enumerate() {
            let bb_name = format!("bb{}", idx);
            let bb = context.append_basic_block(self.function, &bb_name);
            self.blocks.insert(idx, bb);
        }

        // Position at entry block
        if let Some(entry_bb) = self.blocks.get(&self.mir_func.entry_block) {
            self.builder().position_at_end(*entry_bb);
        }

        // Allocate space for all locals
        for local in &self.mir_func.locals {
            let llvm_type = self.type_lowering().lower_type(&local.ty);
            let alloca = self
                .builder()
                .build_alloca(llvm_type, &format!("local_{}", local.id.0))
                .map_err(|e| anyhow::anyhow!("Failed to create alloca: {}", e))?;
            self.locals.insert(local.id, alloca.into());
        }

        // Initialize function parameters by storing them into their local allocas
        // MIR represents parameters as the first N locals
        let llvm_params = self.function.get_params();
        for (param_idx, param_value) in llvm_params.iter().enumerate() {
            // Parameters are the first locals (LocalId(0), LocalId(1), ...)
            let local_id = LocalId(param_idx as u32);
            if let Some(local_alloca) = self.locals.get(&local_id) {
                if let BasicValueEnum::PointerValue(ptr) = local_alloca {
                    self.builder()
                        .build_store(*ptr, *param_value)
                        .map_err(|e| anyhow::anyhow!("Failed to store parameter: {}", e))?;
                }
            }
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
            self.builder().position_at_end(*llvm_bb);
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
                        let local_ty = self
                            .mir_func
                            .locals
                            .iter()
                            .find(|l| l.id == place.local)
                            .map(|l| &l.ty);

                        if let Some(ty) = local_ty {
                            let expected_type = self.type_lowering().lower_type(ty);
                            if let BasicTypeEnum::IntType(expected_int_type) = expected_type {
                                let expected_width = expected_int_type.get_bit_width();

                                // Convert if widths don't match
                                if value_width < expected_width {
                                    // Zero-extend smaller values (e.g., i1 -> i32)
                                    value = self
                                        .builder()
                                        .build_int_z_extend(value_int, expected_int_type, "zext")
                                        .map_err(|e| {
                                            anyhow::anyhow!("Failed to zero-extend: {}", e)
                                        })?
                                        .into();
                                } else if value_width > expected_width {
                                    // Truncate larger values
                                    value = self
                                        .builder()
                                        .build_int_truncate(value_int, expected_int_type, "trunc")
                                        .map_err(|e| anyhow::anyhow!("Failed to truncate: {}", e))?
                                        .into();
                                }
                            }
                        }
                    }

                    self.builder()
                        .build_store(ptr, value)
                        .map_err(|e| anyhow::anyhow!("Failed to build store: {}", e))?;
                }
            }
            Statement::Nop => {
                // No code generation needed for Nop
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
                let callee = self
                    .llvm_functions
                    .get(func)
                    .ok_or_else(|| anyhow::anyhow!("Function not found: {:?}", func))?;

                // Compile arguments
                let arg_values: Result<Vec<_>> =
                    args.iter().map(|arg| self.compile_operand(arg)).collect();
                let arg_values = arg_values?;

                // Convert BasicValueEnum to BasicMetadataValueEnum
                let args_metadata: Vec<_> = arg_values.into_iter().map(|v| v.into()).collect();

                // Call the function
                let call_site = self
                    .builder()
                    .build_call(*callee, &args_metadata, "call")
                    .map_err(|e| anyhow::anyhow!("Failed to build call: {}", e))?;

                // Get return value
                let return_value = call_site.try_as_basic_value().left()
                    .ok_or_else(|| {
                        anyhow::anyhow!(
                            "ICE: Function call to {:?} returned void, but MIR expects all \
                             function calls to produce a value. All functions should return at least Unit type.",
                            func
                        )
                    })?;

                Ok(return_value)
            }

            RValue::Intrinsic { intrinsic, args, type_args } => {
                self.compile_intrinsic(intrinsic, args, type_args)
            }

            RValue::Ref { place, .. } => {
                // Get the address of the place (place already evaluates to a pointer from get_place)
                // Since locals are allocated with build_alloca, get_place returns a pointer value
                let place_ptr = self.get_place(place)?;

                // The place is already a pointer (alloca returns pointer type)
                // For references, we just return this pointer directly
                if let BasicValueEnum::PointerValue(_) = place_ptr {
                    Ok(place_ptr)
                } else {
                    anyhow::bail!("Expected pointer value for reference, got: {:?}", place_ptr)
                }
            }

            RValue::Aggregate { kind, operands } => {
                match kind {
                    AggregateKind::Struct { .. } | AggregateKind::Tuple => {
                        // Create a struct/tuple aggregate with all fields
                        if operands.is_empty() {
                            // Empty struct/tuple - return empty LLVM struct
                            let empty_struct = self.context().struct_type(&[], false);
                            return Ok(empty_struct.const_zero().into());
                        }

                        // Compile all field values
                        let field_values: Result<Vec<BasicValueEnum>> =
                            operands.iter().map(|op| self.compile_operand(op)).collect();
                        let field_values = field_values?;

                        // Create struct type with the correct number of fields
                        let field_types: Vec<BasicTypeEnum> =
                            field_values.iter().map(|val| val.get_type()).collect();

                        let struct_type = self.context().struct_type(&field_types, false);
                        let mut aggregate_value = struct_type.get_undef();

                        // Insert each field value
                        for (i, field_val) in field_values.into_iter().enumerate() {
                            aggregate_value = self
                                .builder()
                                .build_insert_value(
                                    aggregate_value,
                                    field_val,
                                    i as u32,
                                    &format!("field_{}", i),
                                )
                                .map_err(|e| {
                                    anyhow::anyhow!("Failed to insert field {}: {}", i, e)
                                })?
                                .into_struct_value();
                        }

                        Ok(aggregate_value.into())
                    }
                    AggregateKind::Array(element_ty) => {
                        // Create an array aggregate
                        // Array size is determined by the number of operands
                        if operands.is_empty() {
                            // Empty array - use declared element type for zero-sized array
                            let llvm_elem_ty = self.type_lowering().lower_type(element_ty);
                            return Ok(llvm_elem_ty.array_type(0).const_zero().into());
                        }

                        // Compile all element values
                        let element_values: Result<Vec<BasicValueEnum>> =
                            operands.iter().map(|op| self.compile_operand(op)).collect();
                        let element_values = element_values?;

                        let array_size = element_values.len();

                        // Get element type from first element
                        let element_type = element_values[0].get_type();
                        let array_type = element_type.array_type(array_size as u32);
                        let mut array_value = array_type.get_undef();

                        // Insert each element
                        for (i, elem_val) in element_values.into_iter().enumerate() {
                            array_value = self
                                .builder()
                                .build_insert_value(
                                    array_value,
                                    elem_val,
                                    i as u32,
                                    &format!("elem_{}", i),
                                )
                                .map_err(|e| {
                                    anyhow::anyhow!("Failed to insert element {}: {}", i, e)
                                })?
                                .into_array_value();
                        }

                        Ok(array_value.into())
                    }
                    AggregateKind::Enum { variant_idx, .. } => {
                        // Enum aggregate: discriminant + variant fields
                        // Layout: { i32 discriminant, field0, field1, ... }
                        let discriminant = self
                            .context()
                            .i64_type()
                            .const_int(*variant_idx as u64, false);

                        let mut field_values: Vec<BasicValueEnum> = vec![discriminant.into()];
                        for op in operands {
                            field_values.push(self.compile_operand(op)?);
                        }

                        let field_types: Vec<BasicTypeEnum> =
                            field_values.iter().map(|val| val.get_type()).collect();

                        let struct_type = self.context().struct_type(&field_types, false);
                        let mut aggregate_value = struct_type.get_undef();

                        for (i, field_val) in field_values.into_iter().enumerate() {
                            aggregate_value = self
                                .builder()
                                .build_insert_value(
                                    aggregate_value,
                                    field_val,
                                    i as u32,
                                    &format!("enum_field_{}", i),
                                )
                                .map_err(|e| {
                                    anyhow::anyhow!("Failed to insert enum field {}: {}", i, e)
                                })?
                                .into_struct_value();
                        }

                        Ok(aggregate_value.into())
                    }
                }
            }
            RValue::Discriminant(place) => {
                // Extract the discriminant (field 0) from an enum aggregate
                let discr_place = Place {
                    local: place.local,
                    projection: vec![PlaceElem::Field { field_idx: 0 }],
                };
                let ptr = self.get_place(&discr_place)?;
                if let BasicValueEnum::PointerValue(ptr_val) = ptr {
                    let i64_type = self.context().i64_type();
                    Ok(self
                        .builder()
                        .build_load(i64_type, ptr_val, "discriminant")?
                        .into())
                } else {
                    anyhow::bail!("Discriminant place did not resolve to a pointer")
                }
            }
            RValue::Cast { operand, from, to } => {
                let val = self.compile_operand(operand)?;
                let to_llvm = self.type_lowering().lower_type(to);
                match (from, to) {
                    // Int → Float
                    (rv_lir::LirType::Int(..), rv_lir::LirType::Float(..)) => {
                        let int_val = val.into_int_value();
                        let float_val = self.builder().build_signed_int_to_float(
                            int_val,
                            to_llvm.into_float_type(),
                            "cast_int_to_float",
                        )?;
                        Ok(float_val.into())
                    }
                    // Float → Int (truncate)
                    (rv_lir::LirType::Float(..), rv_lir::LirType::Int(..)) => {
                        let float_val = val.into_float_value();
                        let int_val = self.builder().build_float_to_signed_int(
                            float_val,
                            to_llvm.into_int_type(),
                            "cast_float_to_int",
                        )?;
                        Ok(int_val.into())
                    }
                    // Bool → Int (already integer representation in LLVM)
                    (rv_lir::LirType::Bool, rv_lir::LirType::Int(..)) => Ok(val),
                    // Int → Bool (nonzero check)
                    (rv_lir::LirType::Int(..), rv_lir::LirType::Bool) => {
                        let int_val = val.into_int_value();
                        let zero = self.context().i64_type().const_zero();
                        let cmp = self.builder().build_int_compare(
                            inkwell::IntPredicate::NE,
                            int_val,
                            zero,
                            "cast_int_to_bool",
                        )?;
                        // Extend bool (i1) to i64 for our representation
                        let extended = self.builder().build_int_z_extend(
                            cmp,
                            self.context().i64_type(),
                            "bool_extend",
                        )?;
                        Ok(extended.into())
                    }
                    // Int → Pointer (int_to_ptr)
                    (rv_lir::LirType::Int(..), rv_lir::LirType::Pointer { .. }) => {
                        let int_val = val.into_int_value();
                        let ptr_val = self.builder().build_int_to_ptr(
                            int_val,
                            self.context().ptr_type(inkwell::AddressSpace::default()),
                            "cast_int_to_ptr",
                        )?;
                        Ok(ptr_val.into())
                    }
                    // Pointer → Int (ptr_to_int)
                    (rv_lir::LirType::Pointer { .. }, rv_lir::LirType::Int(..)) => {
                        let ptr_val = val.into_pointer_value();
                        let int_val = self.builder().build_ptr_to_int(
                            ptr_val,
                            to_llvm.into_int_type(),
                            "cast_ptr_to_int",
                        )?;
                        Ok(int_val.into())
                    }
                    // Ref → Pointer: no-op with opaque pointers
                    (rv_lir::LirType::Ref { .. }, rv_lir::LirType::Pointer { .. }) => Ok(val),
                    // Pointer → Pointer: no-op with opaque pointers
                    (rv_lir::LirType::Pointer { .. }, rv_lir::LirType::Pointer { .. }) => Ok(val),
                    // Pointer → Ref: no-op with opaque pointers
                    (rv_lir::LirType::Pointer { .. }, rv_lir::LirType::Ref { .. }) => Ok(val),
                    // Same type or unsupported: pass through
                    _ => Ok(val),
                }
            }
            RValue::VtableCall { .. } => {
                panic!(
                    "ICE: VtableCall not yet supported in LLVM backend. \
                     Trait object dynamic dispatch requires fat pointer infrastructure \
                     (data_ptr + vtable_ptr) which will be implemented in Tier 6."
                );
            }
            RValue::BoxNew { operand, inner_ty } => {
                // Box::new - allocate memory on the heap and store the value
                // For now, use alloca as a placeholder (proper malloc integration needed)
                let value = self.compile_operand(operand)?;
                let llvm_ty = self.type_lowering().lower_type(inner_ty);

                // Allocate space (using alloca for simplicity; real impl would use malloc)
                let alloca = self
                    .builder()
                    .build_alloca(llvm_ty, "box_alloc")
                    .map_err(|e| anyhow::anyhow!("Failed to build box alloca: {}", e))?;

                // Store the value
                self.builder()
                    .build_store(alloca, value)
                    .map_err(|e| anyhow::anyhow!("Failed to store box value: {}", e))?;

                Ok(alloca.into())
            }
            RValue::BoxFree { .. } => {
                // Box::drop - deallocate memory (no-op for alloca-based boxes)
                // Real impl would call free()
                Ok(self.context().i64_type().const_zero().into())
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
                    let llvm_type = self.type_lowering().lower_type(&place_ty);

                    // Load value from place
                    self.builder()
                        .build_load(llvm_type, ptr_val, "load")
                        .map_err(|e| anyhow::anyhow!("Failed to build load: {}", e))
                } else {
                    Ok(ptr)
                }
            }

            Operand::Constant(constant) => self.compile_constant(constant),
        }
    }

    /// Get the type of a place after applying all projections
    fn get_place_type(&self, place: &Place) -> Result<rv_lir::LirType> {
        use rv_lir::PlaceElem;

        // Start with the base local's type
        let local_info = self
            .mir_func
            .locals
            .iter()
            .find(|l| l.id == place.local)
            .ok_or_else(|| anyhow::anyhow!("Unknown local: {:?}", place.local))?;

        let mut current_type = local_info.ty.clone();

        // Apply projections to get the final type
        for projection in &place.projection {
            match projection {
                PlaceElem::Field { field_idx } => {
                    match &current_type {
                        rv_lir::LirType::Struct { fields, .. } => {
                            if let Some(field_type) = fields.get(*field_idx) {
                                current_type = field_type.clone();
                            } else {
                                anyhow::bail!("Field index out of bounds: {}", field_idx);
                            }
                        }
                        rv_lir::LirType::Enum { variants, .. } => {
                            // For enum variant field access, we need to find a variant that has
                            // a field at the given index. We search variants in order.
                            // This works because typically only one variant has fields at a given index
                            // (e.g., for Option<T>, only Some has field 0, None has no fields)
                            let mut found_type = None;
                            for variant in variants {
                                if let Some(field_type) = variant.fields.get(*field_idx) {
                                    found_type = Some(field_type.clone());
                                    break;
                                }
                            }
                            if let Some(ty) = found_type {
                                current_type = ty;
                            } else {
                                anyhow::bail!(
                                    "Field index {} not found in any enum variant",
                                    field_idx
                                );
                            }
                        }
                        rv_lir::LirType::Tuple(elements) => {
                            if let Some(field_type) = elements.get(*field_idx) {
                                current_type = field_type.clone();
                            } else {
                                anyhow::bail!("Tuple index out of bounds: {}", field_idx);
                            }
                        }
                        _ => {
                            anyhow::bail!(
                                "Cannot access field on non-struct/enum/tuple type: {:?}",
                                current_type
                            );
                        }
                    }
                }
                PlaceElem::Deref => {
                    // Dereference unwraps the reference/pointer type to get the inner type
                    match &current_type {
                        rv_lir::LirType::Ref { inner, .. }
                        | rv_lir::LirType::Pointer { inner, .. } => {
                            current_type = (**inner).clone();
                        }
                        _ => {
                            anyhow::bail!(
                                "Cannot dereference non-reference/pointer type: {:?}",
                                current_type
                            );
                        }
                    }
                }
                PlaceElem::Index(_) => {
                    if let rv_lir::LirType::Array { element, .. } = &current_type {
                        current_type = (**element).clone();
                    } else {
                        anyhow::bail!("Cannot index non-array type: {:?}", current_type);
                    }
                }
            }
        }

        Ok(current_type)
    }

    fn compile_constant(&self, constant: &Constant) -> Result<BasicValueEnum<'ctx>> {
        match &constant.kind {
            LiteralKind::Integer(val, _) => {
                // Use the type from the constant's ty field for proper width
                let llvm_ty = self.type_lowering().lower_type(&constant.ty);
                Ok(llvm_ty.into_int_type().const_int(*val as u64, false).into())
            }
            LiteralKind::Float(val, Some(rv_hir::FloatWidth::F32)) => {
                Ok(self.context().f32_type().const_float(*val).into())
            }
            LiteralKind::Float(val, _) => Ok(self.context().f64_type().const_float(*val).into()),
            LiteralKind::Char(c) => {
                Ok(self.context().i32_type().const_int(*c as u64, false).into())
            }
            LiteralKind::Bool(val) => Ok(self
                .context()
                .i64_type()
                .const_int(*val as u64, false)
                .into()),
            LiteralKind::String(s) => {
                // Create a global string constant and return a fat pointer { ptr, len }
                // This matches Rust's &'static str representation
                let global_string = self
                    .builder()
                    .build_global_string_ptr(s, "str")
                    .map_err(|e| anyhow::anyhow!("Failed to build global string: {}", e))?;
                let ptr = global_string.as_pointer_value();
                let len = self
                    .context()
                    .i64_type()
                    .const_int(s.len() as u64, false);

                // Create the fat pointer struct { ptr, len }
                let ptr_type = self.context().ptr_type(inkwell::AddressSpace::default());
                let len_type = self.context().i64_type();
                let str_struct_type =
                    self.context()
                        .struct_type(&[ptr_type.into(), len_type.into()], false);

                // Build the struct value
                let str_struct = str_struct_type.const_named_struct(&[ptr.into(), len.into()]);
                Ok(str_struct.into())
            }
            LiteralKind::Unit => Ok(self.context().i64_type().const_int(0, false).into()),
        }
    }

    fn compile_binary_op(
        &self,
        op: BinaryOp,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>> {
        // Dispatch based on whether operands are floats or integers
        if lhs.is_float_value() && rhs.is_float_value() {
            return self.compile_float_binary_op(op, lhs, rhs);
        }

        if !lhs.is_int_value() {
            anyhow::bail!("Left operand is not an integer or float: {:?}", lhs);
        }
        if !rhs.is_int_value() {
            anyhow::bail!("Right operand is not an integer or float: {:?}", rhs);
        }

        let lhs_int = lhs.into_int_value();
        let rhs_int = rhs.into_int_value();

        let result = match op {
            BinaryOp::Add => self.builder().build_int_add(lhs_int, rhs_int, "add"),
            BinaryOp::Sub => self.builder().build_int_sub(lhs_int, rhs_int, "sub"),
            BinaryOp::Mul => self.builder().build_int_mul(lhs_int, rhs_int, "mul"),
            BinaryOp::Div => self.builder().build_int_signed_div(lhs_int, rhs_int, "div"),
            BinaryOp::Mod => self.builder().build_int_signed_rem(lhs_int, rhs_int, "mod"),
            BinaryOp::Eq => {
                let cmp = self
                    .builder()
                    .build_int_compare(IntPredicate::EQ, lhs_int, rhs_int, "eq")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self
                    .builder()
                    .build_int_z_extend(cmp, self.context().i64_type(), "bool_to_i64")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Ne => {
                let cmp = self
                    .builder()
                    .build_int_compare(IntPredicate::NE, lhs_int, rhs_int, "ne")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self
                    .builder()
                    .build_int_z_extend(cmp, self.context().i64_type(), "bool_to_i64")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Lt => {
                let cmp = self
                    .builder()
                    .build_int_compare(IntPredicate::SLT, lhs_int, rhs_int, "lt")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self
                    .builder()
                    .build_int_z_extend(cmp, self.context().i64_type(), "bool_to_i64")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Le => {
                let cmp = self
                    .builder()
                    .build_int_compare(IntPredicate::SLE, lhs_int, rhs_int, "le")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self
                    .builder()
                    .build_int_z_extend(cmp, self.context().i64_type(), "bool_to_i64")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Gt => {
                let cmp = self
                    .builder()
                    .build_int_compare(IntPredicate::SGT, lhs_int, rhs_int, "gt")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self
                    .builder()
                    .build_int_z_extend(cmp, self.context().i64_type(), "bool_to_i64")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Ge => {
                let cmp = self
                    .builder()
                    .build_int_compare(IntPredicate::SGE, lhs_int, rhs_int, "ge")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self
                    .builder()
                    .build_int_z_extend(cmp, self.context().i64_type(), "bool_to_i64")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::And | BinaryOp::BitAnd => self.builder().build_and(lhs_int, rhs_int, "and"),
            BinaryOp::Or | BinaryOp::BitOr => self.builder().build_or(lhs_int, rhs_int, "or"),
            BinaryOp::BitXor => self.builder().build_xor(lhs_int, rhs_int, "xor"),
            BinaryOp::Shl => self.builder().build_left_shift(lhs_int, rhs_int, "shl"),
            BinaryOp::Shr => self
                .builder()
                .build_right_shift(lhs_int, rhs_int, false, "shr"),
        }
        .map_err(|e| anyhow::anyhow!("Failed to build binary op: {}", e))?;

        Ok(result.into())
    }

    fn compile_float_binary_op(
        &self,
        op: BinaryOp,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>> {
        use inkwell::FloatPredicate;

        let lhs_float = lhs.into_float_value();
        let rhs_float = rhs.into_float_value();

        match op {
            BinaryOp::Add => {
                let result = self
                    .builder()
                    .build_float_add(lhs_float, rhs_float, "fadd")
                    .map_err(|e| anyhow::anyhow!("Failed to build fadd: {}", e))?;
                Ok(result.into())
            }
            BinaryOp::Sub => {
                let result = self
                    .builder()
                    .build_float_sub(lhs_float, rhs_float, "fsub")
                    .map_err(|e| anyhow::anyhow!("Failed to build fsub: {}", e))?;
                Ok(result.into())
            }
            BinaryOp::Mul => {
                let result = self
                    .builder()
                    .build_float_mul(lhs_float, rhs_float, "fmul")
                    .map_err(|e| anyhow::anyhow!("Failed to build fmul: {}", e))?;
                Ok(result.into())
            }
            BinaryOp::Div => {
                let result = self
                    .builder()
                    .build_float_div(lhs_float, rhs_float, "fdiv")
                    .map_err(|e| anyhow::anyhow!("Failed to build fdiv: {}", e))?;
                Ok(result.into())
            }
            BinaryOp::Mod => {
                let result = self
                    .builder()
                    .build_float_rem(lhs_float, rhs_float, "fmod")
                    .map_err(|e| anyhow::anyhow!("Failed to build fmod: {}", e))?;
                Ok(result.into())
            }
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge => {
                let predicate = match op {
                    BinaryOp::Eq => FloatPredicate::OEQ,
                    BinaryOp::Ne => FloatPredicate::ONE,
                    BinaryOp::Lt => FloatPredicate::OLT,
                    BinaryOp::Le => FloatPredicate::OLE,
                    BinaryOp::Gt => FloatPredicate::OGT,
                    BinaryOp::Ge => FloatPredicate::OGE,
                    other => panic!(
                        "ICE: Non-comparison operator {:?} in float comparison codegen. \
                         Only Eq, Ne, Lt, Le, Gt, Ge should reach this match.",
                        other
                    ),
                };
                let cmp = self
                    .builder()
                    .build_float_compare(predicate, lhs_float, rhs_float, "fcmp")
                    .map_err(|e| anyhow::anyhow!("Failed to build float comparison: {}", e))?;
                let extended = self
                    .builder()
                    .build_int_z_extend(cmp, self.context().i64_type(), "bool_to_i64")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                Ok(extended.into())
            }
            _ => anyhow::bail!("Unsupported float binary op: {:?}", op),
        }
    }

    fn compile_unary_op(
        &self,
        op: UnaryOp,
        val: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>> {
        if val.is_float_value() {
            let val_float = val.into_float_value();
            match op {
                UnaryOp::Neg => {
                    let result = self
                        .builder()
                        .build_float_neg(val_float, "fneg")
                        .map_err(|e| anyhow::anyhow!("Failed to build float negation: {}", e))?;
                    return Ok(result.into());
                }
                UnaryOp::Not => {
                    anyhow::bail!("Cannot apply bitwise NOT to float value");
                }
            }
        }

        let val_int = val.into_int_value();

        let result = match op {
            UnaryOp::Neg => self
                .builder()
                .build_int_neg(val_int, "neg")
                .map_err(|e| anyhow::anyhow!("Failed to build negation: {}", e))?,
            UnaryOp::Not => self
                .builder()
                .build_not(val_int, "not")
                .map_err(|e| anyhow::anyhow!("Failed to build not: {}", e))?,
        };

        Ok(result.into())
    }

    fn compile_terminator(&mut self, terminator: &Terminator) -> Result<()> {
        match terminator {
            Terminator::Return { value, .. } => {
                if let Some(ret_val) = value {
                    let val = self.compile_operand(ret_val)?;

                    // Convert boolean (i1) to i64 if needed
                    let ret_val = if val.is_int_value()
                        && val.into_int_value().get_type().get_bit_width() == 1
                    {
                        // Zero-extend i1 to i64
                        self.builder()
                            .build_int_z_extend(
                                val.into_int_value(),
                                self.context().i64_type(),
                                "bool_to_i64",
                            )
                            .map_err(|e| anyhow::anyhow!("Failed to extend bool to i64: {}", e))?
                            .into()
                    } else {
                        val
                    };

                    self.builder()
                        .build_return(Some(&ret_val))
                        .map_err(|e| anyhow::anyhow!("Failed to build return: {}", e))?;
                } else {
                    // Return void/unit
                    let zero = self.context().i64_type().const_int(0, false);
                    self.builder()
                        .build_return(Some(&zero))
                        .map_err(|e| anyhow::anyhow!("Failed to build return: {}", e))?;
                }
            }

            Terminator::Goto { target } => {
                let target_bb = self.blocks.get(&target).ok_or_else(|| {
                    anyhow::anyhow!(
                        "ICE: Goto target block {} not found in LLVM block map. \
                         MIR must reference valid basic block IDs.",
                        target
                    )
                })?;
                self.builder()
                    .build_unconditional_branch(*target_bb)
                    .map_err(|e| anyhow::anyhow!("Failed to build branch: {}", e))?;
            }

            Terminator::SwitchInt {
                discriminant,
                targets,
                otherwise,
                ..
            } => {
                // Compile the discriminant value
                let discr_val = self.compile_operand(discriminant)?;

                let discr_int = if discr_val.is_int_value() {
                    discr_val.into_int_value()
                } else {
                    anyhow::bail!(
                        "ICE: SwitchInt discriminant is not an integer value: {:?}",
                        discr_val
                    );
                };

                let else_bb = self
                    .blocks
                    .get(otherwise)
                    .ok_or_else(|| anyhow::anyhow!("Otherwise block not found"))?;

                if targets.len() == 1 && targets.contains_key(&1) {
                    // Optimized path for boolean if/else: compare != 0
                    let then_bb = self
                        .blocks
                        .get(&targets[&1])
                        .ok_or_else(|| anyhow::anyhow!("Target block not found"))?;

                    let zero = discr_int.get_type().const_int(0, false);
                    let condition = self
                        .builder()
                        .build_int_compare(IntPredicate::NE, discr_int, zero, "switchcond")
                        .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;

                    self.builder()
                        .build_conditional_branch(condition, *then_bb, *else_bb)
                        .map_err(|e| {
                            anyhow::anyhow!("Failed to build conditional branch: {}", e)
                        })?;
                } else {
                    // General multi-way switch using LLVM switch instruction
                    let cases: Vec<_> = targets
                        .iter()
                        .map(|(val, bb_id)| {
                            let target_bb = self.blocks[bb_id];
                            let case_val = discr_int.get_type().const_int(*val as u64, true);
                            (case_val, target_bb)
                        })
                        .collect();

                    self.builder()
                        .build_switch(discr_int, *else_bb, &cases)
                        .map_err(|e| anyhow::anyhow!("Failed to build switch: {}", e))?;
                }
            }

            Terminator::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                // Get the LLVM function
                let callee = self
                    .llvm_functions
                    .get(func)
                    .ok_or_else(|| anyhow::anyhow!("Function not found: {:?}", func))?;

                // Compile arguments
                let arg_values: Result<Vec<_>> =
                    args.iter().map(|arg| self.compile_operand(arg)).collect();
                let args_metadata: Vec<_> = arg_values?.into_iter().map(|v| v.into()).collect();

                // Call the function
                let call_site = self
                    .builder()
                    .build_call(*callee, &args_metadata, "call")
                    .map_err(|e| anyhow::anyhow!("Failed to build call: {}", e))?;

                // Store the return value to the destination place
                if let Some(return_value) = call_site.try_as_basic_value().left() {
                    let dest = self.get_place(destination)?;
                    if let BasicValueEnum::PointerValue(ptr) = dest {
                        self.builder()
                            .build_store(ptr, return_value)
                            .map_err(|e| anyhow::anyhow!("Failed to store call result: {}", e))?;
                    }
                }

                // Branch to the continuation block
                if let Some(target_bb_id) = target {
                    if let Some(target_bb) = self.blocks.get(target_bb_id) {
                        self.builder()
                            .build_unconditional_branch(*target_bb)
                            .map_err(|e| {
                                anyhow::anyhow!("Failed to build branch after call: {}", e)
                            })?;
                    }
                }
            }

            Terminator::Drop { place, target, .. } => {
                // Check if the type being dropped is a Box
                // For Box<T> allocated with alloca, no explicit deallocation needed
                // (the stack memory is automatically freed when the function returns)
                if let Some(local_ty) = self.mir_func.get_local_type(place.local) {
                    if matches!(local_ty, rv_lir::LirType::Box { .. }) {
                        // Box drop: No-op for alloca-based boxes
                        // If we implement proper heap allocation (malloc), we would
                        // call free() here
                    }
                }
                // TODO(tier4): Emit call to Drop::drop if the type implements Drop.
                // For now, just branch to the continuation block.
                let target_bb = self.blocks.get(&target).ok_or_else(|| {
                    anyhow::anyhow!(
                        "ICE: Drop target block {} not found in LLVM block map.",
                        target
                    )
                })?;
                self.builder()
                    .build_unconditional_branch(*target_bb)
                    .map_err(|e| anyhow::anyhow!("Failed to build branch after drop: {}", e))?;
            }

            Terminator::Unreachable => {
                self.builder()
                    .build_unreachable()
                    .map_err(|e| anyhow::anyhow!("Failed to build unreachable: {}", e))?;
            }

            Terminator::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                let cond_val = self.compile_operand(cond)?;

                // Ensure we have an i1 value for the condition
                let cond_i1 = if cond_val.is_int_value() {
                    let int_val = cond_val.into_int_value();
                    if int_val.get_type().get_bit_width() == 1 {
                        int_val
                    } else {
                        // Compare with zero to get boolean
                        let zero = int_val.get_type().const_int(0, false);
                        self.builder()
                            .build_int_compare(
                                inkwell::IntPredicate::NE,
                                int_val,
                                zero,
                                "cond_bool",
                            )
                            .map_err(|e| anyhow::anyhow!("Failed to build condition compare: {}", e))?
                    }
                } else {
                    anyhow::bail!("Assert condition must be an integer value");
                };

                let target_bb = self.blocks.get(&target).ok_or_else(|| {
                    anyhow::anyhow!("Assert target block {} not found", target)
                })?;

                // Create a trap block for assertion failure
                let trap_bb = self.context().append_basic_block(
                    self.builder().get_insert_block().unwrap().get_parent().unwrap(),
                    "assert_trap",
                );

                if *expected {
                    // Expected true: branch to target if true, trap if false
                    self.builder()
                        .build_conditional_branch(cond_i1, *target_bb, trap_bb)
                        .map_err(|e| anyhow::anyhow!("Failed to build conditional branch: {}", e))?;
                } else {
                    // Expected false: branch to target if false, trap if true
                    self.builder()
                        .build_conditional_branch(cond_i1, trap_bb, *target_bb)
                        .map_err(|e| anyhow::anyhow!("Failed to build conditional branch: {}", e))?;
                }

                // Emit trap block - call llvm.trap intrinsic
                self.builder().position_at_end(trap_bb);
                let trap_intrinsic_id =
                    inkwell::intrinsics::Intrinsic::find("llvm.trap").ok_or_else(|| {
                        anyhow::anyhow!("Failed to find llvm.trap intrinsic")
                    })?;
                let trap_fn = trap_intrinsic_id
                    .get_declaration(&self.compiler.module, &[])
                    .ok_or_else(|| anyhow::anyhow!("Failed to get llvm.trap declaration"))?;
                self.builder()
                    .build_call(trap_fn, &[], "trap_call")
                    .map_err(|e| anyhow::anyhow!("Failed to build trap call: {}", e))?;
                self.builder()
                    .build_unreachable()
                    .map_err(|e| anyhow::anyhow!("Failed to build unreachable after trap: {}", e))?;
            }
        }

        Ok(())
    }

    fn get_place(&self, place: &Place) -> Result<BasicValueEnum<'ctx>> {
        use rv_lir::PlaceElem;

        // Get the base local
        if let Some(mut local_val) = self.locals.get(&place.local).copied() {
            // Get the type of the base local for tracking through projections
            let local_info = self
                .mir_func
                .locals
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
                            let basic_type = self.type_lowering().lower_type(current_type);

                            // Extract the actual struct type from BasicTypeEnum
                            if let BasicTypeEnum::StructType(struct_type) = basic_type {
                                // GEP with struct_gep for type-safe field access
                                let field_ptr = self
                                    .builder()
                                    .build_struct_gep(
                                        struct_type,
                                        ptr_val,
                                        *field_idx as u32,
                                        "field_ptr",
                                    )
                                    .map_err(|e| {
                                        anyhow::anyhow!("Failed to build struct GEP: {}", e)
                                    })?;

                                local_val = field_ptr.into();

                                // Update current_type to the field's type
                                if let rv_lir::LirType::Struct { fields, .. } = current_type {
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
                        // Dereference: load the pointer value, then use it as the new pointer
                        if let BasicValueEnum::PointerValue(ptr_val) = local_val {
                            // Get the type we're dereferencing from
                            match current_type {
                                rv_lir::LirType::Ref { inner, .. }
                                | rv_lir::LirType::Pointer { inner, .. } => {
                                    // Load the pointer stored at ptr_val (double indirection)
                                    let llvm_ptr_type =
                                        self.type_lowering().lower_type(current_type);
                                    let loaded_ptr = self
                                        .builder()
                                        .build_load(llvm_ptr_type, ptr_val, "deref_load")
                                        .map_err(|e| {
                                            anyhow::anyhow!(
                                                "Failed to load pointer for deref: {}",
                                                e
                                            )
                                        })?;

                                    // The loaded value should be a pointer to the inner type
                                    local_val = loaded_ptr;
                                    current_type = inner;
                                }
                                _ => {
                                    anyhow::bail!(
                                        "Cannot dereference non-reference/pointer type: {:?}",
                                        current_type
                                    );
                                }
                            }
                        } else {
                            anyhow::bail!("Cannot dereference non-pointer value");
                        }
                    }
                    PlaceElem::Index(index_local) => {
                        // Array indexing: arr[idx]
                        if let BasicValueEnum::PointerValue(ptr_val) = local_val {
                            let basic_type = self.type_lowering().lower_type(current_type);

                            if let BasicTypeEnum::ArrayType(array_type) = basic_type {
                                // Get the index value from the index local
                                let index_val =
                                    if let Some(idx_alloca) = self.locals.get(index_local) {
                                        if let BasicValueEnum::PointerValue(idx_ptr) = idx_alloca {
                                            self.builder()
                                                .build_load(
                                                    self.context().i64_type(),
                                                    *idx_ptr,
                                                    "load_idx",
                                                )
                                                .map_err(|e| {
                                                    anyhow::anyhow!("Failed to load index: {}", e)
                                                })?
                                                .into_int_value()
                                        } else {
                                            anyhow::bail!("Index local is not a pointer");
                                        }
                                    } else {
                                        anyhow::bail!("Index local {:?} not found", index_local);
                                    };

                                // GEP into the array: pointer to element
                                let zero = self.context().i64_type().const_int(0, false);
                                let element_ptr = unsafe {
                                    self.builder()
                                        .build_in_bounds_gep(
                                            array_type,
                                            ptr_val,
                                            &[zero, index_val],
                                            "array_idx",
                                        )
                                        .map_err(|e| {
                                            anyhow::anyhow!("Failed to build array GEP: {}", e)
                                        })?
                                };

                                local_val = element_ptr.into();

                                // Update type to element type
                                if let rv_lir::LirType::Array { element, .. } = current_type {
                                    current_type = element;
                                }
                            } else {
                                anyhow::bail!(
                                    "Expected array type for index access but got {:?}",
                                    basic_type
                                );
                            }
                        } else {
                            anyhow::bail!("Cannot index non-pointer value");
                        }
                    }
                }
            }
            Ok(local_val)
        } else {
            anyhow::bail!("Unknown local: {:?}", place.local)
        }
    }

    /// Compile an intrinsic call to LLVM IR
    fn compile_intrinsic(
        &mut self,
        intrinsic: &rv_mir::Intrinsic,
        args: &[Operand],
        type_args: &[rv_lir::LirType],
    ) -> Result<BasicValueEnum<'ctx>> {
        // Since rv_mir::Intrinsic has a Symbol name, we need to convert it to a string
        // for matching. The Symbol is an opaque ID, so we use Debug format.
        let name_debug = format!("{:?}", intrinsic.name);

        // Helper to get an argument value
        let mut get_arg = |idx: usize| -> Result<BasicValueEnum<'ctx>> {
            args.get(idx)
                .ok_or_else(|| anyhow::anyhow!("Intrinsic missing argument {}", idx))
                .and_then(|arg| self.compile_operand(arg))
        };

        // Match on intrinsic name patterns
        match name_debug.as_str() {
            // Memory intrinsics
            s if s.contains("size_of") && !s.contains("val") => {
                let size = type_args.first().map(Self::calculate_size_of).unwrap_or(8);
                Ok(self.context().i64_type().const_int(size as u64, false).into())
            }
            s if s.contains("size_of_val") => {
                // For sized types, return compile-time size
                let size = type_args.first().map(Self::calculate_size_of).unwrap_or(8);
                Ok(self.context().i64_type().const_int(size as u64, false).into())
            }
            s if s.contains("align_of") && !s.contains("val") => {
                let align = type_args.first().map(Self::calculate_align_of).unwrap_or(8);
                Ok(self.context().i64_type().const_int(align as u64, false).into())
            }
            s if s.contains("align_of_val") => {
                let align = type_args.first().map(Self::calculate_align_of).unwrap_or(8);
                Ok(self.context().i64_type().const_int(align as u64, false).into())
            }
            s if s.contains("transmute") => {
                // Transmute: bitcast the value to the target type
                let val = get_arg(0)?;
                if type_args.len() >= 2 {
                    let to_type = self.type_lowering().lower_type(&type_args[1]);
                    // For same-size types, use bitcast
                    if val.is_int_value() && matches!(to_type, BasicTypeEnum::IntType(_)) {
                        let int_val = val.into_int_value();
                        let to_int = to_type.into_int_type();
                        if int_val.get_type().get_bit_width() == to_int.get_bit_width() {
                            return Ok(int_val.into());
                        }
                    }
                }
                Ok(val)
            }
            s if s.contains("needs_drop") => {
                let needs = type_args.first().map(Self::type_needs_drop).unwrap_or(false);
                Ok(self.context().i64_type().const_int(needs as u64, false).into())
            }
            s if s.contains("forget") => {
                // forget: do nothing (prevent drop)
                Ok(self.context().i64_type().const_zero().into())
            }
            s if s.contains("copy_nonoverlapping") || s.contains("copy") && !s.contains("_copy") => {
                // copy/copy_nonoverlapping: src, dst, count
                // Use LLVM memcpy intrinsic
                let size = type_args.first().map(Self::calculate_size_of).unwrap_or(8);
                let src = get_arg(0)?;
                let dst = get_arg(1)?;
                let count = get_arg(2)?;

                if let (BasicValueEnum::PointerValue(src_ptr), BasicValueEnum::PointerValue(dst_ptr)) = (src, dst) {
                    let count_val = count.into_int_value();
                    let size_const = self.context().i64_type().const_int(size as u64, false);
                    let total_size = self.builder().build_int_mul(count_val, size_const, "total_size")?;

                    // Use memcpy intrinsic
                    let i8_type = self.context().i8_type();
                    let ptr_type = self.context().ptr_type(inkwell::AddressSpace::default());
                    let memcpy_type = self.context().void_type().fn_type(
                        &[ptr_type.into(), ptr_type.into(), self.context().i64_type().into(), self.context().bool_type().into()],
                        false,
                    );
                    let memcpy = self.compiler.module.add_function("llvm.memcpy.p0.p0.i64", memcpy_type, None);
                    let is_volatile = self.context().bool_type().const_int(0, false);
                    self.builder().build_call(memcpy, &[dst_ptr.into(), src_ptr.into(), total_size.into(), is_volatile.into()], "")?;
                }
                Ok(self.context().i64_type().const_zero().into())
            }
            s if s.contains("write_bytes") => {
                // write_bytes: dst, byte, count
                let dst = get_arg(0)?;
                let byte = get_arg(1)?;
                let count = get_arg(2)?;

                if let BasicValueEnum::PointerValue(dst_ptr) = dst {
                    let size = type_args.first().map(Self::calculate_size_of).unwrap_or(1);
                    let count_val = count.into_int_value();
                    let size_const = self.context().i64_type().const_int(size as u64, false);
                    let total_size = self.builder().build_int_mul(count_val, size_const, "total_size")?;

                    let ptr_type = self.context().ptr_type(inkwell::AddressSpace::default());
                    let memset_type = self.context().void_type().fn_type(
                        &[ptr_type.into(), self.context().i8_type().into(), self.context().i64_type().into(), self.context().bool_type().into()],
                        false,
                    );
                    let memset = self.compiler.module.add_function("llvm.memset.p0.i64", memset_type, None);
                    let byte_val = if byte.is_int_value() {
                        self.builder().build_int_truncate(byte.into_int_value(), self.context().i8_type(), "byte")?
                    } else {
                        self.context().i8_type().const_zero()
                    };
                    let is_volatile = self.context().bool_type().const_int(0, false);
                    self.builder().build_call(memset, &[dst_ptr.into(), byte_val.into(), total_size.into(), is_volatile.into()], "")?;
                }
                Ok(self.context().i64_type().const_zero().into())
            }

            // Arithmetic intrinsics - overflow operations
            s if s.contains("add_with_overflow") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                // Return (result, overflowed) tuple
                // Use LLVM's sadd.with.overflow intrinsic
                let int_type = lhs.get_type();
                let result = self.builder().build_int_add(lhs, rhs, "add")?;
                // Simplified overflow check (signed)
                let overflow = self.context().i64_type().const_int(0, false);
                // Create tuple struct
                let struct_type = self.context().struct_type(&[int_type.into(), self.context().i64_type().into()], false);
                let mut aggregate = struct_type.get_undef();
                aggregate = self.builder().build_insert_value(aggregate, result, 0, "res")?.into_struct_value();
                aggregate = self.builder().build_insert_value(aggregate, overflow, 1, "ovf")?.into_struct_value();
                Ok(aggregate.into())
            }
            s if s.contains("sub_with_overflow") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                let int_type = lhs.get_type();
                let result = self.builder().build_int_sub(lhs, rhs, "sub")?;
                let overflow = self.context().i64_type().const_int(0, false);
                let struct_type = self.context().struct_type(&[int_type.into(), self.context().i64_type().into()], false);
                let mut aggregate = struct_type.get_undef();
                aggregate = self.builder().build_insert_value(aggregate, result, 0, "res")?.into_struct_value();
                aggregate = self.builder().build_insert_value(aggregate, overflow, 1, "ovf")?.into_struct_value();
                Ok(aggregate.into())
            }
            s if s.contains("mul_with_overflow") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                let int_type = lhs.get_type();
                let result = self.builder().build_int_mul(lhs, rhs, "mul")?;
                let overflow = self.context().i64_type().const_int(0, false);
                let struct_type = self.context().struct_type(&[int_type.into(), self.context().i64_type().into()], false);
                let mut aggregate = struct_type.get_undef();
                aggregate = self.builder().build_insert_value(aggregate, result, 0, "res")?.into_struct_value();
                aggregate = self.builder().build_insert_value(aggregate, overflow, 1, "ovf")?.into_struct_value();
                Ok(aggregate.into())
            }

            // Wrapping arithmetic
            s if s.contains("wrapping_add") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                Ok(self.builder().build_int_add(lhs, rhs, "wrapping_add")?.into())
            }
            s if s.contains("wrapping_sub") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                Ok(self.builder().build_int_sub(lhs, rhs, "wrapping_sub")?.into())
            }
            s if s.contains("wrapping_mul") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                Ok(self.builder().build_int_mul(lhs, rhs, "wrapping_mul")?.into())
            }

            // Saturating arithmetic
            s if s.contains("saturating_add") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                // Simplified: just use regular add
                Ok(self.builder().build_int_add(lhs, rhs, "saturating_add")?.into())
            }
            s if s.contains("saturating_sub") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                Ok(self.builder().build_int_sub(lhs, rhs, "saturating_sub")?.into())
            }

            // Unchecked arithmetic
            s if s.contains("unchecked_add") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                Ok(self.builder().build_int_add(lhs, rhs, "unchecked_add")?.into())
            }
            s if s.contains("unchecked_sub") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                Ok(self.builder().build_int_sub(lhs, rhs, "unchecked_sub")?.into())
            }
            s if s.contains("unchecked_mul") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                Ok(self.builder().build_int_mul(lhs, rhs, "unchecked_mul")?.into())
            }
            s if s.contains("unchecked_div") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                Ok(self.builder().build_int_signed_div(lhs, rhs, "unchecked_div")?.into())
            }
            s if s.contains("exact_div") => {
                let lhs = get_arg(0)?.into_int_value();
                let rhs = get_arg(1)?.into_int_value();
                Ok(self.builder().build_int_signed_div(lhs, rhs, "exact_div")?.into())
            }

            // Bit manipulation
            s if s.contains("rotate_left") => {
                let val = get_arg(0)?.into_int_value();
                let amt = get_arg(1)?.into_int_value();
                let bits = val.get_type().get_bit_width();
                let bits_const = val.get_type().const_int(bits as u64, false);
                let mask = self.builder().build_int_sub(bits_const, amt, "mask")?;
                let left = self.builder().build_left_shift(val, amt, "left")?;
                let right = self.builder().build_right_shift(val, mask, false, "right")?;
                Ok(self.builder().build_or(left, right, "rotl")?.into())
            }
            s if s.contains("rotate_right") => {
                let val = get_arg(0)?.into_int_value();
                let amt = get_arg(1)?.into_int_value();
                let bits = val.get_type().get_bit_width();
                let bits_const = val.get_type().const_int(bits as u64, false);
                let mask = self.builder().build_int_sub(bits_const, amt, "mask")?;
                let right = self.builder().build_right_shift(val, amt, false, "right")?;
                let left = self.builder().build_left_shift(val, mask, "left")?;
                Ok(self.builder().build_or(left, right, "rotr")?.into())
            }
            s if s.contains("ctlz") => {
                // Count leading zeros - use LLVM ctlz intrinsic
                let val = get_arg(0)?.into_int_value();
                let int_type = val.get_type();
                let ctlz_type = int_type.fn_type(&[int_type.into(), self.context().bool_type().into()], false);
                let fn_name = format!("llvm.ctlz.i{}", int_type.get_bit_width());
                let ctlz = self.compiler.module.add_function(&fn_name, ctlz_type, None);
                let is_zero_undef = self.context().bool_type().const_int(0, false);
                let result = self.builder().build_call(ctlz, &[val.into(), is_zero_undef.into()], "ctlz")?;
                Ok(result.try_as_basic_value().left().unwrap_or_else(|| self.context().i64_type().const_zero().into()))
            }
            s if s.contains("cttz") => {
                // Count trailing zeros
                let val = get_arg(0)?.into_int_value();
                let int_type = val.get_type();
                let cttz_type = int_type.fn_type(&[int_type.into(), self.context().bool_type().into()], false);
                let fn_name = format!("llvm.cttz.i{}", int_type.get_bit_width());
                let cttz = self.compiler.module.add_function(&fn_name, cttz_type, None);
                let is_zero_undef = self.context().bool_type().const_int(0, false);
                let result = self.builder().build_call(cttz, &[val.into(), is_zero_undef.into()], "cttz")?;
                Ok(result.try_as_basic_value().left().unwrap_or_else(|| self.context().i64_type().const_zero().into()))
            }
            s if s.contains("ctpop") => {
                // Population count (number of 1 bits)
                let val = get_arg(0)?.into_int_value();
                let int_type = val.get_type();
                let ctpop_type = int_type.fn_type(&[int_type.into()], false);
                let fn_name = format!("llvm.ctpop.i{}", int_type.get_bit_width());
                let ctpop = self.compiler.module.add_function(&fn_name, ctpop_type, None);
                let result = self.builder().build_call(ctpop, &[val.into()], "ctpop")?;
                Ok(result.try_as_basic_value().left().unwrap_or_else(|| self.context().i64_type().const_zero().into()))
            }
            s if s.contains("bitreverse") => {
                let val = get_arg(0)?.into_int_value();
                let int_type = val.get_type();
                let bitrev_type = int_type.fn_type(&[int_type.into()], false);
                let fn_name = format!("llvm.bitreverse.i{}", int_type.get_bit_width());
                let bitrev = self.compiler.module.add_function(&fn_name, bitrev_type, None);
                let result = self.builder().build_call(bitrev, &[val.into()], "bitrev")?;
                Ok(result.try_as_basic_value().left().unwrap_or_else(|| self.context().i64_type().const_zero().into()))
            }
            s if s.contains("bswap") => {
                let val = get_arg(0)?.into_int_value();
                let int_type = val.get_type();
                let bswap_type = int_type.fn_type(&[int_type.into()], false);
                let fn_name = format!("llvm.bswap.i{}", int_type.get_bit_width());
                let bswap = self.compiler.module.add_function(&fn_name, bswap_type, None);
                let result = self.builder().build_call(bswap, &[val.into()], "bswap")?;
                Ok(result.try_as_basic_value().left().unwrap_or_else(|| self.context().i64_type().const_zero().into()))
            }

            // Float intrinsics
            s if s.contains("sqrtf32") => {
                let val = get_arg(0)?.into_float_value();
                let sqrt_type = self.context().f32_type().fn_type(&[self.context().f32_type().into()], false);
                let sqrt = self.compiler.module.add_function("llvm.sqrt.f32", sqrt_type, None);
                let result = self.builder().build_call(sqrt, &[val.into()], "sqrt")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("sqrtf64") => {
                let val = get_arg(0)?.into_float_value();
                let sqrt_type = self.context().f64_type().fn_type(&[self.context().f64_type().into()], false);
                let sqrt = self.compiler.module.add_function("llvm.sqrt.f64", sqrt_type, None);
                let result = self.builder().build_call(sqrt, &[val.into()], "sqrt")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("sinf32") => {
                let val = get_arg(0)?.into_float_value();
                let sin_type = self.context().f32_type().fn_type(&[self.context().f32_type().into()], false);
                let sin = self.compiler.module.add_function("llvm.sin.f32", sin_type, None);
                let result = self.builder().build_call(sin, &[val.into()], "sin")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("sinf64") => {
                let val = get_arg(0)?.into_float_value();
                let sin_type = self.context().f64_type().fn_type(&[self.context().f64_type().into()], false);
                let sin = self.compiler.module.add_function("llvm.sin.f64", sin_type, None);
                let result = self.builder().build_call(sin, &[val.into()], "sin")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("cosf32") => {
                let val = get_arg(0)?.into_float_value();
                let cos_type = self.context().f32_type().fn_type(&[self.context().f32_type().into()], false);
                let cos = self.compiler.module.add_function("llvm.cos.f32", cos_type, None);
                let result = self.builder().build_call(cos, &[val.into()], "cos")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("cosf64") => {
                let val = get_arg(0)?.into_float_value();
                let cos_type = self.context().f64_type().fn_type(&[self.context().f64_type().into()], false);
                let cos = self.compiler.module.add_function("llvm.cos.f64", cos_type, None);
                let result = self.builder().build_call(cos, &[val.into()], "cos")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("floorf32") => {
                let val = get_arg(0)?.into_float_value();
                let floor_type = self.context().f32_type().fn_type(&[self.context().f32_type().into()], false);
                let floor = self.compiler.module.add_function("llvm.floor.f32", floor_type, None);
                let result = self.builder().build_call(floor, &[val.into()], "floor")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("floorf64") => {
                let val = get_arg(0)?.into_float_value();
                let floor_type = self.context().f64_type().fn_type(&[self.context().f64_type().into()], false);
                let floor = self.compiler.module.add_function("llvm.floor.f64", floor_type, None);
                let result = self.builder().build_call(floor, &[val.into()], "floor")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("ceilf32") => {
                let val = get_arg(0)?.into_float_value();
                let ceil_type = self.context().f32_type().fn_type(&[self.context().f32_type().into()], false);
                let ceil = self.compiler.module.add_function("llvm.ceil.f32", ceil_type, None);
                let result = self.builder().build_call(ceil, &[val.into()], "ceil")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("ceilf64") => {
                let val = get_arg(0)?.into_float_value();
                let ceil_type = self.context().f64_type().fn_type(&[self.context().f64_type().into()], false);
                let ceil = self.compiler.module.add_function("llvm.ceil.f64", ceil_type, None);
                let result = self.builder().build_call(ceil, &[val.into()], "ceil")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("fmaf32") => {
                let a = get_arg(0)?.into_float_value();
                let b = get_arg(1)?.into_float_value();
                let c = get_arg(2)?.into_float_value();
                let fma_type = self.context().f32_type().fn_type(
                    &[self.context().f32_type().into(), self.context().f32_type().into(), self.context().f32_type().into()],
                    false,
                );
                let fma = self.compiler.module.add_function("llvm.fma.f32", fma_type, None);
                let result = self.builder().build_call(fma, &[a.into(), b.into(), c.into()], "fma")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }
            s if s.contains("fmaf64") => {
                let a = get_arg(0)?.into_float_value();
                let b = get_arg(1)?.into_float_value();
                let c = get_arg(2)?.into_float_value();
                let fma_type = self.context().f64_type().fn_type(
                    &[self.context().f64_type().into(), self.context().f64_type().into(), self.context().f64_type().into()],
                    false,
                );
                let fma = self.compiler.module.add_function("llvm.fma.f64", fma_type, None);
                let result = self.builder().build_call(fma, &[a.into(), b.into(), c.into()], "fma")?;
                Ok(result.try_as_basic_value().left().unwrap())
            }

            // Control intrinsics
            s if s.contains("unreachable") => {
                self.builder().build_unreachable()?;
                // After unreachable, we need to return something (even though it won't be used)
                Ok(self.context().i64_type().const_zero().into())
            }
            s if s.contains("assume") => {
                // assume: hint to optimizer that condition is true
                let cond = get_arg(0)?;
                if cond.is_int_value() {
                    let assume_type = self.context().void_type().fn_type(&[self.context().bool_type().into()], false);
                    let assume = self.compiler.module.add_function("llvm.assume", assume_type, None);
                    let cond_i1 = if cond.into_int_value().get_type().get_bit_width() > 1 {
                        self.builder().build_int_truncate(cond.into_int_value(), self.context().bool_type(), "cond")?
                    } else {
                        cond.into_int_value()
                    };
                    self.builder().build_call(assume, &[cond_i1.into()], "")?;
                }
                Ok(self.context().i64_type().const_zero().into())
            }
            s if s.contains("abort") => {
                let abort_type = self.context().void_type().fn_type(&[], false);
                let abort = self.compiler.module.add_function("abort", abort_type, None);
                self.builder().build_call(abort, &[], "")?;
                self.builder().build_unreachable()?;
                Ok(self.context().i64_type().const_zero().into())
            }
            s if s.contains("type_id") => {
                // Return a hash of the type
                let hash = type_args.first().map(Self::type_hash).unwrap_or(0);
                Ok(self.context().i64_type().const_int(hash, false).into())
            }
            s if s.contains("type_name") => {
                // Return a pointer to a static string with the type name
                let name = type_args.first().map(Self::type_name).unwrap_or_else(|| "unknown".to_string());
                let global_string = self.builder().build_global_string_ptr(&name, "type_name")?;
                Ok(global_string.as_pointer_value().into())
            }

            // Pointer intrinsics
            s if s.contains("offset") || s.contains("arith_offset") => {
                let ptr = get_arg(0)?;
                let offset = get_arg(1)?.into_int_value();
                if let BasicValueEnum::PointerValue(ptr_val) = ptr {
                    let elem_size = type_args.first().map(Self::calculate_size_of).unwrap_or(1);
                    let size_const = self.context().i64_type().const_int(elem_size as u64, false);
                    let byte_offset = self.builder().build_int_mul(offset, size_const, "byte_offset")?;
                    let ptr_int = self.builder().build_ptr_to_int(ptr_val, self.context().i64_type(), "ptr_int")?;
                    let new_ptr_int = self.builder().build_int_add(ptr_int, byte_offset, "new_ptr_int")?;
                    let new_ptr = self.builder().build_int_to_ptr(new_ptr_int, self.context().ptr_type(inkwell::AddressSpace::default()), "new_ptr")?;
                    Ok(new_ptr.into())
                } else {
                    anyhow::bail!("offset intrinsic requires pointer argument")
                }
            }
            s if s.contains("ptr_offset_from") => {
                let ptr1 = get_arg(0)?;
                let ptr2 = get_arg(1)?;
                if let (BasicValueEnum::PointerValue(p1), BasicValueEnum::PointerValue(p2)) = (ptr1, ptr2) {
                    let elem_size = type_args.first().map(Self::calculate_size_of).unwrap_or(1);
                    let p1_int = self.builder().build_ptr_to_int(p1, self.context().i64_type(), "p1_int")?;
                    let p2_int = self.builder().build_ptr_to_int(p2, self.context().i64_type(), "p2_int")?;
                    let diff = self.builder().build_int_sub(p1_int, p2_int, "diff")?;
                    let size_const = self.context().i64_type().const_int(elem_size as u64, false);
                    let elem_diff = self.builder().build_int_signed_div(diff, size_const, "elem_diff")?;
                    Ok(elem_diff.into())
                } else {
                    Ok(self.context().i64_type().const_zero().into())
                }
            }
            s if s.contains("raw_eq") => {
                // Bitwise equality comparison
                let a = get_arg(0)?;
                let b = get_arg(1)?;
                if a.is_int_value() && b.is_int_value() {
                    let cmp = self.builder().build_int_compare(IntPredicate::EQ, a.into_int_value(), b.into_int_value(), "raw_eq")?;
                    let extended = self.builder().build_int_z_extend(cmp, self.context().i64_type(), "eq_i64")?;
                    Ok(extended.into())
                } else {
                    Ok(self.context().i64_type().const_int(0, false).into())
                }
            }
            s if s.contains("volatile_load") => {
                let ptr = get_arg(0)?;
                if let BasicValueEnum::PointerValue(ptr_val) = ptr {
                    let ty = type_args.first().map(|t| self.type_lowering().lower_type(t)).unwrap_or_else(|| self.context().i64_type().into());
                    let load = self.builder().build_load(ty, ptr_val, "volatile_load")?;
                    // Mark as volatile
                    if let BasicValueEnum::IntValue(int_val) = load {
                        // Unfortunately inkwell doesn't have a direct volatile flag setter for loads
                        // The load is done but not marked volatile in this simplified impl
                        return Ok(int_val.into());
                    }
                    Ok(load)
                } else {
                    anyhow::bail!("volatile_load requires pointer argument")
                }
            }
            s if s.contains("volatile_store") => {
                let ptr = get_arg(0)?;
                let val = get_arg(1)?;
                if let BasicValueEnum::PointerValue(ptr_val) = ptr {
                    self.builder().build_store(ptr_val, val)?;
                }
                Ok(self.context().i64_type().const_zero().into())
            }

            // Default: return zero for unknown intrinsics
            _ => {
                Ok(self.context().i64_type().const_zero().into())
            }
        }
    }

    /// Calculate the size of a type in bytes
    fn calculate_size_of(ty: &rv_lir::LirType) -> usize {
        match ty {
            rv_lir::LirType::Int(width, _) => match width {
                rv_hir::IntWidth::I8 => 1,
                rv_hir::IntWidth::I16 => 2,
                rv_hir::IntWidth::I32 => 4,
                rv_hir::IntWidth::I64 => 8,
                rv_hir::IntWidth::I128 => 16,
                rv_hir::IntWidth::Isize => 8, // assume 64-bit
            },
            rv_lir::LirType::Float(width) => match width {
                rv_hir::FloatWidth::F32 => 4,
                rv_hir::FloatWidth::F64 => 8,
            },
            rv_lir::LirType::Bool => 1,
            rv_lir::LirType::Char => 4,
            rv_lir::LirType::Unit => 0,
            rv_lir::LirType::String => 16, // fat pointer (ptr + len)
            rv_lir::LirType::Struct { fields, .. } => {
                let mut size = 0;
                let mut max_align = 1;
                for field in fields {
                    let field_align = Self::calculate_align_of(field);
                    let field_size = Self::calculate_size_of(field);
                    // Pad to alignment
                    size = (size + field_align - 1) / field_align * field_align;
                    size += field_size;
                    max_align = max_align.max(field_align);
                }
                // Pad to struct alignment
                (size + max_align - 1) / max_align * max_align
            }
            rv_lir::LirType::Enum { variants, .. } => {
                // discriminant + max variant size
                let mut max_size = 0;
                for variant in variants {
                    let variant_size: usize = variant.fields.iter().map(Self::calculate_size_of).sum();
                    max_size = max_size.max(variant_size);
                }
                8 + max_size // 8 bytes for discriminant
            }
            rv_lir::LirType::Array { element, size } => {
                Self::calculate_size_of(element) * size
            }
            rv_lir::LirType::Tuple(elements) => {
                let mut size = 0;
                let mut max_align = 1;
                for elem in elements {
                    let elem_align = Self::calculate_align_of(elem);
                    let elem_size = Self::calculate_size_of(elem);
                    size = (size + elem_align - 1) / elem_align * elem_align;
                    size += elem_size;
                    max_align = max_align.max(elem_align);
                }
                (size + max_align - 1) / max_align * max_align
            }
            rv_lir::LirType::Ref { inner, .. } => {
                if inner.is_unsized() { 16 } else { 8 }
            }
            rv_lir::LirType::Pointer { inner, .. } => {
                if inner.is_unsized() { 16 } else { 8 }
            }
            rv_lir::LirType::Function { .. } | rv_lir::LirType::FunctionPointer { .. } => 8,
            rv_lir::LirType::Box { .. } => 8,
            rv_lir::LirType::Slice { .. } => 16, // fat pointer
            rv_lir::LirType::DynTrait { .. } => 16, // fat pointer
            rv_lir::LirType::ImplTrait { .. } => 8,
            rv_lir::LirType::Never => 0,
        }
    }

    /// Calculate the alignment of a type in bytes
    fn calculate_align_of(ty: &rv_lir::LirType) -> usize {
        match ty {
            rv_lir::LirType::Int(width, _) => match width {
                rv_hir::IntWidth::I8 => 1,
                rv_hir::IntWidth::I16 => 2,
                rv_hir::IntWidth::I32 => 4,
                rv_hir::IntWidth::I64 => 8,
                rv_hir::IntWidth::I128 => 16,
                rv_hir::IntWidth::Isize => 8,
            },
            rv_lir::LirType::Float(width) => match width {
                rv_hir::FloatWidth::F32 => 4,
                rv_hir::FloatWidth::F64 => 8,
            },
            rv_lir::LirType::Bool => 1,
            rv_lir::LirType::Char => 4,
            rv_lir::LirType::Unit => 1,
            rv_lir::LirType::String => 8,
            rv_lir::LirType::Struct { fields, .. } => {
                fields.iter().map(Self::calculate_align_of).max().unwrap_or(1)
            }
            rv_lir::LirType::Enum { variants, .. } => {
                let mut max_align = 8; // discriminant alignment
                for variant in variants {
                    for field in &variant.fields {
                        max_align = max_align.max(Self::calculate_align_of(field));
                    }
                }
                max_align
            }
            rv_lir::LirType::Array { element, .. } => Self::calculate_align_of(element),
            rv_lir::LirType::Tuple(elements) => {
                elements.iter().map(Self::calculate_align_of).max().unwrap_or(1)
            }
            rv_lir::LirType::Ref { .. } | rv_lir::LirType::Pointer { .. } => 8,
            rv_lir::LirType::Function { .. } | rv_lir::LirType::FunctionPointer { .. } => 8,
            rv_lir::LirType::Box { .. } => 8,
            rv_lir::LirType::Slice { .. } => 8,
            rv_lir::LirType::DynTrait { .. } => 8,
            rv_lir::LirType::ImplTrait { .. } => 8,
            rv_lir::LirType::Never => 1,
        }
    }

    /// Check if a type needs drop
    fn type_needs_drop(ty: &rv_lir::LirType) -> bool {
        match ty {
            rv_lir::LirType::Int(..)
            | rv_lir::LirType::Float(..)
            | rv_lir::LirType::Bool
            | rv_lir::LirType::Char
            | rv_lir::LirType::Unit
            | rv_lir::LirType::Never => false,
            rv_lir::LirType::String => true,
            rv_lir::LirType::Struct { fields, .. } => fields.iter().any(Self::type_needs_drop),
            rv_lir::LirType::Enum { variants, .. } => {
                variants.iter().any(|v| v.fields.iter().any(Self::type_needs_drop))
            }
            rv_lir::LirType::Array { element, .. } => Self::type_needs_drop(element),
            rv_lir::LirType::Tuple(elements) => elements.iter().any(Self::type_needs_drop),
            rv_lir::LirType::Ref { .. } | rv_lir::LirType::Pointer { .. } => false,
            rv_lir::LirType::Function { .. } | rv_lir::LirType::FunctionPointer { .. } => false,
            rv_lir::LirType::Box { .. } => true,
            rv_lir::LirType::Slice { .. } => false,
            rv_lir::LirType::DynTrait { .. } => true,
            rv_lir::LirType::ImplTrait { .. } => true,
        }
    }

    /// Compute a hash for type identity
    fn type_hash(ty: &rv_lir::LirType) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        // Hash the debug representation as a simple hash
        format!("{:?}", ty).hash(&mut hasher);
        hasher.finish()
    }

    /// Get the name of a type as a string
    fn type_name(ty: &rv_lir::LirType) -> String {
        match ty {
            rv_lir::LirType::Int(width, sign) => {
                let prefix = match sign {
                    rv_hir::Signedness::Signed => "i",
                    rv_hir::Signedness::Unsigned => "u",
                };
                let bits = match width {
                    rv_hir::IntWidth::I8 => "8",
                    rv_hir::IntWidth::I16 => "16",
                    rv_hir::IntWidth::I32 => "32",
                    rv_hir::IntWidth::I64 => "64",
                    rv_hir::IntWidth::I128 => "128",
                    rv_hir::IntWidth::Isize => "size",
                };
                format!("{}{}", prefix, bits)
            }
            rv_lir::LirType::Float(width) => match width {
                rv_hir::FloatWidth::F32 => "f32".to_string(),
                rv_hir::FloatWidth::F64 => "f64".to_string(),
            },
            rv_lir::LirType::Bool => "bool".to_string(),
            rv_lir::LirType::Char => "char".to_string(),
            rv_lir::LirType::Unit => "()".to_string(),
            rv_lir::LirType::String => "&str".to_string(),
            rv_lir::LirType::Struct { name, .. } => format!("{:?}", name),
            rv_lir::LirType::Enum { name, .. } => format!("{:?}", name),
            rv_lir::LirType::Array { element, size } => format!("[{}; {}]", Self::type_name(element), size),
            rv_lir::LirType::Tuple(elements) => {
                let names: Vec<_> = elements.iter().map(Self::type_name).collect();
                format!("({})", names.join(", "))
            }
            rv_lir::LirType::Ref { inner, mutable, .. } => {
                if *mutable {
                    format!("&mut {}", Self::type_name(inner))
                } else {
                    format!("&{}", Self::type_name(inner))
                }
            }
            rv_lir::LirType::Pointer { inner, mutable } => {
                if *mutable {
                    format!("*mut {}", Self::type_name(inner))
                } else {
                    format!("*const {}", Self::type_name(inner))
                }
            }
            rv_lir::LirType::Function { params, ret } => {
                let param_names: Vec<_> = params.iter().map(Self::type_name).collect();
                format!("fn({}) -> {}", param_names.join(", "), Self::type_name(ret))
            }
            rv_lir::LirType::FunctionPointer { params, ret, .. } => {
                let param_names: Vec<_> = params.iter().map(Self::type_name).collect();
                format!("fn({}) -> {}", param_names.join(", "), Self::type_name(ret))
            }
            rv_lir::LirType::Box { inner } => format!("Box<{}>", Self::type_name(inner)),
            rv_lir::LirType::Slice { element } => format!("[{}]", Self::type_name(element)),
            rv_lir::LirType::DynTrait { principal } => format!("dyn {:?}", principal),
            rv_lir::LirType::ImplTrait { principal } => format!("impl {:?}", principal),
            rv_lir::LirType::Never => "!".to_string(),
        }
    }
}
