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
use rv_hir::{ExternalFunction, FunctionId, LiteralKind};
use rv_lir::{
    AggregateKind, BasicBlock, BinaryOp, Constant, LocalId, LirFunction, Operand, Place, RValue,
    Statement, Terminator, UnaryOp,
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
        external_functions: &HashMap<FunctionId, ExternalFunction>,
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
        external_functions: &HashMap<FunctionId, ExternalFunction>,
    ) -> Result<()> {
        let compiler = Compiler::new(&self.context, &self.module_name, self.opt_level);
        compiler.compile_functions_with_externals(functions, external_functions)?;

        // Get IR string for later use
        let ir = compiler.module.print_to_string().to_string();

        *self.compiled_state.borrow_mut() = Some(CompiledState { ir });

        Ok(())
    }

    pub fn compile_functions(
        &self,
        functions: &[LirFunction],
    ) -> Result<()> {
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
                &self.module_name
            );
            let module = self.context.create_module_from_ir(memory_buffer)
                .map_err(|e| anyhow::anyhow!("Failed to parse IR: {}", e))?;

            // Write object file
            self.write_module_to_object(&module, output_path)
        } else {
            anyhow::bail!("No compiled IR available. Call compile_functions_with_externals first.")
        }
    }

    fn write_module_to_object(
        &self,
        module: &Module,
        output_path: &Path,
    ) -> Result<()> {
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
                RelocMode::Default,
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
    pub fn compile_functions(&self, mir_funcs: &[LirFunction]) -> Result<()> {
        self.compile_functions_with_externals(mir_funcs, &HashMap::new())
    }

    /// Compile multiple MIR functions with external function support
    pub fn compile_functions_with_externals(
        &self,
        mir_funcs: &[LirFunction],
        external_funcs: &HashMap<FunctionId, ExternalFunction>,
    ) -> Result<()> {
        use std::collections::HashMap;

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
                        self.context.i32_type().into()
                    }
                })
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

        // Phase 4: Create main() wrapper that calls first function and exits
        if !mir_funcs.is_empty() {
            self.create_main_wrapper(&llvm_functions, &mir_funcs[0])?;
        }

        Ok(())
    }

    /// Create a main() wrapper function that calls the entry point and exits
    fn create_main_wrapper(&self, llvm_functions: &HashMap<FunctionId, FunctionValue>, entry_func: &LirFunction) -> Result<()> {
        // Create main() function with signature: int main()
        let main_fn_type = self.context.i32_type().fn_type(&[], false);
        let main_function = self.module.add_function("main", main_fn_type, None);

        // Create entry basic block
        let entry_block = self.context.append_basic_block(main_function, "entry");
        self.builder.position_at_end(entry_block);

        // Call the entry function (func_0) - discard its return value
        if let Some(&entry_fn_value) = llvm_functions.get(&entry_func.id) {
            self.builder.build_call(entry_fn_value, &[], "call_entry")?;
        }

        // Always return 0 (success) regardless of entry function's return value
        // The entry function's return value is computational, not a program exit status
        self.builder.build_return(Some(&self.context.i32_type().const_int(0, false)))?;

        Ok(())
    }

    /// Compile a single MIR function to LLVM IR (legacy API)
    pub fn compile_function(&self, mir_func: &LirFunction) -> Result<FunctionValue<'ctx>> {
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
            let alloca = self.builder().build_alloca(llvm_type, &format!("local_{}", local.id.0))
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
                    self.builder().build_store(*ptr, *param_value)
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
                        let local_ty = self.mir_func.locals
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
                                    value = self.builder().build_int_z_extend(
                                        value_int,
                                        expected_int_type,
                                        "zext"
                                    ).map_err(|e| anyhow::anyhow!("Failed to zero-extend: {}", e))?.into();
                                } else if value_width > expected_width {
                                    // Truncate larger values
                                    value = self.builder().build_int_truncate(
                                        value_int,
                                        expected_int_type,
                                        "trunc"
                                    ).map_err(|e| anyhow::anyhow!("Failed to truncate: {}", e))?.into();
                                }
                            }
                        }
                    }

                    self.builder().build_store(ptr, value)
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
                let call_site = self.builder()
                    .build_call(*callee, &args_metadata, "call")
                    .map_err(|e| anyhow::anyhow!("Failed to build call: {}", e))?;

                // Get return value
                let return_value = call_site.try_as_basic_value().left()
                    .ok_or_else(|| {
                        anyhow::anyhow!(
                            "COMPILER BUG: Function call to {:?} returned void, but MIR expects all \
                             function calls to produce a value. All functions should return at least Unit type.",
                            func
                        )
                    })?;

                Ok(return_value)
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
                    AggregateKind::Struct | AggregateKind::Tuple => {
                        // Create a struct/tuple aggregate with all fields
                        if operands.is_empty() {
                            // Empty struct/tuple - return unit value
                            return Ok(self.context().i32_type().const_int(0, false).into());
                        }

                        // Compile all field values
                        let field_values: Result<Vec<BasicValueEnum>> = operands
                            .iter()
                            .map(|op| self.compile_operand(op))
                            .collect();
                        let field_values = field_values?;

                        // Create struct type with the correct number of fields
                        let field_types: Vec<BasicTypeEnum> = field_values
                            .iter()
                            .map(|val| val.get_type())
                            .collect();

                        let struct_type = self.context().struct_type(&field_types, false);
                        let mut aggregate_value = struct_type.get_undef();

                        // Insert each field value
                        for (i, field_val) in field_values.into_iter().enumerate() {
                            aggregate_value = self.builder()
                                .build_insert_value(aggregate_value, field_val, i as u32, &format!("field_{}", i))
                                .map_err(|e| anyhow::anyhow!("Failed to insert field {}: {}", i, e))?
                                .into_struct_value();
                        }

                        Ok(aggregate_value.into())
                    }
                    AggregateKind::Array(_element_ty) => {
                        // Create an array aggregate
                        // Array size is determined by the number of operands
                        if operands.is_empty() {
                            // Empty array - return zero-sized array
                            let i32_type = self.context().i32_type();
                            return Ok(i32_type.array_type(0).const_zero().into());
                        }

                        // Compile all element values
                        let element_values: Result<Vec<BasicValueEnum>> = operands
                            .iter()
                            .map(|op| self.compile_operand(op))
                            .collect();
                        let element_values = element_values?;

                        let array_size = element_values.len();

                        // Get element type from first element
                        let element_type = element_values[0].get_type();
                        let array_type = element_type.array_type(array_size as u32);
                        let mut array_value = array_type.get_undef();

                        // Insert each element
                        for (i, elem_val) in element_values.into_iter().enumerate() {
                            array_value = self.builder()
                                .build_insert_value(array_value, elem_val, i as u32, &format!("elem_{}", i))
                                .map_err(|e| anyhow::anyhow!("Failed to insert element {}: {}", i, e))?
                                .into_array_value();
                        }

                        Ok(array_value.into())
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
                    let llvm_type = self.type_lowering().lower_type(&place_ty);

                    // Load value from place
                    self.builder().build_load(llvm_type, ptr_val, "load")
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
        let local_info = self.mir_func.locals
            .iter()
            .find(|l| l.id == place.local)
            .ok_or_else(|| anyhow::anyhow!("Unknown local: {:?}", place.local))?;

        let mut current_type = local_info.ty.clone();

        // Apply projections to get the final type
        for projection in &place.projection {
            match projection {
                PlaceElem::Field { field_idx } => {
                    if let rv_lir::LirType::Struct { fields, .. } = &current_type {
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
                    // Dereference unwraps the reference type to get the inner type
                    if let rv_lir::LirType::Ref { inner, .. } = &current_type {
                        current_type = (**inner).clone();
                    } else {
                        anyhow::bail!("Cannot dereference non-reference type: {:?}", current_type);
                    }
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
                Ok(self.context().i32_type().const_int(*val as u64, false).into())
            }
            LiteralKind::Float(val) => {
                Ok(self.context().f64_type().const_float(*val).into())
            }
            LiteralKind::Bool(val) => {
                // Use i32 for booleans for consistency with comparison operators
                Ok(self.context().i32_type().const_int(*val as u64, false).into())
            }
            LiteralKind::String(s) => {
                // Create a global string constant and return pointer to it
                let global_string = self.builder()
                    .build_global_string_ptr(s, "str")
                    .map_err(|e| anyhow::anyhow!("Failed to build global string: {}", e))?;
                Ok(global_string.as_pointer_value().into())
            }
            LiteralKind::Unit => {
                Ok(self.context().i32_type().const_int(0, false).into())
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
            BinaryOp::Add => self.builder().build_int_add(lhs_int, rhs_int, "add"),
            BinaryOp::Sub => self.builder().build_int_sub(lhs_int, rhs_int, "sub"),
            BinaryOp::Mul => self.builder().build_int_mul(lhs_int, rhs_int, "mul"),
            BinaryOp::Div => self.builder().build_int_signed_div(lhs_int, rhs_int, "div"),
            BinaryOp::Mod => self.builder().build_int_signed_rem(lhs_int, rhs_int, "mod"),
            BinaryOp::Eq => {
                let cmp = self.builder().build_int_compare(IntPredicate::EQ, lhs_int, rhs_int, "eq")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                // Extend i1 to i32 for consistency (MIR bool type maps to i32)
                let extended = self.builder().build_int_z_extend(cmp, self.context().i32_type(), "bool_to_i32")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Ne => {
                let cmp = self.builder().build_int_compare(IntPredicate::NE, lhs_int, rhs_int, "ne")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self.builder().build_int_z_extend(cmp, self.context().i32_type(), "bool_to_i32")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Lt => {
                let cmp = self.builder().build_int_compare(IntPredicate::SLT, lhs_int, rhs_int, "lt")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self.builder().build_int_z_extend(cmp, self.context().i32_type(), "bool_to_i32")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Le => {
                let cmp = self.builder().build_int_compare(IntPredicate::SLE, lhs_int, rhs_int, "le")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self.builder().build_int_z_extend(cmp, self.context().i32_type(), "bool_to_i32")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Gt => {
                let cmp = self.builder().build_int_compare(IntPredicate::SGT, lhs_int, rhs_int, "gt")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self.builder().build_int_z_extend(cmp, self.context().i32_type(), "bool_to_i32")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::Ge => {
                let cmp = self.builder().build_int_compare(IntPredicate::SGE, lhs_int, rhs_int, "ge")
                    .map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;
                let extended = self.builder().build_int_z_extend(cmp, self.context().i32_type(), "bool_to_i32")
                    .map_err(|e| anyhow::anyhow!("Failed to extend bool: {}", e))?;
                return Ok(extended.into());
            }
            BinaryOp::BitAnd => self.builder().build_and(lhs_int, rhs_int, "and"),
            BinaryOp::BitOr => self.builder().build_or(lhs_int, rhs_int, "or"),
            BinaryOp::BitXor => self.builder().build_xor(lhs_int, rhs_int, "xor"),
            BinaryOp::Shl => self.builder().build_left_shift(lhs_int, rhs_int, "shl"),
            BinaryOp::Shr => self.builder().build_right_shift(lhs_int, rhs_int, false, "shr"),
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
                self.builder().build_int_neg(val_int, "neg")
                    .map_err(|e| anyhow::anyhow!("Failed to build negation: {}", e))?
            }
            UnaryOp::Not => {
                self.builder().build_not(val_int, "not")
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
                        self.builder().build_int_z_extend(
                            val.into_int_value(),
                            self.context().i32_type(),
                            "bool_to_i32"
                        ).map_err(|e| anyhow::anyhow!("Failed to extend bool to i32: {}", e))?.into()
                    } else {
                        val
                    };

                    self.builder().build_return(Some(&ret_val))
                        .map_err(|e| anyhow::anyhow!("Failed to build return: {}", e))?;
                } else {
                    // Return void/unit
                    let zero = self.context().i32_type().const_int(0, false);
                    self.builder().build_return(Some(&zero))
                        .map_err(|e| anyhow::anyhow!("Failed to build return: {}", e))?;
                }
            }

            Terminator::Goto { target } => {
                if let Some(target_bb) = self.blocks.get(&target) {
                    self.builder().build_unconditional_branch(*target_bb)
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
                        // Debug: print what type it actually is
                        let type_str = if discr_val.is_pointer_value() {
                            "PointerValue".to_string()
                        } else if discr_val.is_struct_value() {
                            "StructValue".to_string()
                        } else if discr_val.is_array_value() {
                            "ArrayValue".to_string()
                        } else if discr_val.is_vector_value() {
                            "VectorValue".to_string()
                        } else {
                            "Unknown".to_string()
                        };
                        anyhow::bail!("Discriminant is not an integer value, got: {}", type_str);
                    };

                    // Create comparison: discr_val != 0
                    let zero = if discr_int.get_type().get_bit_width() == 1 {
                        discr_int.get_type().const_int(0, false)
                    } else {
                        self.context().i32_type().const_int(0, false)
                    };

                    let condition = self.builder().build_int_compare(
                        IntPredicate::NE,
                        discr_int,
                        zero,
                        "switchcond"
                    ).map_err(|e| anyhow::anyhow!("Failed to build comparison: {}", e))?;

                    // Build conditional branch
                    self.builder().build_conditional_branch(condition, *then_bb, *else_bb)
                        .map_err(|e| anyhow::anyhow!("Failed to build conditional branch: {}", e))?;
                } else {
                    // More complex switch - not implemented yet
                    // For now, just jump to otherwise
                    if let Some(else_bb) = self.blocks.get(otherwise) {
                        self.builder().build_unconditional_branch(*else_bb)
                            .map_err(|e| anyhow::anyhow!("Failed to build branch: {}", e))?;
                    }
                }
            }

            Terminator::Call { .. } => {
                // TODO: Implement call terminator
            }

            Terminator::Unreachable => {
                self.builder().build_unreachable()
                    .map_err(|e| anyhow::anyhow!("Failed to build unreachable: {}", e))?;
            }
        }

        Ok(())
    }

    fn get_place(&self, place: &Place) -> Result<BasicValueEnum<'ctx>> {
        use rv_lir::PlaceElem;

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
                            let basic_type = self.type_lowering().lower_type(current_type);

                            // Extract the actual struct type from BasicTypeEnum
                            if let BasicTypeEnum::StructType(struct_type) = basic_type {
                                // GEP with struct_gep for type-safe field access
                                let field_ptr = self.builder().build_struct_gep(
                                    struct_type,
                                    ptr_val,
                                    *field_idx as u32,
                                    "field_ptr"
                                ).map_err(|e| anyhow::anyhow!("Failed to build struct GEP: {}", e))?;

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
                            if let rv_lir::LirType::Ref { inner, .. } = current_type {
                                // Load the pointer stored at ptr_val (double indirection)
                                let llvm_ptr_type = self.type_lowering().lower_type(current_type);
                                let loaded_ptr = self.builder().build_load(llvm_ptr_type, ptr_val, "deref_load")
                                    .map_err(|e| anyhow::anyhow!("Failed to load pointer for deref: {}", e))?;

                                // The loaded value should be a pointer to the inner type
                                local_val = loaded_ptr;
                                current_type = inner;
                            } else {
                                anyhow::bail!("Cannot dereference non-reference type: {:?}", current_type);
                            }
                        } else {
                            anyhow::bail!("Cannot dereference non-pointer value");
                        }
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
