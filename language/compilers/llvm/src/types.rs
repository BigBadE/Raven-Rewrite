use crate::function::get_function_type;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::BasicTypeEnum;
use inkwell::values::FunctionValue;
use mir::types::MediumType;
use mir::MediumSyntaxLevel;
use std::collections::HashMap;
use syntax::{FunctionRef, Syntax, TypeRef};

/// Manages the MIR types and converting them to LLVMIR versions
pub struct TypeManager<'a, 'ctx> {
    /// The syntax tree
    pub syntax: &'ctx Syntax<MediumSyntaxLevel>,
    /// The LLVM context
    pub context: &'ctx Context,
    /// The LLVM module
    pub module: &'a Module<'ctx>,
    /// The LLVM builder
    pub builder: &'a Builder<'ctx>,
    /// MIR to LLVMIR type map
    pub types: HashMap<TypeRef, BasicTypeEnum<'ctx>>,
    /// MIR to LLVMIR function map
    pub functions: HashMap<FunctionRef, FunctionValue<'ctx>>,
}

impl<'a, 'ctx> TypeManager<'a, 'ctx> {
    /// Gets the LLVMIR function from the MIR function ref
    pub fn function_type(&mut self, reference: &FunctionRef) -> FunctionValue<'ctx> {
        if let Some(found) = self.functions.get(&reference) {
            return *found;
        }
        let function = &self.syntax.functions[reference.0];
        let compiled = get_function_type(self, function);
        self.functions.insert(*reference, compiled);
        compiled
    }

    /// Gets the LLVMIR type from the MIR type ref
    pub fn convert_type(&mut self, types: TypeRef) -> BasicTypeEnum<'ctx> {
        if let Some(found) = self.types.get(&types) {
            return *found;
        }
        let compiled = self.compile_type(&self.syntax.types[types.0]);
        self.types.insert(types, compiled);
        compiled
    }

    /// Compiles a MIR type to an LLVMIR type
    fn compile_type(&mut self, types: &MediumType<MediumSyntaxLevel>) -> BasicTypeEnum<'ctx> {
        BasicTypeEnum::StructType(
            self.context.struct_type(
                types
                    .fields
                    .iter()
                    .map(|field| self.convert_type(*field))
                    .collect::<Vec<_>>()
                    .as_slice(),
                false,
            ),
        )
    }
}
