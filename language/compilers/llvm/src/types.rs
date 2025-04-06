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

pub struct TypeManager<'a, 'ctx> {
    pub syntax: &'ctx Syntax<MediumSyntaxLevel>,
    pub context: &'ctx Context,
    pub module: &'a Module<'ctx>,
    pub builder: &'a Builder<'ctx>,
    pub types: HashMap<TypeRef, BasicTypeEnum<'ctx>>,
    pub functions: HashMap<FunctionRef, FunctionValue<'ctx>>,
}

impl<'a, 'ctx> TypeManager<'a, 'ctx> {
    pub fn function_type(&mut self, reference: &FunctionRef) -> FunctionValue<'ctx> {
        if let Some(found) = self.functions.get(&reference) {
            return *found;
        }
        let function = &self.syntax.functions[reference.0];
        let compiled = get_function_type(self, function);
        self.functions.insert(*reference, compiled);
        compiled
    }

    pub fn convert_type(&mut self, types: TypeRef) -> BasicTypeEnum<'ctx> {
        if let Some(found) = self.types.get(&types) {
            return *found;
        }
        let compiled = self.compile_type(&self.syntax.types[types.0]);
        self.types.insert(types, compiled);
        compiled
    }

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
