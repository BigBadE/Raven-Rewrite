use inkwell::context::Context;
use inkwell::types::BasicTypeEnum;
use std::collections::HashMap;
use syntax::mir::types::MediumType;
use syntax::mir::MediumSyntaxLevel;
use syntax::{Syntax, TypeRef};

pub struct TypeManager<'ctx> {
    pub syntax: &'ctx Syntax<MediumSyntaxLevel>,
    pub context: &'ctx Context,
    pub types: HashMap<TypeRef, BasicTypeEnum<'ctx>>,
}

impl<'ctx> TypeManager<'ctx> {
    pub fn convert_type(&mut self, types: TypeRef) -> BasicTypeEnum<'ctx> {
        if let Some(found) = self.types.get(&types) {
            return *found;
        }
        let compiled = self.compile_type(&self.syntax.types[types.0]);
        self.types.insert(types, compiled);
        compiled
    }

    fn compile_type(&mut self, types: &MediumType<MediumSyntaxLevel>) -> BasicTypeEnum<'ctx> {
        BasicTypeEnum::StructType(self.context.struct_type(
            types.fields.iter().map(|field| self.convert_type(*field)).collect::<Vec<_>>().as_slice(), false,
        ))
    }
}