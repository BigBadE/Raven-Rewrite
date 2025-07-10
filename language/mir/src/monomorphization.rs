use std::collections::HashMap;
use crate::MirFunctionContext;
use anyhow::anyhow;
use hir::function::HighFunction;
use hir::types::HighType;
use hir::HighSyntaxLevel;
use lasso::ThreadedRodeo;
use syntax::structure::visitor::Translate;
use syntax::util::pretty_print::PrettyPrint;
use syntax::util::CompileError;
use syntax::{FunctionRef, GenericFunctionRef, GenericTypeRef, TypeRef};

pub struct MonomorphizationContext<'a, 'b> {
    pub generics: HashMap<GenericTypeRef, TypeRef>,
    pub context: &'a mut MirFunctionContext<'b>
}

impl Translate<TypeRef, MonomorphizationContext<'_, '_>> for HighType<HighSyntaxLevel> {
    fn translate(&self, context: &mut MonomorphizationContext) -> Result<TypeRef, CompileError> {
        let GenericTypeRef::Struct { reference, .. } = &self.reference else {
            return Err(CompileError::Internal(anyhow!("Cannot monomorphize generic type reference")))
        };

        let reference = add_generics_to_reference(&reference, &context.generics, &context.context.output.symbols)?;
        let mut temp = (*self).clone();
        temp.reference = GenericTypeRef::Struct {
            reference: reference.clone(),
            generics: vec![]
        };

        let mut inner_context = MirFunctionContext::new(context.context.source, context.context.output);
        inner_context.generics = context.generics.clone();
        temp.translate(&mut inner_context)?;

        Ok(reference)
    }
}

impl Translate<FunctionRef, MonomorphizationContext<'_, '_>> for HighFunction<HighSyntaxLevel> {
    fn translate(&self, context: &mut MonomorphizationContext) -> Result<FunctionRef, CompileError> {
        let mut inner_context = MirFunctionContext::new(context.context.source, context.context.output);
        inner_context.generics = context.generics.clone();
        let mut temp = (*self).clone();
        temp.reference = GenericFunctionRef {
            reference: add_generics_to_reference(&self.reference.reference, &context.generics,
                                                 &inner_context.output.symbols)?,
            generics: vec![]
        };
        temp.translate(&mut inner_context)?;

        Ok(temp.reference.reference)
    }
}

fn add_generics_to_reference(reference: &TypeRef, generics: &HashMap<GenericTypeRef, TypeRef>, interner: &ThreadedRodeo) -> Result<TypeRef, CompileError> {
    let mut reference = reference.clone();
    let last = reference.last_mut().unwrap();
    let mut string = interner.resolve(last).to_string();
    string.push('_');
    for (i, generic) in generics.values().enumerate() {
        if i > 0 {
            string.push('_');
        }
        generic.format_top(interner, &mut string)?;
    }
    *last = interner.get_or_intern(string);
    Ok(reference)
}