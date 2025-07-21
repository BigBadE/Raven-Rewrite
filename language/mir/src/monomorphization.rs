use std::collections::HashMap;
use crate::MirFunctionContext;
use anyhow::anyhow;
use hir::function::HighFunction;
use hir::types::{HighType, TypeData};
use hir::HighSyntaxLevel;
use syntax::structure::visitor::Translate;
use syntax::util::CompileError;
use syntax::{get_monomorphized_name, FunctionRef, GenericFunctionRef, GenericTypeRef, TypeRef};

/// Contains the generics currently in scope and the context for the outer function
pub struct MonomorphizationContext<'a, 'b> {
    pub generics: HashMap<GenericTypeRef, TypeRef>,
    pub context: &'a mut MirFunctionContext<'b>
}

impl Translate<TypeRef, MonomorphizationContext<'_, '_>> for HighType<HighSyntaxLevel> {
    /// Translate the function by cloning the type, updating the reference, then substituting the fields
    fn translate(&self, context: &mut MonomorphizationContext) -> Result<TypeRef, CompileError> {
        let GenericTypeRef::Struct { reference, .. } = &self.reference else {
            return Err(CompileError::Internal(anyhow!("Cannot monomorphize generic type reference")))
        };

        // Clone the type and update the reference
        let monomorphized_reference = get_monomorphized_name(&reference, context.generics.values(),
                                                             &context.context.output.symbols)?;
        let mut inner_context = MirFunctionContext::new(context.context.source, context.context.output);
        inner_context.generics = context.generics.clone();
        let mut temp = (*self).clone();
        temp.reference = GenericTypeRef::Struct {
            reference: monomorphized_reference.clone(),
            generics: vec![]
        };
        temp.generics.clear();
        
        // Substitute generics in type fields
        match &mut temp.data {
            TypeData::Struct { fields } => {
                for (_, field_type) in fields {
                    *field_type = field_type.substitute_generics_in_type(&context.generics)?;
                }
            }
            TypeData::Trait { .. } => {
                // Traits don't have fields to substitute
            }
        }
        
        temp.translate(&mut inner_context)?;

        Ok(monomorphized_reference)
    }
}

impl Translate<FunctionRef, MonomorphizationContext<'_, '_>> for HighFunction<HighSyntaxLevel> {
    fn translate(&self, context: &mut MonomorphizationContext) -> Result<FunctionRef, CompileError> {
        // Clone the function and update the reference
        let monomorphized_reference = get_monomorphized_name(&self.reference.reference, context.generics.values(),
                                                                &context.context.output.symbols)?;
        let mut inner_context = MirFunctionContext::new(context.context.source, context.context.output);
        inner_context.generics = context.generics.clone();
        let mut temp = (*self).clone();
        temp.reference = GenericFunctionRef {
            reference: monomorphized_reference.clone(),
            generics: vec![]
        };
        temp.generics.clear();

        // Substitute generics in parameters and return type
        for (_, param_type) in &mut temp.parameters {
            *param_type = param_type.substitute_generics_in_type(&context.generics)?;
        }

        if let Some(ref mut return_type) = temp.return_type {
            *return_type = return_type.substitute_generics_in_type(&context.generics)?;
        }
        
        temp.translate(&mut inner_context)?;

        Ok(monomorphized_reference)
    }
}