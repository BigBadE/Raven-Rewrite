use crate::{MediumSyntaxLevel, MirFunctionContext};
use hir::types::{HighType, TypeData};
use serde::{Deserialize, Serialize};
use hir::HighSyntaxLevel;
use syntax::{GenericTypeRef, SyntaxLevel, TypeRef};
use syntax::structure::Modifier;
use syntax::structure::traits::Type;
use syntax::structure::visitor::Translate;
use syntax::util::CompileError;
use syntax::util::translation::{translate_iterable, Translatable};
use crate::monomorphization::MonomorphizationContext;

/// A type in the MIR
#[derive(Serialize, Deserialize, Clone)]
pub struct MediumType<T: SyntaxLevel> {
    /// The reference to the type
    pub reference: T::TypeReference,
    /// The type's modifiers
    pub modifiers: Vec<Modifier>,
    /// The type's fields
    pub fields: Vec<T::TypeReference>,
}

impl<T: SyntaxLevel> Type<T::TypeReference> for MediumType<T> {
    fn reference(&self) -> &T::TypeReference {
        &self.reference
    }
}

impl<'a> Translate<(), MirFunctionContext<'a>> for HighType<HighSyntaxLevel>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<(), CompileError> {
        // We don't translate functions with generics. The main function will translate the type references,
        // which will in turn call translate with the correct context.
        if !self.generics.is_empty() {
            return Ok(());
        }

        if let TypeData::Struct { fields } = &self.data {
            let types = MediumType::<MediumSyntaxLevel> {
                reference: HighSyntaxLevel::translate_type_ref(&self.reference, context)?,
                modifiers: self.modifiers.clone(),
                fields: fields
                    .iter()
                    .map(|(_, types)| HighSyntaxLevel::translate_type_ref(types, context))
                    .collect::<Result<_, _>>()?,
            };
            context.output.types.insert(types.reference.clone(), types);
        }
        Ok(())
    }
}

impl<'a> Translate<TypeRef, MirFunctionContext<'a>> for GenericTypeRef {
    fn translate(&self, context: &mut MirFunctionContext<'a>) -> Result<TypeRef, CompileError> {
        match self {
            GenericTypeRef::Struct { reference, generics } => {
                if generics.is_empty() {
                    return Ok(reference.clone());
                }

                Translate::<TypeRef, MonomorphizationContext>::
                translate(&context.source.syntax.types[self], &mut MonomorphizationContext {
                    generics: translate_iterable(generics, context, |generic, context|
                        Ok((generic.clone(), Translate::translate(generic, context)?)))?,
                    context
                })
            }
            GenericTypeRef::Generic { .. } => {
                Ok(context.generics[self].clone())
            }
        }
    }
}