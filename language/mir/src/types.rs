use crate::{MediumSyntaxLevel, MirFunctionContext};
use hir::types::{HighType, TypeData};
use lasso::Spur;
use serde::{Deserialize, Serialize};
use hir::HighSyntaxLevel;
use syntax::{GenericTypeRef, SyntaxLevel, TypeRef};
use syntax::structure::Modifier;
use syntax::structure::traits::Type;
use syntax::structure::visitor::Translate;
use syntax::util::CompileError;
use syntax::util::path::FilePath;
use syntax::util::translation::Translatable;
use crate::monomorphization::MonomorphizationContext;

/// A type in the MIR
#[derive(Serialize, Deserialize, Debug)]
pub struct MediumType<T: SyntaxLevel> {
    /// The type's name
    pub name: Spur,
    /// The file path where the type is defined
    pub file: FilePath,
    /// The type's modifiers
    pub modifiers: Vec<Modifier>,
    /// The type's fields
    pub fields: Vec<T::TypeReference>,
}

impl<T: SyntaxLevel> Type for MediumType<T> {
    fn reference(&self) -> &FilePath {
        &self.file
    }
}

impl<'a, I: SyntaxLevel + Translatable<I, MediumSyntaxLevel>>
Translate<Option<MediumType<MediumSyntaxLevel>>, MirFunctionContext<'a>> for HighType<I>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<Option<MediumType<MediumSyntaxLevel>>, CompileError> {
        // We don't translate functions with generics. The main function will translate the type references,
        // which will in turn call translate with the correct context.
        if !self.generics.is_empty() {
            return Ok(None);
        }

        Ok(match &self.data {
            TypeData::Struct { fields } => Some(MediumType {
                name: self.name,
                file: self.file.clone(),
                modifiers: self.modifiers.clone(),
                fields: fields
                    .iter()
                    .map(|(_, types)| I::translate_type_ref(types, context))
                    .collect::<Result<_, _>>()?,
            }),
            TypeData::Trait { .. } => None,
        })
    }
}

impl<'a> Translate<TypeRef, MirFunctionContext<'a>> for GenericTypeRef {
    fn translate(&self, context: &mut MirFunctionContext<'a>) -> Result<TypeRef, CompileError> {
        match self {
            // TODO
            GenericTypeRef::Struct { reference, generics } => {
                if generics.is_empty() {
                    return Ok(*reference);
                }

                context.source.syntax.types.push(
                    Translate::<HighType<HighSyntaxLevel>, MonomorphizationContext>::
                    translate(&context.source.syntax.types[*reference], &mut MonomorphizationContext {
                        generics: generics.clone()
                    })?);
                Ok(context.source.syntax.types.len() - 1)
            }
            GenericTypeRef::Generic { reference } => {

                Ok(*reference)
            }
        }
    }
}