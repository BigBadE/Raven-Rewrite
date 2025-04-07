use crate::{MediumSyntaxLevel, MirFunctionContext};
use hir::types::{HighType, TypeData};
use lasso::Spur;
use serde::{Deserialize, Serialize};
use syntax::structure::traits::Type;
use syntax::structure::visitor::Translate;
use syntax::structure::Modifier;
use syntax::util::path::FilePath;
use syntax::util::translation::Translatable;
use syntax::util::CompileError;
use syntax::SyntaxLevel;

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

impl<'a, I: SyntaxLevel + Translatable<MirFunctionContext<'a>, I, MediumSyntaxLevel>>
    Translate<Option<MediumType<MediumSyntaxLevel>>, MirFunctionContext<'a>> for HighType<I>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<Option<MediumType<MediumSyntaxLevel>>, CompileError> {
        Ok(Some(match &self.data {
            TypeData::Struct { fields } => MediumType {
                name: self.name,
                file: self.file.clone(),
                modifiers: self.modifiers.clone(),
                fields: fields
                    .iter()
                    .map(|(_, types)| I::translate_type_ref(types, context))
                    .collect::<Result<_, _>>()?,
            },
            // Raw -> High should get rid of traits
            TypeData::Trait { .. } => unreachable!(),
        }))
    }
}
