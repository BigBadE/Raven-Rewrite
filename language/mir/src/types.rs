use crate::{MediumSyntaxLevel, MirFunctionContext};
use hir::types::{HighType, TypeData};
use lasso::Spur;
use serde::{Deserialize, Serialize};
use syntax::structure::traits::Type;
use syntax::structure::visitor::Translate;
use syntax::structure::Modifier;
use syntax::util::path::FilePath;
use syntax::util::translation::Translatable;
use syntax::util::ParseError;
use syntax::SyntaxLevel;

#[derive(Serialize, Deserialize, Debug)]
pub struct MediumType<T: SyntaxLevel> {
    pub name: Spur,
    pub file: FilePath,
    pub modifiers: Vec<Modifier>,
    pub fields: Vec<T::TypeReference>,
}

impl<T: SyntaxLevel> Type for MediumType<T> {
    fn file(&self) -> &FilePath {
        &self.file
    }
}

impl<'a, 'b, I: SyntaxLevel + Translatable<MirFunctionContext<'a>, I, MediumSyntaxLevel>>
    Translate<Option<MediumType<MediumSyntaxLevel>>, MirFunctionContext<'a>, I, MediumSyntaxLevel>
    for HighType<I>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<Option<MediumType<MediumSyntaxLevel>>, ParseError> {
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
