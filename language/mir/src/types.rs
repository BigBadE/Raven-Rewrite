use lasso::Spur;
use hir::types::{HighType, TypeData};
use crate::{MediumSyntaxLevel, MirContext};
use syntax::structure::Modifier;
use syntax::structure::traits::Type;
use syntax::structure::visitor::Translate;
use syntax::SyntaxLevel;
use syntax::util::ParseError;
use syntax::util::path::FilePath;
use syntax::util::translation::Translatable;

#[derive(Debug)]
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

impl<'a, I: SyntaxLevel + Translatable<MirContext<'a>, I, MediumSyntaxLevel>>
Translate<MediumType<MediumSyntaxLevel>, MirContext<'a>, I, MediumSyntaxLevel> for HighType<I>
{
    fn translate(&self, context: &mut MirContext<'a>) -> Result<MediumType<MediumSyntaxLevel>, ParseError> {
        Ok(match &self.data {
            TypeData::Struct { fields } => MediumType {
                name: self.name,
                file: self.file.clone(),
                modifiers: self.modifiers.clone(),
                fields: fields.iter().map(|(_, types)| I::translate_type_ref(types, context))
                    .collect::<Result<_, _>>()?,
            }
        })
    }
}