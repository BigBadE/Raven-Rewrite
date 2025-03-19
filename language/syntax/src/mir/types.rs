use lasso::Spur;
use crate::hir::types::{HighType, Type, TypeData};
use crate::mir::{MediumSyntaxLevel, MirContext};
use crate::structure::Modifier;
use crate::structure::visitor::Translate;
use crate::SyntaxLevel;
use crate::util::ParseError;
use crate::util::path::FilePath;
use crate::util::translation::Translatable;

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
Translate<MediumType<MediumSyntaxLevel>, MirContext<'_>, I, MediumSyntaxLevel> for HighType<I>
{
    fn translate(&self, context: &mut MirContext) -> Result<MediumType<MediumSyntaxLevel>, ParseError> {
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