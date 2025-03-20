use syntax::structure::visitor::Translate;
use syntax::structure::{FileOwner, Modifier};
use syntax::util::path::FilePath;
use syntax::util::translation::translate_fields;
use syntax::util::translation::Translatable;
use syntax::util::ParseError;
use syntax::SyntaxLevel;
use lasso::Spur;
use std::fmt::Debug;
use syntax::structure::traits::Type;
use crate::RawSyntaxLevel;

#[derive(Debug)]
pub struct HighType<T: SyntaxLevel> {
    pub name: Spur,
    pub file: FilePath,
    pub modifiers: Vec<Modifier>,
    pub data: TypeData<T>,
}

impl HighType<RawSyntaxLevel> {
    pub fn internal(name: Spur) -> Self {
        Self {
            name,
            file: FilePath::default(),
            modifiers: vec![Modifier::PUBLIC],
            data: TypeData::Struct {
                fields: vec![],
            }
        }
    }
}

impl<T: SyntaxLevel> Type for HighType<T> {
    fn file(&self) -> &FilePath {
        &self.file
    }
}

#[derive(Debug)]
pub enum TypeData<T: SyntaxLevel> {
    Struct {
        fields: Vec<(Spur, T::TypeReference)>,
    },
}

// Handle type translations
impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<HighType<O>, C, I, O> for HighType<I>
{
    fn translate(&self, context: &mut C) -> Result<HighType<O>, ParseError> {
        context.set_file(self.file().clone());
        Ok(HighType {
            name: self.name.clone(),
            file: self.file.clone(),
            modifiers: self.modifiers.clone(),
            data: match &self.data {
                TypeData::Struct { fields } => TypeData::Struct {
                    fields: translate_fields(fields, context, I::translate_type_ref)?,
                },
            },
        })
    }
}
