use syntax::structure::visitor::Translate;
use syntax::structure::{FileOwner, Modifier};
use syntax::util::path::FilePath;
use syntax::util::translation::{translate_fields, translate_vec};
use syntax::util::translation::Translatable;
use syntax::util::ParseError;
use syntax::SyntaxLevel;
use lasso::Spur;
use std::fmt::Debug;
use serde::{Deserialize, Serialize};
use syntax::structure::traits::Type;
use crate::RawSyntaxLevel;

#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
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

#[derive(Serialize, Deserialize, Debug)]
pub enum TypeData<T: SyntaxLevel> {
    Struct {
        fields: Vec<(Spur, T::TypeReference)>,
    },
    Trait {
        functions: Vec<T::Function>
    }
}

// Handle type translations
impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<Option<HighType<O>>, C, I, O> for HighType<I>
{
    fn translate(&self, context: &mut C) -> Result<Option<HighType<O>>, ParseError> {
        context.set_file(self.file().clone());
        Ok(Some(HighType {
            name: self.name.clone(),
            file: self.file.clone(),
            modifiers: self.modifiers.clone(),
            data: match &self.data {
                TypeData::Struct { fields } => TypeData::Struct {
                    fields: translate_fields(fields, context, I::translate_type_ref)?
                },
                TypeData::Trait { functions } => TypeData::Trait {
                    functions: translate_vec(functions, context, I::translate_func)?
                }
            },
        }))
    }
}
