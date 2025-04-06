use crate::RawSyntaxLevel;
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use syntax::SyntaxLevel;
use syntax::structure::traits::Type;
use syntax::structure::visitor::Translate;
use syntax::structure::{FileOwner, Modifier};
use syntax::util::ParseError;
use syntax::util::path::FilePath;
use syntax::util::translation::{translate_vec, Translatable};
use syntax::util::translation::translate_fields;

#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub struct HighType<T: SyntaxLevel> {
    pub name: Spur,
    pub file: FilePath,
    pub generics: Vec<(Spur, Vec<T::TypeReference>)>,
    pub modifiers: Vec<Modifier>,
    pub data: TypeData<T>,
}

impl HighType<RawSyntaxLevel> {
    pub fn internal(name: Spur) -> Self {
        Self {
            name,
            file: vec![name],
            generics: vec![],
            modifiers: vec![Modifier::PUBLIC],
            data: TypeData::Struct { fields: vec![] },
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
        functions: Vec<T::Function>,
    },
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
            generics: self
                .generics
                .iter()
                .map(|(name, generics)| {
                    Ok((
                        name.clone(),
                        translate_vec(generics, context, I::translate_type_ref)?
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?,
            modifiers: self.modifiers.clone(),
            data: match &self.data {
                TypeData::Struct { fields } => TypeData::Struct {
                    fields: translate_fields(fields, context, I::translate_type_ref)?,
                },
                TypeData::Trait { .. } => return Ok(None),
            },
        }))
    }
}
