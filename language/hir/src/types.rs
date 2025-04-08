use crate::RawSyntaxLevel;
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use syntax::SyntaxLevel;
use syntax::structure::traits::Type;
use syntax::structure::visitor::Translate;
use syntax::structure::Modifier;
use syntax::util::CompileError;
use syntax::util::path::FilePath;
use syntax::util::translation::translate_fields;
use syntax::util::translation::{Translatable, translate_vec};

/// A type in the HIR
#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub struct HighType<T: SyntaxLevel> {
    /// The name of the type
    pub name: Spur,
    /// The file this type is defined in
    pub file: FilePath,
    /// The type's generics
    pub generics: Vec<(Spur, Vec<T::TypeReference>)>,
    /// The type's modifiers
    pub modifiers: Vec<Modifier>,
    /// The per-type data, such as fields, functions, etc...
    pub data: TypeData<T>,
}

impl<T: SyntaxLevel> Type for HighType<T> {
    fn file(&self) -> &FilePath {
        &self.file
    }
}

impl HighType<RawSyntaxLevel> {
    /// Creates an internal type
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

/// The data associated with a type, depending on what type it is
#[derive(Serialize, Deserialize, Debug)]
pub enum TypeData<T: SyntaxLevel> {
    /// A structure holds fields of data
    Struct {
        /// The fields of the structure
        fields: Vec<(Spur, T::TypeReference)>,
    },
    /// A trait defines what functions data must implement
    Trait {
        /// The functions that must be implemented
        functions: Vec<T::Function>,
    },
}

// Handle type translations
impl<C, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<Option<HighType<O>>, C> for HighType<I>
{
    fn translate(&self, context: &mut C) -> Result<Option<HighType<O>>, CompileError> {
        Ok(Some(HighType {
            name: self.name.clone(),
            file: self.file.clone(),
            generics: self
                .generics
                .iter()
                .map(|(name, generics)| {
                    Ok((
                        name.clone(),
                        translate_vec(generics, context, I::translate_type_ref)?,
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
