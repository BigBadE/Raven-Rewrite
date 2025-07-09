use crate::{HighSyntaxLevel, HirFunctionContext, RawSyntaxLevel, RawTypeRef};
use lasso::Spur;
use serde::{Deserialize, Serialize};
use indexmap::IndexMap;
use syntax::structure::traits::Type;
use syntax::structure::visitor::Translate;
use syntax::structure::Modifier;
use syntax::util::translation::translate_fields;
use syntax::util::translation::{translate_iterable, Translatable};
use syntax::util::CompileError;
use syntax::SyntaxLevel;
use crate::function::HighFunction;

/// A type in the HIR
#[derive(Serialize, Deserialize)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub struct HighType<T: SyntaxLevel> {
    /// The reference to the type
    pub reference: T::TypeReference,
    /// The type's generics
    pub generics: IndexMap<Spur, Vec<T::TypeReference>>,
    /// The type's modifiers
    pub modifiers: Vec<Modifier>,
    /// The per-type data, such as fields, functions, etc...
    pub data: TypeData<T>,
}

impl<T: SyntaxLevel> Type<T::TypeReference> for HighType<T> {
    fn reference(&self) -> &T::TypeReference {
        &self.reference
    }
}

impl HighType<RawSyntaxLevel> {
    /// Creates an internal type
    pub fn internal(name: Spur) -> Self {
        Self {
            reference: RawTypeRef { path: vec![name], generics: vec![] },
            generics: IndexMap::default(),
            modifiers: vec![Modifier::PUBLIC],
            data: TypeData::Struct { fields: vec![] },
        }
    }
}

/// The data associated with a type, depending on what type it is
#[derive(Serialize, Deserialize)]
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
impl<'ctx, I: SyntaxLevel<Type = HighType<I>, Function = HighFunction<I>> + Translatable<I, HighSyntaxLevel>>
Translate<(), HirFunctionContext<'ctx>> for HighType<I>
{
    fn translate(&self, context: &mut HirFunctionContext<'_>) -> Result<(), CompileError> {
        let types = HighType::<HighSyntaxLevel> {
            reference: I::translate_type_ref(&self.reference, context)?,
            generics: self
                .generics
                .iter()
                .map(|(name, generics)| {
                    Ok::<_, CompileError>((
                        name.clone(),
                        translate_iterable(generics, context, I::translate_type_ref)?,
                    ))
                })
                .collect::<Result<IndexMap<_, _>, _>>()?,
            modifiers: self.modifiers.clone(),
            data: match &self.data {
                TypeData::Struct { fields } => TypeData::Struct {
                    fields: translate_fields(fields, context, I::translate_type_ref)?,
                },
                TypeData::Trait { .. } => return Ok(()),
            },
        };
        context.syntax.types.insert(types.reference.clone(), types);
        Ok(())
    }
}
