use crate::{HighSyntaxLevel, HirFunctionContext};
use lasso::Spur;
use serde::{Deserialize, Serialize};
use indexmap::IndexMap;
use syntax::structure::visitor::Translate;
use syntax::structure::Modifier;
use syntax::util::translation::{translate_iterable, Translatable};
use syntax::util::CompileError;
use syntax::{SyntaxLevel, GenericTypeRef};
use crate::function::HighFunction;

/// An impl block in the HIR
#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub struct HighImpl<T: SyntaxLevel> {
    /// The type being implemented for
    pub target_type: T::TypeReference,
    /// The impl block's generics
    pub generics: IndexMap<Spur, Vec<T::TypeReference>>,
    /// The impl block's modifiers
    pub modifiers: Vec<Modifier>,
    /// The functions implemented in this impl block
    pub functions: Vec<T::Function>,
}

// Handle impl block translations
impl<'ctx, I: SyntaxLevel<Type = crate::types::HighType<I>, Function = HighFunction<I>> + Translatable<I, HighSyntaxLevel>>
Translate<(), HirFunctionContext<'ctx>> for HighImpl<I>
{
    fn translate(&self, context: &mut HirFunctionContext<'_>) -> Result<(), CompileError> {
        // Validate target type translation
        let _target_type = I::translate_type_ref(&self.target_type, context)?;
        
        // Validate generics translation
        let _generics: IndexMap<Spur, Vec<GenericTypeRef>> = self
            .generics
            .iter()
            .map(|(name, generics)| {
                Ok::<_, CompileError>((
                    name.clone(),
                    translate_iterable(generics, context, I::translate_type_ref)?,
                ))
            })
            .collect::<Result<IndexMap<Spur, Vec<GenericTypeRef>>, _>>()?;
        
        // Translate all functions in the impl block by adding them to the syntax
        for function in &self.functions {
            I::translate_func(function, context)?;
        }
        
        // For now, we'll just validate the translation worked
        // TODO: Add proper impl block storage in syntax
        Ok(())
    }
}