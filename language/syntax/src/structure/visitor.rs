use crate::structure::traits::{Function, Type};
use crate::util::translation::{translate_vec, Translatable};
use crate::util::{CompileError, Context};
use crate::{ContextSyntaxLevel, Syntax, SyntaxLevel};

/// Translates a type from an input type to an output type.
pub trait Translate<T, C> {
    fn translate(&self, context: &mut C) -> Result<T, CompileError>;
}

impl<'ctx, I: SyntaxLevel + Translatable<I, O>, O: ContextSyntaxLevel>
    Translate<Syntax<O>, O::Context<'ctx>> for Syntax<I>
{
    fn translate(&self, context: &mut O::Context<'_>) -> Result<Syntax<O>, CompileError> {
        let functions = translate_vec(&self.functions, context, |input, context| {
            I::translate_func(input, &mut context.function_context(input.file()))
        });

        let types = translate_vec(&self.types, context, |input, context| {
            I::translate_type(input, &mut context.function_context(input.file()))
        });

        let (functions, types) = merge_result(functions, types)?;

        Ok(Syntax {
            symbols: self.symbols.clone(),
            functions,
            types: types.into_iter().flatten().collect(),
        })
    }
}

/// Merges two possible compiler errors into one using the Multi variant.
pub fn merge_result<A, B>(
    first: Result<A, CompileError>,
    second: Result<B, CompileError>,
) -> Result<(A, B), CompileError> {
    match (first, second) {
        (Err(functions), Err(types)) => Err(CompileError::Multi(vec![functions, types])),
        (first, second) => Ok((first?, second?)),
    }
}
