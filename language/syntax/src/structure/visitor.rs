use crate::structure::traits::{Function, Type};
use crate::util::translation::{translate_iterable, Translatable};
use crate::util::{CompileError, Context};
use crate::{ContextSyntaxLevel, Syntax, SyntaxLevel};

/// Translates a type from an input type to an output type.
pub trait Translate<T, C> {
    fn translate(&self, context: &mut C) -> Result<T, CompileError>;
}

impl<'ctx, I: SyntaxLevel + Translatable<I, O>, O: ContextSyntaxLevel<I>>
Translate<Syntax<O>, O::Context<'ctx>> for Syntax<I>
{
    fn translate(&self, context: &mut O::Context<'_>) -> Result<Syntax<O>, CompileError> {
        let functions =
            translate_iterable(&self.functions, context,
                               |(_, input), context| {
                                   let func = I::translate_func(input, &mut context.function_context(input)?)?;
                                   Ok(func.into_iter().map(|func| (func.reference().clone(), func)))
                               });

        let types =
            translate_iterable(&self.types, context,
                               |(_, input), context| {
                                   let types = I::translate_type(input, &mut context.type_context(input)?)?;
                                   Ok(types.into_iter().map(|types| (types.reference().clone(), types)))
                               });

        let (functions, types) =
            merge_result::<Vec<_>, Vec<_>>(functions, types)?;

        Ok(Syntax {
            symbols: self.symbols.clone(),
            functions: functions.into_iter().flatten().collect(),
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
