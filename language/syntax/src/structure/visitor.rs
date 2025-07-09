use std::marker::PhantomData;
use crate::util::translation::{translate_iterable, Translatable};
use crate::util::{CompileError, Context};
use crate::{ContextSyntaxLevel, Syntax, SyntaxLevel};

/// Translates a type from an input type to an output type.
pub trait Translate<T, C> {
    fn translate(&self, context: &mut C) -> Result<T, CompileError>;
}

impl<'ctx, I: SyntaxLevel + Translatable<I, O>, O: ContextSyntaxLevel<I>>
Translate<PhantomData<O>, O::Context<'ctx>> for Syntax<I>
{
    fn translate(&self, context: &mut O::Context<'_>) -> Result<PhantomData<O>, CompileError> {
        let functions =
            translate_iterable(&self.functions, context,
                               |(_, input), context| {
                                   I::translate_func(input, &mut context.function_context(input)?)?;
                                   Ok(())
                               });

        let types =
            translate_iterable(&self.types, context,
                               |(_, input), context| {
                                   I::translate_type(input, &mut context.type_context(input)?)?;
                                   Ok(())
                               });

        merge_result::<Vec<_>, Vec<_>>(functions, types)?;
        Ok(PhantomData::default())
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
