use crate::structure::traits::{Function, Type};
use crate::util::translation::{Translatable, translate_vec};
use crate::util::{CompileError, Context};
use crate::{Syntax, SyntaxLevel};

/// Translates a type from an input type to an output type.
pub trait Translate<'a, T, C> {
    fn translate(&self, context: &'a mut C) -> Result<T, CompileError>;
}

impl<'a, C: Context<'a>, I: SyntaxLevel + Translatable<C::FunctionContext, I, O>, O: SyntaxLevel>
    Translate<'a, Syntax<O>, C> for Syntax<I>
{
    fn translate(&self, context: &'a mut C) -> Result<Syntax<O>, CompileError> {
        for function in &self.functions {
            I::translate_func(function, &mut context.function_context(function.file()))?;
        }

        /*let functions = translate_vec(&self.functions, context, |input, context| {
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
        })*/

        Ok(Syntax {
            symbols: self.symbols.clone(),
            functions: vec![],
            types: vec![],
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
