use crate::structure::FileOwner;
use crate::util::CompileError;
use crate::util::translation::{Translatable, translate_vec};
use crate::{Syntax, SyntaxLevel};

/// Translates a type from an input type to an output type.
pub trait Translate<T, C> {
    fn translate(&self, context: &mut C) -> Result<T, CompileError>;
}

impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel> Translate<Syntax<O>, C>
    for Syntax<I>
{
    fn translate(&self, context: &mut C) -> Result<Syntax<O>, CompileError> {
        let functions = translate_vec(&self.functions, context, I::translate_func);

        let types = translate_vec(&self.types, context, I::translate_type);

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
