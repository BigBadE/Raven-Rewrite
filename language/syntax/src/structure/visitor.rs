use crate::structure::FileOwner;
use crate::util::translation::{translate_vec, Translatable};
use crate::util::ParseError;
use crate::{Syntax, SyntaxLevel};

pub trait Translate<T, C, I: SyntaxLevel, O: SyntaxLevel> {
    fn translate(&self, context: &mut C) -> Result<T, ParseError>;
}

impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<Syntax<O>, C, I, O> for Syntax<I>
{
    fn translate(&self, context: &mut C) -> Result<Syntax<O>, ParseError> {
        let functions = translate_vec(&self.functions, context, I::translate_func);

        let types = translate_vec(&self.types, context, I::translate_type);

        let (functions, types) = merge_result(functions, types)?;

        Ok(Syntax {
            symbols: self.symbols.clone(),
            functions,
            types: types.into_iter().filter_map(|ty| ty).collect(),
        })
    }
}

pub fn merge_result<A, B>(
    first: Result<A, ParseError>,
    second: Result<B, ParseError>,
) -> Result<(A, B), ParseError> {
    match (first, second) {
        (Err(functions), Err(types)) => Err(ParseError::MultiError(vec![functions, types])),
        (first, second) => Ok((first?, second?)),
    }
}
