use crate::util::path::FilePath;
use crate::util::{collect_results, ParseError};
use crate::{Syntax, SyntaxLevel};

pub trait Translate<T, C, I: SyntaxLevel, O: SyntaxLevel> {
    fn translate(&self, context: &mut C) -> Result<T, ParseError>;
}

pub trait FileOwner {
    fn file(&self) -> &FilePath;

    fn set_file(&mut self, file: FilePath);
}

impl<C, I: SyntaxLevel, O: SyntaxLevel> Translate<Syntax<O>, C, I, O> for Syntax<I>
where
    I::Function: Translate<O::Function, C, I, O>,
    I::Type: Translate<O::Type, C, I, O>,
{
    fn translate(&self, context: &mut C) -> Result<Syntax<O>, ParseError> {
        let functions = collect_results(
            self.functions
                .iter()
                .map(|function| Translate::translate(function, context)),
        );

        let types = collect_results(
            self.types
                .iter()
                .map(|ty| Translate::translate(ty, context)),
        );

        match (functions, types) {
            (Ok(functions), Ok(types)) => Ok(Syntax {
                symbols: self.symbols.clone(),
                functions,
                types,
            }),
            (Err(functions), Err(types)) => Err(ParseError::MultiError(functions.into_iter().chain(types).collect())),
            (Err(functions), Ok(_)) => Err(ParseError::MultiError(functions)),
            (Ok(_), Err(types)) => Err(ParseError::MultiError(types)),
        }
    }
}
