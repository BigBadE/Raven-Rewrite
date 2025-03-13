use crate::util::path::FilePath;
use crate::util::{collect_results, ParseError};
use crate::{Syntax, SyntaxLevel};
use crate::util::translation::Translatable;

pub trait Translate<T, C, I: SyntaxLevel, O: SyntaxLevel> {
    fn translate(&self, context: &mut C) -> Result<T, ParseError>;
}

pub trait FileOwner {
    fn file(&self) -> &FilePath;

    fn set_file(&mut self, file: FilePath);
}

impl<C, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel> Translate<Syntax<O>, C, I, O> for Syntax<I> {
    fn translate(&self, context: &mut C) -> Result<Syntax<O>, ParseError> {
        let functions = collect_results(
            self.functions
                .iter()
                .map(|function| I::translate_func(function, context)),
        );

        let types = collect_results(
            self.types
                .iter()
                .map(|ty| I::translate_type(ty, context)),
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
