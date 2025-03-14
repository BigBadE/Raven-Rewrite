use anyhow::Error;
use thiserror::Error;

pub mod path;
pub mod translation;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Internal error:\n{0}")]
    InternalError(Error),
    #[error("{0}")]
    ParseError(String),
    #[error("{0:?}")]
    MultiError(Vec<ParseError>),
}

pub fn collect_results<T, E, I>(iter: I) -> Result<Vec<T>, Vec<E>>
where
    I: IntoIterator<Item = Result<T, E>>,
{
    iter.into_iter()
        .fold(Ok(Vec::new()), |acc, item| match (acc, item) {
            (Ok(mut oks), Ok(value)) => {
                oks.push(value);
                Ok(oks)
            }
            (Ok(_), Err(e)) => Err(vec![e]),
            (Err(errs), Ok(_)) => Err(errs),
            (Err(mut errs), Err(e)) => {
                errs.push(e);
                Err(errs)
            }
        })
}
