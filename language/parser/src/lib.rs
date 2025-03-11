use crate::errors::error_message;
use crate::function::parse_function;
use crate::util::ignored;
use anyhow::Error;
use async_recursion::async_recursion;
use lasso::{Spur, ThreadedRodeo};
use nom_locate::LocatedSpan;
use nom_supreme::error::ErrorTree;
use nom_supreme::final_parser::final_parser;
use nom_supreme::multi::collect_separated_terminated;
use std::path::PathBuf;
use std::sync::Arc;
use syntax::hir::RawSource;
use syntax::structure::function::RawFunction;
use syntax::util::path::{get_path, FilePath};
use thiserror::Error;
use tokio::fs;

mod code;
mod errors;
mod expressions;
mod function;
mod statements;
mod util;

pub type IResult<I, O, E = ErrorTree<I>> = Result<(I, O), nom::Err<E>>;
type Span<'a> = LocatedSpan<&'a str, ParseContext>;

#[derive(Clone)]
pub struct ParseContext {
    pub interner: Arc<ThreadedRodeo>,
    pub file: FilePath,
}

impl ParseContext {
    pub fn intern<T: AsRef<str>>(&self, string: T) -> Spur {
        self.interner.get_or_intern(string)
    }
}

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Internal error")]
    InternalError(Error),
    #[error("Parse error")]
    ParseError(String),
}

pub struct File {
    pub imports: Vec<FilePath>,
    pub functions: Vec<RawFunction>,
}

pub async fn parse_source(dir: PathBuf) -> Result<RawSource, ParseError> {
    let mut source = RawSource::default();
    let mut errors = Vec::new();

    for path in read_recursive(&dir).await.map_err(|err| ParseError::InternalError(err))? {
        let file_path = get_path(&source.syntax.symbols, &dir, &path);
        let file = match parse_file(&path, file_path.clone(), source.syntax.symbols.clone()).await {
            Ok(file) => file,
            Err(ParseError::ParseError(err)) => {
                errors.push(err);
                continue;
            },
            Err(err) => return Err(err)
        };
        for function in file.functions {
            source.syntax.functions.push(function);
        }
        source.imports.insert(file_path,
        file.imports);
    }

    if !errors.is_empty() {
        return Err(ParseError::ParseError(errors.join("\n")));
    }

    Ok(source)
}

pub async fn parse_file(path: &PathBuf, file: FilePath, interner: Arc<ThreadedRodeo>) -> Result<File, ParseError> {
    let parsing = fs::read_to_string(&path).await.map_err(|err| ParseError::InternalError(err.into()))?;

    let functions =
        match final_parser(collect_separated_terminated(parse_function, ignored, ignored))(Span::new_extra(&parsing, ParseContext {
            interner,
            file
        })) {
            Ok(functions) => functions,
            Err(errors) => {
                return Err(ParseError::ParseError(error_message(errors)))
            }
        };

    Ok(File {
        imports: vec![],
        functions,
    })
}

#[async_recursion]
pub async fn read_recursive(dir: &PathBuf) -> Result<Vec<PathBuf>, Error> {
    let metadata = fs::metadata(&dir).await?;
    let mut output = Vec::new();
    if metadata.is_dir() {
        let mut iter = fs::read_dir(dir).await?;
        while let Some(entry) = iter.next_entry().await? {
            output.append(&mut read_recursive(&entry.path()).await?);
        }
    } else {
        output.push(dir.clone());
    }
    Ok(output)
}