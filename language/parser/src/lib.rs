use crate::errors::error_message;
use crate::file::parse_top_element;
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
use nom::combinator::eof;
use nom_supreme::ParserExt;
use syntax::hir::types::Type;
use syntax::hir::RawSource;
use syntax::structure::function::RawFunction;
use syntax::util::path::{get_path, FilePath};
use syntax::util::ParseError;
use tokio::fs;

mod code;
mod errors;
mod expressions;
mod function;
mod statements;
mod util;
mod file;
mod structure;

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

#[derive(Default)]
pub struct File {
    pub imports: Vec<FilePath>,
    pub functions: Vec<RawFunction>,
    pub types: Vec<Type<Spur>>,
}

pub enum TopLevelItem {
    Function(RawFunction),
    Type(Type<Spur>),
    Import(FilePath),
}

impl Extend<TopLevelItem> for File {
    fn extend<T: IntoIterator<Item=TopLevelItem>>(&mut self, iter: T) {
        for item in iter {
            match item {
                TopLevelItem::Function(function) => {
                    self.functions.push(function);
                },
                TopLevelItem::Import(path) => {
                    self.imports.push(path);
                },
                TopLevelItem::Type(types) => {
                    self.types.push(types)
                }
            }
        }
    }
}

pub async fn parse_source(dir: PathBuf) -> Result<RawSource, Vec<ParseError>> {
    let mut source = RawSource::default();
    let mut errors = Vec::new();

    for path in read_recursive(&dir).await.map_err(|err| vec!(ParseError::InternalError(err)))? {
        let file_path = get_path(&source.syntax.symbols, &path, &dir);
        let file = match parse_file(&path, file_path.clone(), source.syntax.symbols.clone()).await {
            Ok(file) => file,
            Err(err) => {
                errors.push(err);
                continue;
            }
        };
        
        for function in file.functions {
            let mut path = file_path.clone();
            path.push(function.name);
            source.functions.insert(path, source.syntax.functions.len());
            source.syntax.functions.push(function);
        }
        
        for types in file.types {
            let mut path = file_path.clone();
            path.push(types.name);
            source.types.insert(path, source.syntax.types.len());
            source.syntax.types.push(types);
        }
        
        source.imports.insert(file_path, file.imports);
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    Ok(source)
}

pub async fn parse_file(path: &PathBuf, file: FilePath, interner: Arc<ThreadedRodeo>) -> Result<File, ParseError> {
    let parsing = fs::read_to_string(&path).await.map_err(|err| ParseError::InternalError(err.into()))?;

    let file =
        final_parser(collect_separated_terminated(parse_top_element, ignored, eof).context("Top"))(Span::new_extra(&parsing, ParseContext {
            interner,
            file
        })).map_err(|err| ParseError::ParseError(error_message(err)))?;

    Ok(file)
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