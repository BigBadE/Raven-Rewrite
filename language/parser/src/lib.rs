use crate::errors::error_message;
use crate::file::parse_top_element;
use crate::util::ignored;
use anyhow::Error;
use async_recursion::async_recursion;
use hir::function::HighFunction;
use hir::types::HighType;
use hir::{create_syntax, RawSource, RawSyntaxLevel};
use lasso::{Spur, ThreadedRodeo};
use nom::combinator::eof;
use nom_locate::LocatedSpan;
use nom_supreme::error::ErrorTree;
use nom_supreme::final_parser::final_parser;
use nom_supreme::multi::collect_separated_terminated;
use nom_supreme::ParserExt;
use std::path::PathBuf;
use std::sync::Arc;
use syntax::structure::Modifier;
use syntax::util::path::{get_path, FilePath};
use syntax::util::ParseError;
use syntax::{FunctionRef, TypeRef};
use tokio::fs;

mod code;
mod errors;
mod expressions;
mod file;
mod function;
mod statements;
mod structure;
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

#[derive(Default)]
pub struct File {
    pub imports: Vec<FilePath>,
    pub functions: Vec<HighFunction<RawSyntaxLevel>>,
    pub types: Vec<HighType<RawSyntaxLevel>>,
}

pub enum TopLevelItem {
    Function(HighFunction<RawSyntaxLevel>),
    Type(HighType<RawSyntaxLevel>),
    Import(FilePath),
}

impl Extend<TopLevelItem> for File {
    fn extend<T: IntoIterator<Item = TopLevelItem>>(&mut self, iter: T) {
        for item in iter {
            match item {
                TopLevelItem::Function(function) => {
                    self.functions.push(function);
                }
                TopLevelItem::Import(path) => {
                    self.imports.push(path);
                }
                TopLevelItem::Type(types) => self.types.push(types),
            }
        }
    }
}

/// Parses a source directory into a `RawSource`.
pub async fn parse_source(dir: PathBuf) -> Result<RawSource, ParseError> {
    let mut source = RawSource {
        syntax: create_syntax(),
        imports: Default::default(),
        types: Default::default(),
        functions: Default::default(),
        pre_unary_operations: Default::default(),
        post_unary_operations: Default::default(),
        binary_operations: Default::default(),
    };
    let mut errors = Vec::new();

    for path in read_recursive(&dir)
        .await
        .map_err(|err| ParseError::InternalError(err))?
    {
        // Parse a single file
        let file_path = get_path(&source.syntax.symbols, &path, &dir);
        let file = match parse_file(&path, file_path.clone(), source.syntax.symbols.clone()).await {
            Ok(file) => file,
            Err(err) => {
                errors.push(err);
                continue;
            }
        };

        // Add the functions to the output
        for function in file.functions {
            let mut path = file_path.clone();
            path.push(function.name);
            let reference = FunctionRef(source.syntax.functions.len());
            if function.modifiers.contains(&Modifier::OPERATION) {
                match function.parameters.len() {
                    1 => source.pre_unary_operations.entry(function.name).or_default().push(reference),
                    2 => source.binary_operations.entry(function.name).or_default().push(reference),
                    _ => return Err(ParseError::ParseError("Expected operation to only have 1 or 2 args".to_string()))
                }
            }
            source.functions.insert(path, reference);
            source.syntax.functions.push(function);
        }

        for types in file.types {
            let mut path = file_path.clone();
            path.push(types.name);
            source.types.insert(path, TypeRef(source.syntax.types.len()));
            source.syntax.types.push(types);
        }

        source.imports.insert(file_path, file.imports);
    }

    if !errors.is_empty() {
        return Err(ParseError::MultiError(errors));
    }

    Ok(source)
}

pub async fn parse_file(
    path: &PathBuf,
    file: FilePath,
    interner: Arc<ThreadedRodeo>,
) -> Result<File, ParseError> {
    let parsing = fs::read_to_string(&path)
        .await
        .map_err(|err| ParseError::InternalError(err.into()))?;

    let file = final_parser(
        collect_separated_terminated(parse_top_element, ignored, eof).context("Ignored"),
    )(Span::new_extra(&parsing, ParseContext { interner, file }))
    .map_err(|err| ParseError::ParseError(error_message(err)))?;

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
