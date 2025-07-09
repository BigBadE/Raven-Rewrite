use crate::errors::error_message;
use crate::file::parse_top_element;
use crate::util::ignored;
use anyhow::Error;
use async_recursion::async_recursion;
use hir::function::HighFunction;
use hir::types::HighType;
use hir::{RawSource, RawSyntaxLevel, create_syntax};
use lasso::{Spur, ThreadedRodeo};
use nom::combinator::eof;
use nom_locate::LocatedSpan;
use nom_supreme::ParserExt;
use nom_supreme::error::ErrorTree;
use nom_supreme::final_parser::final_parser;
use nom_supreme::multi::collect_separated_terminated;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use syntax::structure::Modifier;
use syntax::structure::literal::TYPES;
use syntax::util::CompileError;
use syntax::util::path::{FilePath, get_path};
use syntax::{GenericFunctionRef, GenericTypeRef};
use tokio::fs;

/// Parses blocks of code
mod code;
/// Handles errors
mod errors;
/// Parses expressions
mod expressions;
/// Parses a file
mod file;
/// Parses a function
mod function;
/// Parses statements
mod statements;
/// Parses structures
mod structure;
/// Utility parsing functions
mod util;

/// Keeps track of the parsing location, the function output, and any error that arises
pub type IResult<I, O, E = ErrorTree<I>> = Result<(I, O), nom::Err<E>>;
/// A location in the source file and the parsing context
type Span<'a> = LocatedSpan<&'a str, ParseContext>;

/// Context used during parsing
#[derive(Clone)]
pub struct ParseContext {
    /// The interner used to intern strings
    pub interner: Arc<ThreadedRodeo>,
    /// The current file being parsed
    pub file: FilePath,
}

impl ParseContext {
    /// Interns a string using the interner
    pub fn intern<T: AsRef<str>>(&self, string: T) -> Spur {
        self.interner.get_or_intern(string)
    }
}

/// A parsed file
#[derive(Default)]
pub struct File {
    /// The file's imports
    pub imports: Vec<FilePath>,
    /// The functions in the file
    pub functions: Vec<HighFunction<RawSyntaxLevel>>,
    /// The types in the file
    pub types: Vec<HighType<RawSyntaxLevel>>,
}

/// A top level item, used to handle the different possible return types
pub enum TopLevelItem {
    /// A function
    Function(HighFunction<RawSyntaxLevel>),
    /// A type
    Type(HighType<RawSyntaxLevel>),
    /// An import
    Import(FilePath),
}

impl Extend<TopLevelItem> for File {
    fn extend<T: IntoIterator<Item=TopLevelItem>>(&mut self, iter: T) {
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
pub async fn parse_source(dir: PathBuf) -> Result<RawSource, CompileError> {
    let syntax = create_syntax();
    let mut source = RawSource {
        imports: HashMap::default(),
        types: TYPES
            .iter()
            .enumerate()
            .map(|(id, name)| (vec![syntax.symbols.get_or_intern(name)],
                               GenericTypeRef::Struct { reference: id, generics: vec![] }))
            .collect(),
        functions: HashMap::default(),
        pre_unary_operations: HashMap::default(),
        post_unary_operations: HashMap::default(),
        binary_operations: HashMap::default(),
        syntax,
    };
    let mut errors = Vec::new();
    for path in read_recursive(&dir)
        .await
        .map_err(|err| CompileError::Internal(err))?
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
        errors.append(&mut add_file_to_syntax(&mut source, file, file_path));
    }

    if !errors.is_empty() {
        return Err(CompileError::Multi(errors));
    }

    Ok(source)
}

fn add_file_to_syntax(
    source: &mut RawSource,
    file: File,
    file_path: FilePath,
) -> Vec<CompileError> {
    let mut errors = Vec::new();

    // Add the functions to the output
    for function in file.functions {
        let mut path = file_path.clone();
        path.push(function.name);
        let reference = GenericFunctionRef { reference: source.syntax.functions.len(), generics: vec![] };
        if function.modifiers.contains(&Modifier::OPERATION) {
            match function.parameters.len() {
                1 => source
                    .pre_unary_operations
                    .entry(function.name)
                    .or_default()
                    .push(reference.clone()),
                2 => source
                    .binary_operations
                    .entry(function.name)
                    .or_default()
                    .push(reference.clone()),
                _ => {
                    errors.push(CompileError::Basic(
                        "Expected operation to only have 1 or 2 args".to_string(),
                    ));
                }
            }
        }
        source.functions.insert(path, reference);
        source.syntax.functions.push(function);
    }

    for types in file.types {
        let mut path = file_path.clone();
        path.push(types.name);
        source
            .types
            .insert(path, GenericTypeRef::Struct { reference: source.syntax.types.len(), generics: vec![] });
        source.syntax.types.push(types);
    }

    source.imports.insert(file_path, file.imports);
    errors
}

/// Parses a single file into a `File`.
pub async fn parse_file(
    path: &PathBuf,
    file: FilePath,
    interner: Arc<ThreadedRodeo>,
) -> Result<File, CompileError> {
    let parsing = fs::read_to_string(&path)
        .await
        .map_err(|err| CompileError::Internal(err.into()))?;

    let file = final_parser(
        collect_separated_terminated(parse_top_element, ignored, eof).context("Ignored"),
    )(Span::new_extra(&parsing, ParseContext { interner, file }))
        .map_err(|err| CompileError::Basic(error_message(err)))?;

    Ok(file)
}

/// Recursively reads a directory from the path.
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
