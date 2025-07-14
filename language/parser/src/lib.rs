use crate::errors::{print_err, ParserError};
use crate::file::parse_top_element;
use crate::util::ignored;
use anyhow::Error;
use async_recursion::async_recursion;
use hir::function::HighFunction;
use hir::types::HighType;
use hir::{create_syntax, RawSource, RawSyntaxLevel};
use lasso::{Spur, ThreadedRodeo};
use nom::multi::many1;
use nom::sequence::delimited;
use nom_locate::LocatedSpan;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use syntax::structure::Modifier;
use syntax::util::path::{get_path, FilePath};
use syntax::util::CompileError;
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
pub type IResult<'a, I, O, E = ParserError<'a>> = Result<(I, O), nom::Err<E>>;
/// A location in the source file and the parsing context
type Span<'a> = LocatedSpan<&'a str, ParseContext<'a>>;

/// Context used during parsing
#[derive(Debug, Clone)]
pub struct ParseContext<'a> {
    /// The interner used to intern strings
    pub interner: Arc<ThreadedRodeo>,
    /// The current file being parsed
    pub file: FilePath,
    /// The content of the file
    pub parsing: &'a str,
}

impl ParseContext<'_> {
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
        if function.modifiers.contains(&Modifier::OPERATION) {
            match function.parameters.len() {
                1 => source
                    .pre_unary_operations
                    .entry(function.reference.path.last().unwrap().clone())
                    .or_default()
                    .push(function.reference.path.clone().into()),
                2 => source
                    .binary_operations
                    .entry(function.reference.path.last().unwrap().clone())
                    .or_default()
                    .push(function.reference.path.clone().into()),
                _ => {
                    errors.push(CompileError::Basic(
                        "Expected operation to only have 1 or 2 args".to_string(),
                    ));
                }
            }
        }
        source.syntax.functions.insert(function.reference.clone(), function);
    }

    for types in file.types {
        source.syntax.types.insert(types.reference.clone(), types);
    }

    source.imports.insert(file_path, file.imports);
    errors
}

/// Parses a single file into a `File`.
pub async fn parse_file(
    path: &PathBuf,
    file_path: FilePath,
    interner: Arc<ThreadedRodeo>,
) -> Result<File, CompileError> {
    let parsing = fs::read_to_string(&path)
        .await
        .map_err(|err| CompileError::Internal(err.into()))?;

    let mut file = File::default();
    file.extend(
        many1(delimited(ignored, parse_top_element, ignored))(
            Span::new_extra(&parsing, ParseContext { interner, file: file_path, parsing: &parsing }))
            .map_err(|err| CompileError::Basic(format!("{}", print_err(&err).unwrap())))?.1);

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
