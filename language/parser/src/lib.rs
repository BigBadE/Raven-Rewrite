use crate::errors::{print_err, ParserError};
use crate::file::parse_top_element;
use crate::util::ignored;
use anyhow::Error;
use async_recursion::async_recursion;
use hir::function::HighFunction;
use hir::types::HighType;
use hir::{create_syntax, RawSource, RawSyntaxLevel};
use lasso::{Spur, ThreadedRodeo};
use nom::multi::many0;
use nom::sequence::preceded;
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
                1 => {
                    source
                        .pre_unary_operations
                        .entry(function.reference.path.last().unwrap().clone())
                        .or_default()
                        .push(function.reference.path.clone().into());
                },
                2 => {
                    source
                        .binary_operations
                        .entry(function.reference.path.last().unwrap().clone())
                        .or_default()
                        .push(function.reference.path.clone().into());
                },
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
    
    // Parse all top-level elements
    let (remaining, elements) = many0(preceded(ignored, parse_top_element))(
        Span::new_extra(&parsing, ParseContext { interner, file: file_path.clone(), parsing: &parsing }))
        .map_err(|err| {
            // Provide more detailed error information
            let error_msg = match print_err(&err) {
                Ok(msg) => msg,
                Err(_) => "Failed to parse file".to_string(),
            };
            
            // Add context about what might have been left unparsed
            match &err {
                nom::Err::Error(parser_err) | nom::Err::Failure(parser_err) => {
                    let remaining = parser_err.span.fragment();
                    if !remaining.trim().is_empty() {
                        let preview = remaining.chars().take(100).collect::<String>();
                        let line_info = format!("at line {}", parser_err.span.location_line());
                        CompileError::Basic(format!(
                            "Parse error {}: {}\nUnparsed content: {:?}",
                            line_info, error_msg, preview
                        ))
                    } else {
                        CompileError::Basic(error_msg)
                    }
                }
                _ => CompileError::Basic(error_msg),
            }
        })?;
    
    // Check if there's any meaningful unparsed content (ignoring trailing whitespace/comments)
    let remaining_after_ignored = match ignored(remaining.clone()) {
        Ok((remaining, _)) => remaining,
        Err(_) => remaining, // If ignored parsing fails, use original remaining
    };
    if !remaining_after_ignored.fragment().is_empty() {
        let preview = remaining_after_ignored.fragment().chars().take(100).collect::<String>();
        let line_info = format!("at line {}", remaining_after_ignored.location_line());
        
        return Err(CompileError::Basic(format!(
            "Parse error {}: Unexpected content after parsing completed\nUnparsed content: {:?}",
            line_info, preview
        )));
    }
    
    // Ensure we parsed at least one element
    if elements.is_empty() {
        return Err(CompileError::Basic("No valid top-level elements found in file".to_string()));
    }
    
    file.extend(elements);

    // Optional validation: warn if file seems to have incomplete parsing
    // This helps catch cases where parsing stops unexpectedly
    if parsing.contains("fn ") || parsing.contains("struct ") || parsing.contains("trait ") {
        let function_count = parsing.matches("fn ").count();
        let struct_count = parsing.matches("struct ").count(); 
        let trait_count = parsing.matches("trait ").count();
        let total_expected = function_count + struct_count + trait_count;
        let total_parsed = file.functions.len() + file.types.len();
        
        // Only warn in debug builds to avoid performance impact in release
        #[cfg(debug_assertions)]
        if total_parsed < total_expected {
            eprintln!(
                "Warning: Possible incomplete parsing in {:?}. Expected ~{} elements, parsed {}",
                file_path, total_expected, total_parsed
            );
        }
    }

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
