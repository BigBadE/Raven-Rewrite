use crate::util::path::FilePath;
use crate::{ContextSyntaxLevel, SyntaxLevel};
use anyhow::Error;
use owo_colors::OwoColorize;
use std::fmt;

/// Utility functions for paths
pub mod path;
/// Utility functions for translation
pub mod translation;
/// Pretty printing utilities that resolve Spurs to actual strings
pub mod pretty_print;

/// A trait for handling translation contexts
pub trait Context<I: SyntaxLevel, O: ContextSyntaxLevel<I>> {
    /// Creates a function context
    fn function_context(&mut self, function: &I::Function) -> Result<O::InnerContext<'_>, CompileError>;

    /// Creates a type context
    fn type_context(&mut self, types: &I::Type) -> Result<O::InnerContext<'_>, CompileError>;
}

/// A trait for all objects that have a file associated with them
pub trait FileOwner {
    /// The file that this object is associated with
    fn file(&self) -> &FilePath;

    /// Set the file that this object is associated with
    fn set_file(&mut self, file: FilePath);
}

/// An error raised in the compilation process
#[derive(Debug)]
pub enum CompileError {
    Internal(Error),
    Basic(String),
    Multi(Vec<CompileError>),
}

impl From<fmt::Error> for CompileError {
    fn from(err: fmt::Error) -> Self {
        CompileError::Internal(err.into())
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompileError::Internal(err) => write!(f, "{}\n{}", "Internal error:".red(), err.to_string().red()),
            CompileError::Basic(msg) => write!(f, "\n{}", msg.red()),
            CompileError::Multi(errors) => {
                writeln!(f)?;
                for (i, error) in errors.iter().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "{}", error)?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for CompileError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            CompileError::Internal(err) => Some(err.as_ref()),
            CompileError::Basic(_) => None,
            CompileError::Multi(_) => None,
        }
    }
}

impl CompileError {
    /// Prints out a compiler error
    pub fn print(&self) {
        match self {
            CompileError::Basic(_) | CompileError::Internal(_) => {
                println!("{}", self);
            }
            CompileError::Multi(errors) => {
                for error in errors {
                    error.print();
                }
            }
        }
    }
}
