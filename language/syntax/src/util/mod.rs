use anyhow::Error;
use thiserror::Error;
use crate::util::path::FilePath;

/// Utility functions for paths
pub mod path;
/// Utility functions for translation
pub mod translation;

/// A trait for handling translation contexts
pub trait Context<'a> {
    type FunctionContext;

    /// Creates a function context
    fn function_context(&'a mut self, file: &FilePath) -> Self::FunctionContext;
}

/// A trait for all objects that have a file associated with them
pub trait FileOwner {
    /// The file that this object is associated with
    fn file(&self) -> &FilePath;

    /// Set the file that this object is associated with
    fn set_file(&mut self, file: FilePath);
}

/// An error raised in the compilation process
#[derive(Error, Debug)]
pub enum CompileError {
    #[error("Internal error:\n{0}")]
    Internal(Error),
    #[error("{0}")]
    Basic(String),
    #[error("{0:?}")]
    Multi(Vec<CompileError>),
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
