use anyhow::Error;
use thiserror::Error;

pub mod path;
pub mod translation;

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
