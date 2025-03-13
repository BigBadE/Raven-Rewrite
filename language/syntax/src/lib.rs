use crate::hir::types::{Type, TypeReference};
use lasso::ThreadedRodeo;
use std::fmt::Debug;
use std::sync::Arc;
use crate::hir::expression::Expression;
use crate::hir::function::{Function, FunctionReference};
use crate::hir::statement::Statement;

pub mod code;
pub mod structure;
pub mod hir;
pub mod util;
pub mod mir;

pub type TypeRef = usize;
pub type FunctionRef = usize;

pub trait SyntaxLevel: Debug {
    type TypeReference: TypeReference;
    type Type: Type;
    type FunctionReference: FunctionReference;
    type Function: Function;
    type Statement: Statement;
    type Expression: Expression;
}

pub struct Syntax<T: SyntaxLevel> {
    pub symbols: Arc<ThreadedRodeo>,
    pub functions: Vec<T::Function>,
    pub types: Vec<T::Type>
}

impl<T: SyntaxLevel> Default for Syntax<T> {
    fn default() -> Self {
        Self {
            symbols: Arc::default(),
            functions: Vec::default(),
            types: Vec::default()
        }
    }
}