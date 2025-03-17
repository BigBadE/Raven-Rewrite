use crate::hir::expression::Expression;
use crate::hir::function::{Function, FunctionReference, Terminator};
use crate::hir::statement::Statement;
use crate::hir::types::{Type, TypeReference};
use crate::structure::visitor::Translate;
use crate::util::ParseError;
use lasso::ThreadedRodeo;
use std::fmt::Debug;
use std::sync::Arc;

pub mod code;
pub mod hir;
pub mod mir;
pub mod structure;
pub mod util;

#[derive(Debug, Copy, Clone)]
pub struct TypeRef(pub usize);

#[derive(Debug, Copy, Clone)]
pub struct FunctionRef(pub usize);

pub trait SyntaxLevel: Debug {
    type TypeReference: TypeReference;
    type Type: Type;
    type FunctionReference: FunctionReference;
    type Function: Function;
    type Statement: Statement;
    type Expression: Expression;
    type Terminator: Terminator;
}

pub struct Syntax<T: SyntaxLevel> {
    pub symbols: Arc<ThreadedRodeo>,
    pub functions: Vec<T::Function>,
    pub types: Vec<T::Type>,
}

impl<T: SyntaxLevel> Default for Syntax<T> {
    fn default() -> Self {
        Self {
            symbols: Arc::default(),
            functions: Vec::default(),
            types: Vec::default(),
        }
    }
}

impl<C, I: SyntaxLevel, O: SyntaxLevel> Translate<TypeRef, C, I, O> for TypeRef {
    fn translate(&self, _context: &mut C) -> Result<TypeRef, ParseError> {
        Ok(*self)
    }
}

impl<C, I: SyntaxLevel, O: SyntaxLevel> Translate<FunctionRef, C, I, O> for FunctionRef {
    fn translate(&self, _context: &mut C) -> Result<FunctionRef, ParseError> {
        Ok(*self)
    }
}