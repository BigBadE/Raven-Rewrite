use crate::structure::visitor::Translate;
use crate::util::ParseError;
use lasso::ThreadedRodeo;
use std::fmt::Debug;
use std::sync::Arc;
use serde::{Deserialize, Serialize};
use crate::structure::traits::{Expression, Function, FunctionReference, Statement, Terminator, Type, TypeReference};

pub mod structure;
pub mod util;

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeRef(pub usize);
impl TypeReference for TypeRef {}

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionRef(pub usize);
impl FunctionReference for FunctionRef {}

pub trait SyntaxLevel: Serialize + for<'a> Deserialize<'a> + Debug {
    type TypeReference: TypeReference;
    type Type: Type;
    type FunctionReference: FunctionReference;
    type Function: Function;
    type Statement: Statement;
    type Expression: Expression;
    type Terminator: Terminator;
}

#[derive(Serialize, Deserialize)]
pub struct Syntax<T: SyntaxLevel> {
    pub symbols: Arc<ThreadedRodeo>,
    pub functions: Vec<T::Function>,
    pub types: Vec<T::Type>,
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
