use crate::structure::traits::{
    Expression, Function, FunctionReference, Statement, Terminator, Type, TypeReference,
};
use crate::structure::visitor::Translate;
use crate::util::CompileError;
use lasso::ThreadedRodeo;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::sync::Arc;

/// The structure of the program in memory
pub mod structure;
/// Various utility functions
pub mod util;

/// A reference to a specific type
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeRef(pub usize);
impl TypeReference for TypeRef {}

/// A reference to a specific function
#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionRef(pub usize);
impl FunctionReference for FunctionRef {}

/// A level of syntax. As the program is compiled, it goes lower until it hits the lowest level.
/// Associated traits are used to keep track of exactly what the data structure is at each level
/// and allow the same transformations to be used on multiple levels.
pub trait SyntaxLevel: Serialize + for<'a> Deserialize<'a> + Debug {
    type TypeReference: TypeReference;
    type Type: Type;
    type FunctionReference: FunctionReference;
    type Function: Function;
    type Statement: Statement;
    type Expression: Expression;
    type Terminator: Terminator;
}

/// The syntax of the program, used to
#[derive(Serialize, Deserialize)]
pub struct Syntax<T: SyntaxLevel> {
    /// The symbol table
    pub symbols: Arc<ThreadedRodeo>,
    /// The program's functions
    pub functions: Vec<T::Function>,
    /// The program's types
    pub types: Vec<T::Type>,
}

impl<C> Translate<TypeRef, C> for TypeRef {
    fn translate(&self, _context: &mut C) -> Result<TypeRef, CompileError> {
        Ok(*self)
    }
}

impl<C> Translate<FunctionRef, C> for FunctionRef {
    fn translate(&self, _context: &mut C) -> Result<FunctionRef, CompileError> {
        Ok(*self)
    }
}
