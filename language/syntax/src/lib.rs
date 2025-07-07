use crate::structure::traits::{
    Expression, Function, FunctionReference, Statement, Terminator, Type, TypeReference,
};
use crate::structure::visitor::Translate;
use crate::util::{CompileError, Context};
use lasso::ThreadedRodeo;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::sync::Arc;

/// The structure of the program in memory
pub mod structure;
/// Various utility functions
pub mod util;

/// A reference to a specific type
#[derive(Debug, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub enum GenericTypeRef {
    Struct {
        /// The reference to the type
        reference: usize,
        /// The generic constraints of the type
        generics: Vec<GenericTypeRef>,
    },
    Generic {
        /// The reference to the generic
        reference: usize,
    },
}

impl TypeReference for GenericTypeRef {}

/// A reference to a specific type
pub type TypeRef = usize;

impl TypeReference for TypeRef {}

/// A reference to a specific function
#[derive(Debug, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionRef {
    /// The reference to the function
    pub reference: usize,
    /// The generic constraints of the function
    pub generics: Vec<GenericTypeRef>,
}
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

/// A SyntaxLevel that also contains a context type for translation.
pub trait ContextSyntaxLevel<I: SyntaxLevel>: SyntaxLevel {
    type Context<'ctx>: Context<I, Self>;
    type InnerContext<'ctx>;
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

impl<C> Translate<FunctionRef, C> for FunctionRef {
    fn translate(&self, _context: &mut C) -> Result<FunctionRef, CompileError> {
        Ok(self.clone())
    }
}
