use std::collections::HashMap;
use std::fmt;
use crate::structure::traits::{
    Expression, Function, FunctionReference, Statement, Terminator, Type, TypeReference,
};
use crate::structure::visitor::Translate;
use crate::util::{CompileError, Context};
use lasso::ThreadedRodeo;
use serde::{Deserialize, Serialize};
use std::fmt::{Debug, Write};
use std::sync::Arc;
use crate::util::path::FilePath;
use crate::util::pretty_print::{write_generics, PrettyPrint};

/// The structure of the program in memory
pub mod structure;
/// Various utility functions
pub mod util;

/// A reference to a specific type
#[derive(Debug, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub enum GenericTypeRef {
    Struct {
        /// The reference to the type
        reference: TypeRef,
        /// The generic constraints of the type
        generics: Vec<GenericTypeRef>,
    },
    Generic {
        /// The reference to the generic in the function context
        reference: TypeRef,
    },
}

impl TypeReference for GenericTypeRef {}

/// A reference to a specific type
pub type TypeRef = FilePath;

impl TypeReference for TypeRef {}

/// A reference to a specific function
#[derive(Debug, Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenericFunctionRef {
    /// The reference to the function
    pub reference: FunctionRef,
    /// The generic constraints of the function
    pub generics: Vec<GenericTypeRef>,
}

impl FunctionReference for GenericFunctionRef {}

pub type FunctionRef = FilePath;

impl FunctionReference for FunctionRef {}

/// A level of syntax. As the program is compiled, it goes lower until it hits the lowest level.
/// Associated traits are used to keep track of exactly what the data structure is at each level
/// and allow the same transformations to be used on multiple levels.
pub trait SyntaxLevel: Serialize + for<'a> Deserialize<'a> + Debug {
    type TypeReference: TypeReference;
    type Type: Type<Self::TypeReference>;
    type FunctionReference: FunctionReference;
    type Function: Function<Self::FunctionReference>;
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
    pub functions: HashMap<T::FunctionReference, T::Function>,
    /// The program's types
    pub types: HashMap<T::TypeReference, T::Type>,
}

impl<C> Translate<GenericFunctionRef, C> for GenericFunctionRef {
    fn translate(&self, _context: &mut C) -> Result<GenericFunctionRef, CompileError> {
        Ok(self.clone())
    }
}

/// Implement PrettyPrint for generic type references
impl<W: Write> PrettyPrint<W> for GenericTypeRef {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut W) -> Result<(), fmt::Error> {
        match self {
            GenericTypeRef::Struct { reference, generics } => {
                reference.format(interner, writer)?;
                write_generics(generics, writer)
            },
            GenericTypeRef::Generic { reference } => {
                reference.format(interner, writer)
            }
        }
    }
}

/// Implement PrettyPrint for function references
impl<W: Write> PrettyPrint<W> for GenericFunctionRef {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut W) -> Result<(), fmt::Error> {
        self.reference.format(interner, writer)?;
        write_generics(&self.generics, writer)
    }
}


