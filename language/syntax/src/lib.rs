use std::collections::HashMap;
use std::fmt;
use crate::structure::traits::{
    Expression, Function, FunctionReference, Statement, Terminator, Type, TypeReference,
};
use crate::structure::visitor::Translate;
use crate::util::{CompileError, Context};
use lasso::ThreadedRodeo;
use serde::{Deserialize, Serialize};
use std::fmt::Write;
use std::sync::Arc;
use crate::util::path::FilePath;
use crate::util::pretty_print::{write_generics, NestedWriter, PrettyPrint};

/// The structure of the program in memory
pub mod structure;
/// Various utility functions
pub mod util;

/// A reference to a specific type
#[derive(Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
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

impl From<TypeRef> for GenericTypeRef {
    fn from(reference: TypeRef) -> Self {
        GenericTypeRef::Struct { reference, generics: vec![] }
    }
}

impl TypeReference for GenericTypeRef {
    fn path(&self) -> FilePath {
        match self {
            GenericTypeRef::Struct { reference, .. } | GenericTypeRef::Generic { reference } => {
                TypeReference::path(reference)
            }
        }
    }
}

/// A reference to a specific type
pub type TypeRef = FilePath;

impl TypeReference for TypeRef {
    fn path(&self) -> FilePath {
        self.clone()
    }
}

/// A reference to a specific function
#[derive(Clone, Hash, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenericFunctionRef {
    /// The reference to the function
    pub reference: FunctionRef,
    /// The generic constraints of the function
    pub generics: Vec<GenericTypeRef>,
}

impl From<FunctionRef> for GenericFunctionRef {
    fn from(reference: FunctionRef) -> Self {
        GenericFunctionRef { reference, generics: vec![] }
    }
}

impl FunctionReference for GenericFunctionRef {
    fn path(&self) -> FilePath {
        self.reference.clone()
    }
}

pub type FunctionRef = FilePath;

impl FunctionReference for FunctionRef {
    fn path(&self) -> FilePath {
        self.clone()
    }
}

/// A level of syntax. As the program is compiled, it goes lower until it hits the lowest level.
/// Associated traits are used to keep track of exactly what the data structure is at each level
/// and allow the same transformations to be used on multiple levels.
pub trait SyntaxLevel: Serialize + for<'a> Deserialize<'a> {
    type TypeReference: TypeReference;
    type Type: Type<Self::TypeReference>;
    type FunctionReference: FunctionReference;
    type Function: Function<Self::FunctionReference>;
    type Statement: Statement;
    type Expression: Expression;
    type Terminator: Terminator;
}

pub trait PrettyPrintableSyntaxLevel<W: Write>: SyntaxLevel<TypeReference: PrettyPrint<W>,
    Type: PrettyPrint<W>, FunctionReference: PrettyPrint<W>, Function: PrettyPrint<W>,
    Statement: PrettyPrint<W>, Expression: PrettyPrint<W>, Terminator: PrettyPrint<W>> {

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
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), fmt::Error> {
        match self {
            GenericTypeRef::Struct { reference, generics } => {
                reference.format(interner, writer)?;
                write_generics(interner, generics, writer)
            },
            GenericTypeRef::Generic { reference } => {
                reference.format(interner, writer)
            }
        }
    }
}

/// Implement PrettyPrint for function references
impl<W: Write> PrettyPrint<W> for GenericFunctionRef {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), fmt::Error> {
        self.reference.format(interner, writer)?;
        write_generics(interner, &self.generics, writer)
    }
}


