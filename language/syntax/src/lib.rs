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
use std::path::PathBuf;

/// The structure of the program in memory
pub mod structure;
/// Various utility functions
pub mod util;

/// A package dependency
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PackageDependency {
    /// The name of the package
    pub name: String,
    /// The path to the package (for path dependencies)
    pub path: Option<PathBuf>,
    /// The version constraint (for registry dependencies)
    pub version: Option<String>,
}

/// Package manifest structure
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PackageManifest {
    /// Package information
    pub package: PackageInfo,
    /// Dependencies
    pub dependencies: HashMap<String, PackageDependency>,
}

/// Package information
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PackageInfo {
    /// The name of the package
    pub name: String,
    /// The version of the package
    pub version: String,
}

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

impl GenericTypeRef {
    pub fn substitute_generics_in_type(&self, generics: &HashMap<GenericTypeRef, TypeRef>) -> Result<GenericTypeRef, CompileError> {
        match &self {
            GenericTypeRef::Generic { reference } => {
                let generic_key = GenericTypeRef::Generic { reference: reference.clone() };

                // If this is a generic parameter, substitute it with the concrete type
                if let Some(concrete_type) = generics.get(&generic_key) {
                    Ok(GenericTypeRef::from(concrete_type.clone()))
                } else {
                    // If not found, keep as-is (shouldn't happen in correct code)
                    Ok(self.clone())
                }
            }
            GenericTypeRef::Struct { reference, generics: type_generics } => {
                // Recursively substitute generics in the struct's type parameters
                let substituted_generics: Result<Vec<_>, _> = type_generics.iter()
                    .map(|generic| generic.substitute_generics_in_type(generics))
                    .collect();
                Ok(GenericTypeRef::Struct {
                    reference: reference.clone(),
                    generics: substituted_generics?,
                })
            }
        }
    }
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

/// Converts the reference to the monomorphized version by appending the generics to the last segment
pub fn get_monomorphized_name<'a, I: Iterator<Item=&'a TypeRef>>
(reference: &TypeRef, generics: I, interner: &ThreadedRodeo) -> Result<TypeRef, CompileError> {
    let mut reference = reference.clone();
    let last = reference.last_mut().unwrap();
    let mut string = interner.resolve(last).to_string();
    for generic in generics {
        string.push('_');
        generic.format_top(interner, &mut string)?;
    }
    *last = interner.get_or_intern(string);
    Ok(reference)
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
pub trait SyntaxLevel: Serialize + for<'a> Deserialize<'a> + Clone {
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
    Statement: PrettyPrint<W>, Expression: PrettyPrint<W>, Terminator: PrettyPrint<W>> {}

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
            }
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


