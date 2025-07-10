use crate::util::path::FilePath;
use serde::{Deserialize, Serialize};
use std::hash::Hash;

/// Indicates that this represents a type in the language.
pub trait Type<T>: Serialize + for<'a> Deserialize<'a> + Clone {
    fn reference(&self) -> &T;
}

/// Indicates that this represents a type reference in the language.
pub trait TypeReference: Serialize + for<'a> Deserialize<'a> + Clone + Eq + Hash {
    fn path(&self) -> FilePath;
}

/// Indicates that this represents a function in the language.
pub trait Function<T>: Serialize + for<'a> Deserialize<'a> + Clone {
    fn reference(&self) -> &T;
}

/// Indicates that this represents a function reference in the language.
pub trait FunctionReference: Serialize + for<'a> Deserialize<'a> + Clone + Eq + Hash {
    fn path(&self) -> FilePath;
}

/// Indicates that this represents a terminator for a block of code in the language.
/// Terminators end blocks of code, and can alter the flow of the program.
/// For example, a return, continue, and break statement is a terminator.
pub trait Terminator: Serialize + for<'a> Deserialize<'a> + Clone {}

/// Indicates that this represents an expression in the language.
/// Expressions are pieces of code that can evaluate to a value.
/// For example, a function call, a variable reference, or a literal value is an expression.
/// Function calls are special, as they can be both an expression and a statement.
/// They are treated as expressions and separately checked for lacking a value
pub trait Expression: Serialize + for<'a> Deserialize<'a> + Clone {}

/// Indicates that this represents a statement in the language.
/// Statements can be thought of as a "line" of code, always terminated by a semicolon.
/// Their return value is ignored if it exists.
pub trait Statement: Serialize + for<'a> Deserialize<'a> + Clone {}
