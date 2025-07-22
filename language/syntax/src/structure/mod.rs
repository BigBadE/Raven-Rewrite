use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::fmt::{Display, Formatter};
use lasso::Spur;

/// Literal values like numbers or strings
pub mod literal;
/// Traits for various types used in the syntax
pub mod traits;
/// Defines the visitor system used to traverse the syntax tree
pub mod visitor;

lazy_static! {
    /// A list of all possible modifiers
    pub static ref MODIFIERS: HashMap<&'static str, Modifier> = HashMap::from([
        ("pub", Modifier::PUBLIC),
        ("operation", Modifier::OPERATION)
    ]);
}

/// All modifiers that can be added to a function, struct, or variable
/// Must be added to MODIFIERS to be parsable
#[derive(Serialize, Deserialize, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Modifier {
    /// Allows access from other projects
    PUBLIC = 0b1,
    /// Indicates that the function is an operation with special naming and calling conventions
    OPERATION = 0b10,
}

impl Display for Modifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Modifier::PUBLIC => write!(f, "pub"),
            Modifier::OPERATION => write!(f, "operation"),
        }
    }
}

/// An attribute that can be applied to functions, structs, etc.
/// Similar to Rust's attribute system like #[test], #[derive(Clone)]
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
pub struct Attribute {
    /// The name of the attribute (e.g., "test", "derive")
    pub name: Spur,
    /// Optional parameters/arguments for the attribute
    pub args: Vec<AttributeArg>,
}

/// Arguments that can be passed to attributes
#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
pub enum AttributeArg {
    /// A simple identifier like `Clone` in #[derive(Clone)]
    Identifier(Spur),
    /// A string literal like `"hello"` in #[doc = "hello"]
    String(String),
    /// A nested attribute for complex cases
    Nested(Attribute),
}

impl Display for Attribute {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "#[{:?}]", self.name)
    }
}

impl Display for AttributeArg {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AttributeArg::Identifier(spur) => write!(f, "{:?}", spur),
            AttributeArg::String(s) => write!(f, "\"{}\"", s),
            AttributeArg::Nested(attr) => write!(f, "{}", attr),
        }
    }
}