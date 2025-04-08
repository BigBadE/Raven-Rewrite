use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

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
#[derive(Serialize, Deserialize, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Modifier {
    /// Allows access from other projects
    PUBLIC = 0b1,
    /// Indicates that the function is an operation with special naming and calling conventions
    OPERATION = 0b10,
}