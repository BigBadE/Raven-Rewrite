use crate::util::path::FilePath;
use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

pub mod literal;
pub mod traits;
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

/// A trait for all objects that have a file associated with them
pub trait FileOwner {
    /// The file that this object is associated with
    fn file(&self) -> &FilePath;

    /// Set the file that this object is associated with
    fn set_file(&mut self, file: FilePath);
}
