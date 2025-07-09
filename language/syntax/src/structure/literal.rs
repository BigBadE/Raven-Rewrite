use crate::TypeRef;
use lasso::{Spur, ThreadedRodeo};
use serde::{Deserialize, Serialize};

/// A literal value
#[derive(Serialize, Deserialize, Debug, Clone, Copy)]
pub enum Literal {
    /// A string, like "foo"
    String(Spur),
    /// A double precision float
    F64(f64),
    /// A single precision float
    F32(f32),
    /// A 8-byte signed integer
    I64(i64),
    /// A 4-byte signed integer
    I32(i32),
    /// A 8-byte unsigned integer
    U64(u64),
    /// A 4-byte unsigned integer
    U32(u32),
    /// A boolean value
    Bool(bool),
    /// A 1-byte character
    Char(char),
}

/// A list of all literal types, must be kept in sync with Literals
pub const TYPES: [&str; 9] = [
    "str", "f64", "f32", "i64", "i32", "u64", "u32", "bool", "char",
];

impl Literal {
    /// This is expected to be kept in sync with TYPES.
    pub fn get_type(&self, interner: &ThreadedRodeo) -> TypeRef {
        vec![interner.get_or_intern(match self {
            Literal::String(_) => "str",
            Literal::F32(_) => "f32",
            Literal::F64(_) => "f64",
            Literal::I64(_) => "i64",
            Literal::I32(_) => "i32",
            Literal::U64(_) => "u64",
            Literal::U32(_) => "u32",
            Literal::Bool(_) => "bool",
            Literal::Char(_) => "char",
        })]
    }
}
