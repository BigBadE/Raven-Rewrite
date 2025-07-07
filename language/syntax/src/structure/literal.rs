use crate::GenericTypeRef;
use lasso::Spur;
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
    pub fn get_type(&self) -> GenericTypeRef {
        GenericTypeRef::Struct {
            reference: match self {
                Literal::String(_) => 0,
                Literal::F64(_) => 1,
                Literal::F32(_) => 2,
                Literal::I64(_) => 3,
                Literal::I32(_) => 4,
                Literal::U64(_) => 5,
                Literal::U32(_) => 6,
                Literal::Bool(_) => 7,
                Literal::Char(_) => 8,
            },
            generics: vec![],
        }
    }
}
