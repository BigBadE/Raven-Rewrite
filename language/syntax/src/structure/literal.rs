use crate::TypeRef;
use lasso::Spur;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, Clone, Copy)]
pub enum Literal {
    String(Spur),
    F64(f64),
    F32(f32),
    I64(i64),
    I32(i32),
    U64(u64),
    U32(u32),
    Bool(bool),
    Char(char),
}

pub const TYPES: [&str; 9] = [
    "str", "f64", "f32", "i64", "i32", "u64", "u32", "bool", "char",
];

impl Literal {
    /// This is expected to be kept in sync with TYPES.
    pub fn get_type(&self) -> TypeRef {
        TypeRef(match self {
            Literal::String(_) => 0,
            Literal::F64(_) => 1,
            Literal::F32(_) => 2,
            Literal::I64(_) => 3,
            Literal::I32(_) => 4,
            Literal::U64(_) => 5,
            Literal::U32(_) => 6,
            Literal::Bool(_) => 7,
            Literal::Char(_) => 8,
        })
    }
}
