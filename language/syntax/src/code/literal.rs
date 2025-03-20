use lasso::Spur;
use crate::TypeRef;

#[derive(Debug, Clone, Copy)]
pub enum Literal {
    Void,
    String(Spur),
    F64(f64),
    F32(f32),
    I64(i64),
    I32(i32),
    U64(u64),
    U32(u32),
    Bool(bool),
    Char(char)
}

impl Literal {
    pub fn get_type(&self) -> TypeRef {
        TypeRef(match self {
            Literal::Void => 0,
            Literal::String(_) => 1,
            Literal::F64(_) => 2,
            Literal::F32(_) => 3,
            Literal::I64(_) => 4,
            Literal::I32(_) => 5,
            Literal::U64(_) => 6,
            Literal::U32(_) => 7,
            Literal::Bool(_) => 8,
            Literal::Char(_) => 9
        })
    }
}