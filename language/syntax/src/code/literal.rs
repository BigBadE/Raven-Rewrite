use lasso::Spur;
use crate::TypeRef;

#[derive(Debug, Clone, Copy)]
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
    Void
}

impl Literal {
    pub fn get_type(&self) -> TypeRef {
        match self {
            /*Literal::String(_) => TypeRef::String,
            Literal::F64(_) => TypeRef::F64,
            Literal::F32(_) => TypeRef::F32,
            Literal::I64(_) => TypeRef::I64,
            Literal::I32(_) => TypeRef::I32,
            Literal::U64(_) => TypeRef::U64,
            Literal::U32(_) => TypeRef::U32,
            Literal::Bool(_) => TypeRef::Bool,
            Literal::Char(_) => TypeRef::Char,
            Literal::Void => TypeRef::Void*/
            _ => todo!()
        }
    }
}