use lasso::Spur;

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
}
