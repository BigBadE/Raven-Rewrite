use crate::code::statement::Statement;
use crate::structure::Modifier;
use crate::util::path::FilePath;
use crate::{FunctionRef, TypeRef};
use lasso::Spur;

pub type RawFunction = Function<Spur, Spur>;
pub type LowFunction = Function<TypeRef, FunctionRef>;

#[derive(Debug)]
pub struct Function<S, F> {
    pub modifiers: Vec<Modifier>,
    pub file: FilePath,
    pub name: Spur,
    pub parameters: Vec<(Spur, S)>,
    pub return_type: Option<S>,
    pub body: Statement<S, F>
}