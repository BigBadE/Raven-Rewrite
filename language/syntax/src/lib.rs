use std::sync::Arc;
use crate::structure::function::Function;
use lasso::{Spur, ThreadedRodeo};
use crate::hir::types::Type;

pub mod code;
pub mod structure;
pub mod hir;
pub mod util;

pub type TypeRef = usize;
pub type FunctionRef = usize;

pub type RawSyntax = Syntax<Spur, Spur>;
pub type LowSyntax = Syntax<TypeRef, FunctionRef>;

#[derive(Default)]
pub struct Syntax<S, F> {
    pub symbols: Arc<ThreadedRodeo>,
    pub functions: Vec<Function<S, F>>,
    pub types: Vec<Type<S>>
}

impl<S, F> Syntax<S, F> {

}