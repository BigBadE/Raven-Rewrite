use lasso::Spur;
use crate::code::literal::Literal;
use crate::code::statement::Statement;
use crate::{FunctionRef, TypeRef};

pub type RawExpression = Expression<Spur, Spur>;
pub type LowExpression = Expression<TypeRef, FunctionRef>;

#[derive(Debug)]
pub enum Expression<S, F> {
    // No input one output
    Literal(Literal),
    CodeBlock(Vec<Statement<S, F>>),
    Variable(Spur),
    // One input one output
    Assignment {
        declaration: bool,
        variable: Spur,
        value: Box<Expression<S, F>>,
    },
    // Multiple inputs one output
    FunctionCall {
        function: F,
        target: Option<Box<Expression<S, F>>>,
        arguments: Vec<Expression<S, F>>,
    },
    CreateStruct {
        struct_target: S,
        fields: Vec<(Spur, Expression<S, F>)>,
    }
}