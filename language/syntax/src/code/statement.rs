use crate::code::expression::Expression;
use crate::{FunctionRef, TypeRef};
use lasso::Spur;

pub type RawStatement = Statement<Spur, Spur>;
pub type LowStatement = Statement<TypeRef, FunctionRef>;

#[derive(Debug)]
pub enum Statement<S, F> {
    Expression(Expression<S, F>),
    Return,
    Break,
    Continue,
    If {
        conditions: Vec<Conditional<S, F>>,
        else_branch: Option<Box<Statement<S, F>>>,
    },
    For {
        iterator: Box<Expression<S, F>>,
        body: Box<Statement<S, F>>,
    },
    While {
        condition: Box<Conditional<S, F>>
    },
    Loop {
        body: Box<Statement<S, F>>
    }
}

pub type RawConditional = Conditional<Spur, Spur>;

#[derive(Debug)]
pub struct Conditional<S, F> {
    pub condition: Expression<S, F>,
    pub branch: Statement<S, F>
}