use crate::code::literal::Literal;
use crate::hir::expression::{Expression, HighExpression};
use crate::structure::visitor::{FileOwner, Translate};
use crate::util::translation::translate_fields;
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::SyntaxLevel;
use lasso::Spur;
use std::fmt;
use std::fmt::Debug;

pub enum MediumExpression<T: SyntaxLevel> {
    // No input one output
    Literal(Literal),
    CodeBlock(Vec<T::Statement>),
    Variable(Spur),
    // One input one output
    Assignment {
        declaration: bool,
        variable: Spur,
        value: Box<T::Expression>,
    },
    // Multiple inputs one output
    FunctionCall {
        function: T::FunctionReference,
        target: Option<Box<T::Expression>>,
        arguments: Vec<T::Expression>,
    },
    CreateStruct {
        target_struct: T::TypeReference,
        fields: Vec<(Spur, T::Expression)>,
    },
    Jump {
        condition: Box<T::Expression>,
        target: usize
    }
}

impl<T: SyntaxLevel> Expression for MediumExpression<T> {}

impl<T: SyntaxLevel> Debug for MediumExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // MediumExpression is a type alias for InnerHighExpression<TR, HighFunction<TR, FR>>
        match self {
            MediumExpression::Literal(lit) => {
                write!(f, "MediumExpression::Literal({:?})", lit)
            }
            MediumExpression::CodeBlock(_) => {
                write!(f, "MediumExpression::CodeBlock(...)")
            }
            MediumExpression::Variable(var) => {
                write!(f, "MediumExpression::Variable({:?})", var)
            }
            MediumExpression::Assignment {
                declaration,
                variable,
                value: _,
            } => {
                write!(
                    f,
                    "MediumExpression::Assignment {{ declaration: {:?}, variable: {:?}, value: ... }}",
                    declaration, variable
                )
            }
            MediumExpression::FunctionCall {
                function,
                target: _,
                arguments: _,
            } => {
                write!(
                    f,
                    "MediumExpression::FunctionCall {{ function: {:?}, target: ..., arguments: ... }}",
                    function
                )
            }
            MediumExpression::CreateStruct {
                target_struct,
                fields: _,
            } => {
                write!(
                    f,
                    "MediumExpression::CreateStruct {{ target_struct: {:?}, fields: ... }}",
                    target_struct
                )
            },
            MediumExpression::Jump { .. } => {
                write!(f, "MediumExpression::Jump(...)")
            }
        }
    }
}

// Handle expression translation
impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<MediumExpression<O>, C, I, O> for HighExpression<I> {
    fn translate(&self, context: &mut C) -> Result<MediumExpression<O>, ParseError> {
        Ok(match self {
            HighExpression::Literal(literal) => MediumExpression::Literal(*literal),
            HighExpression::CodeBlock(block) => MediumExpression::CodeBlock(
                block
                    .iter()
                    .map(|statement| I::translate_stmt(statement, context))
                    .collect::<Result<_, _>>()?,
            ),
            HighExpression::Variable(variable) => MediumExpression::Variable(*variable),
            HighExpression::Assignment {
                declaration,
                variable,
                value,
            } => MediumExpression::Assignment {
                declaration: *declaration,
                variable: *variable,
                value: Box::new(I::translate_expr(value, context)?),
            },
            HighExpression::FunctionCall {
                function,
                target,
                arguments,
            } => MediumExpression::FunctionCall {
                function: I::translate_func_ref(function, context)?,
                target: target
                    .as_ref()
                    .map(|inner| Ok::<_, ParseError>(Box::new(I::translate_expr(inner, context)?)))
                    .transpose()?,
                arguments: arguments
                    .iter()
                    .map(|arg| Ok::<_, ParseError>(I::translate_expr(arg, context)?))
                    .collect::<Result<_, _>>()?,
            },
            HighExpression::CreateStruct {
                target_struct,
                fields,
            } => MediumExpression::CreateStruct {
                target_struct: I::translate_type_ref(target_struct, context)?,
                fields: translate_fields(fields, context, I::translate_expr)?,
            },
        })
    }
}
