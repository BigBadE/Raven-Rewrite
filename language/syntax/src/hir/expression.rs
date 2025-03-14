use crate::code::literal::Literal;
use crate::structure::visitor::{FileOwner, Translate};
use crate::util::translation::translate_fields;
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::SyntaxLevel;
use lasso::Spur;
use std::fmt;
use std::fmt::Debug;

pub trait Expression: Debug {}

pub enum HighExpression<T: SyntaxLevel> {
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
}

impl<T: SyntaxLevel> Expression for HighExpression<T> {}

impl<T: SyntaxLevel> Debug for HighExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // HighExpression is a type alias for InnerHighExpression<TR, HighFunction<TR, FR>>
        match self {
            HighExpression::Literal(lit) => {
                write!(f, "HighExpression::Literal({:?})", lit)
            }
            HighExpression::CodeBlock(_) => {
                write!(f, "HighExpression::CodeBlock(...)")
            }
            HighExpression::Variable(var) => {
                write!(f, "HighExpression::Variable({:?})", var)
            }
            HighExpression::Assignment {
                declaration,
                variable,
                value: _,
            } => {
                write!(
                    f,
                    "HighExpression::Assignment {{ declaration: {:?}, variable: {:?}, value: ... }}",
                    declaration, variable
                )
            }
            HighExpression::FunctionCall {
                function,
                target: _,
                arguments: _,
            } => {
                write!(
                    f,
                    "HighExpression::FunctionCall {{ function: {:?}, target: ..., arguments: ... }}",
                    function
                )
            }
            HighExpression::CreateStruct {
                target_struct,
                fields: _,
            } => {
                write!(
                    f,
                    "HighExpression::CreateStruct {{ target_struct: {:?}, fields: ... }}",
                    target_struct
                )
            }
        }
    }
}

// Handle expression translation
impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<HighExpression<O>, C, I, O> for HighExpression<I>
{
    fn translate(&self, context: &mut C) -> Result<HighExpression<O>, ParseError> {
        Ok(match self {
            HighExpression::Literal(literal) => HighExpression::Literal(*literal),
            HighExpression::CodeBlock(block) => HighExpression::CodeBlock(
                block
                    .iter()
                    .map(|statement| I::translate_stmt(statement, context))
                    .collect::<Result<_, _>>()?,
            ),
            HighExpression::Variable(variable) => HighExpression::Variable(*variable),
            HighExpression::Assignment {
                declaration,
                variable,
                value,
            } => HighExpression::Assignment {
                declaration: *declaration,
                variable: *variable,
                value: Box::new(I::translate_expr(value, context)?),
            },
            HighExpression::FunctionCall {
                function,
                target,
                arguments,
            } => HighExpression::FunctionCall {
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
            } => HighExpression::CreateStruct {
                target_struct: I::translate_type_ref(target_struct, context)?,
                fields: translate_fields(fields, context, I::translate_expr)?,
            },
        })
    }
}
