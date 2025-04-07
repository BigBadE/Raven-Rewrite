use crate::HirContext;
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fmt::{Debug, Formatter};
use syntax::SyntaxLevel;
use syntax::structure::literal::Literal;
use syntax::structure::traits::Expression;
use syntax::structure::visitor::Translate;
use syntax::util::CompileError;
use syntax::util::translation::Translatable;
use syntax::util::translation::{translate_fields, translate_vec};

/// An expression in the HIR
#[derive(Serialize, Deserialize)]
pub enum HighExpression<T: SyntaxLevel> {
    // No input one output
    /// A literal value
    Literal(Literal),
    /// A block of code
    CodeBlock {
        /// The code body
        body: Vec<T::Statement>,
        /// A returning value at the end
        value: Box<T::Expression>,
    },
    /// A variable
    Variable(Spur),
    // One input one output
    /// An assignment of a variable
    Assignment {
        /// Whether this is a declaration (let)
        declaration: bool,
        /// The variable to assign to
        variable: Spur,
        /// The value to assign
        value: Box<T::Expression>,
    },
    /// A unary operation
    UnaryOperation {
        /// Whether the symbol is before or after the operation
        pre: bool,
        /// The symbol
        symbol: Spur,
        /// The value passed in
        value: Box<T::Expression>,
    },
    // Multiple inputs one output
    /// A function call
    FunctionCall {
        /// The function to call
        function: T::FunctionReference,
        /// The target to call the function on
        target: Option<Box<T::Expression>>,
        /// The arguments to pass in
        arguments: Vec<T::Expression>,
    },
    /// A binary operation
    BinaryOperation {
        /// The symbol
        symbol: Spur,
        /// The first value to operate on
        first: Box<T::Expression>,
        /// The second value to operate on
        second: Box<T::Expression>,
    },
    /// Creation of a struct
    CreateStruct {
        /// The struct to create
        target_struct: T::TypeReference,
        /// The fields to set and their values
        fields: Vec<(Spur, T::Expression)>,
    },
}

impl<T: SyntaxLevel> Expression for HighExpression<T> {}

impl<T: SyntaxLevel> Debug for HighExpression<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HighExpression::Literal(lit) => {
                f.debug_tuple("HighExpression::Literal").field(lit).finish()
            }
            HighExpression::CodeBlock { body, value } => f
                .debug_struct("HighExpression::CodeBlock")
                .field("body", body)
                .field("value", value)
                .finish(),
            HighExpression::Variable(var) => f
                .debug_tuple("HighExpression::Variable")
                .field(var)
                .finish(),
            HighExpression::Assignment {
                declaration,
                variable,
                value,
            } => f
                .debug_struct("HighExpression::Assignment")
                .field("declaration", declaration)
                .field("variable", variable)
                .field("value", value)
                .finish(),
            HighExpression::FunctionCall {
                function,
                target,
                arguments,
            } => f
                .debug_struct("HighExpression::FunctionCall")
                .field("function", function)
                .field("target", target)
                .field("arguments", arguments)
                .finish(),
            HighExpression::CreateStruct {
                target_struct,
                fields,
            } => f
                .debug_struct("HighExpression::CreateStruct")
                .field("target_struct", target_struct)
                .field("fields", fields)
                .finish(),
            HighExpression::UnaryOperation { pre, symbol, value } => f
                .debug_struct("HighExpression::UnaryOperation")
                .field("pre", pre)
                .field("symbol", symbol)
                .field("value", value)
                .finish(),
            HighExpression::BinaryOperation {
                symbol,
                first,
                second,
            } => f
                .debug_struct("HighExpression::BinaryOperation")
                .field("symbol", symbol)
                .field("first", first)
                .field("second", second)
                .finish(),
        }
    }
}

/// Handle expression translation
impl<I: SyntaxLevel + Translatable<HirContext, I, O>, O: SyntaxLevel>
    Translate<HighExpression<O>, HirContext> for HighExpression<I>
{
    fn translate(&self, context: &mut HirContext) -> Result<HighExpression<O>, CompileError> {
        Ok(match self {
            HighExpression::Literal(literal) => HighExpression::Literal(*literal),
            HighExpression::CodeBlock { body, value } => HighExpression::CodeBlock {
                body: translate_vec(&body, context, I::translate_stmt)?,
                value: Box::new(I::translate_expr(value, context)?),
            },
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
                    .map(|inner| {
                        Ok::<_, CompileError>(Box::new(I::translate_expr(inner, context)?))
                    })
                    .transpose()?,
                arguments: translate_vec(&arguments, context, I::translate_expr)?,
            },
            HighExpression::CreateStruct {
                target_struct,
                fields,
            } => HighExpression::CreateStruct {
                target_struct: I::translate_type_ref(target_struct, context)?,
                fields: translate_fields(fields, context, I::translate_expr)?,
            },
            HighExpression::UnaryOperation { pre, symbol, value } => {
                HighExpression::UnaryOperation {
                    pre: *pre,
                    symbol: *symbol,
                    value: Box::new(I::translate_expr(value, context)?),
                }
            }
            HighExpression::BinaryOperation {
                symbol,
                first,
                second,
            } => HighExpression::BinaryOperation {
                symbol: *symbol,
                first: Box::new(I::translate_expr(first, context)?),
                second: Box::new(I::translate_expr(second, context)?),
            },
        })
    }
}
