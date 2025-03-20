use std::fmt;
use syntax::structure::visitor::Translate;
use syntax::util::translation::{translate_fields, translate_vec};
use syntax::util::translation::Translatable;
use syntax::util::ParseError;
use lasso::Spur;
use std::fmt::{Debug, Formatter};
use syntax::structure::FileOwner;
use syntax::structure::literal::Literal;
use syntax::structure::traits::Expression;
use syntax::SyntaxLevel;

pub enum HighExpression<T: SyntaxLevel> {
    // No input one output
    Literal(Literal),
    CodeBlock {
        body: Vec<T::Statement>,
        value: Box<T::Expression>,
    },
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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HighExpression::Literal(lit) => {
                f.debug_tuple("HighExpression::Literal")
                    .field(lit)
                    .finish()
            }
            HighExpression::CodeBlock { body, value } => {
                f.debug_struct("HighExpression::CodeBlock")
                    .field("body", body)
                    .field("value", value)
                    .finish()
            }
            HighExpression::Variable(var) => {
                f.debug_tuple("HighExpression::Variable")
                    .field(var)
                    .finish()
            }
            HighExpression::Assignment { declaration, variable, value } => {
                f.debug_struct("HighExpression::Assignment")
                    .field("declaration", declaration)
                    .field("variable", variable)
                    .field("value", value)
                    .finish()
            }
            HighExpression::FunctionCall { function, target, arguments } => {
                f.debug_struct("HighExpression::FunctionCall")
                    .field("function", function)
                    .field("target", target)
                    .field("arguments", arguments)
                    .finish()
            }
            HighExpression::CreateStruct { target_struct, fields } => {
                f.debug_struct("HighExpression::CreateStruct")
                    .field("target_struct", target_struct)
                    .field("fields", fields)
                    .finish()
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
            HighExpression::CodeBlock { body, value } => HighExpression::CodeBlock {
                body: translate_vec(&body, context, I::translate_stmt)?,
                value: Box::new(I::translate_expr(&value, context)?),
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
                    .map(|inner| Ok::<_, ParseError>(Box::new(I::translate_expr(inner, context)?)))
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
        })
    }
}
