use serde::{Deserialize, Serialize};
use std::fmt;
use std::fmt::{Debug, Formatter};
use syntax::structure::traits::Statement;
use syntax::structure::visitor::Translate;
use syntax::structure::FileOwner;
use syntax::util::translation::{translate_vec, Translatable};
use syntax::util::ParseError;
use syntax::SyntaxLevel;

#[derive(Serialize, Deserialize)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub enum HighStatement<T: SyntaxLevel> {
    Expression(T::Expression),
    CodeBlock(Vec<T::Statement>),
    Terminator(T::Terminator),
    If {
        conditions: Vec<Conditional<T>>,
        else_branch: Option<Vec<T::Statement>>,
    },
    For {
        condition: Conditional<T>,
    },
    While {
        condition: Conditional<T>,
    },
    Loop {
        body: Vec<T::Statement>,
    },
}

impl<T: SyntaxLevel> Statement for HighStatement<T> {}

impl<T: SyntaxLevel> Debug for HighStatement<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            HighStatement::Expression(expr) => f
                .debug_tuple("HighStatement::Expression")
                .field(expr)
                .finish(),
            HighStatement::CodeBlock(expr) => f
                .debug_tuple("HighStatement::Expression")
                .field(expr)
                .finish(),
            HighStatement::If {
                conditions,
                else_branch,
            } => f
                .debug_struct("HighStatement::If")
                .field("conditions", conditions)
                .field("else_branch", else_branch)
                .finish(),
            HighStatement::For { condition } => f
                .debug_struct("HighStatement::For")
                .field("condition", condition)
                .finish(),
            HighStatement::While { condition } => f
                .debug_struct("HighStatement::While")
                .field("condition", condition)
                .finish(),
            HighStatement::Loop { body } => f
                .debug_struct("HighStatement::Loop")
                .field("body", body)
                .finish(),
            HighStatement::Terminator(terminator) => f
                .debug_tuple("HighStatement::Terminator")
                .field(terminator)
                .finish(),
        }
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Conditional<T: SyntaxLevel> {
    pub condition: T::Expression,
    pub branch: Vec<T::Statement>,
}

impl<C, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel> Translate<Conditional<O>, C, I, O>
    for Conditional<I>
{
    fn translate(&self, context: &mut C) -> Result<Conditional<O>, ParseError> {
        Ok(Conditional {
            condition: I::translate_expr(&self.condition, context)?,
            branch: translate_vec(&self.branch, context, I::translate_stmt)?,
        })
    }
}

// Handle statement translation
impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<HighStatement<O>, C, I, O> for HighStatement<I>
{
    fn translate(&self, context: &mut C) -> Result<HighStatement<O>, ParseError> {
        Ok(match self {
            HighStatement::Expression(expression) => {
                HighStatement::Expression(I::translate_expr(expression, context)?)
            }
            HighStatement::CodeBlock(expressions) => {
                HighStatement::CodeBlock(translate_vec(expressions, context, I::translate_stmt)?)
            }
            HighStatement::If {
                conditions,
                else_branch,
            } => HighStatement::If {
                conditions: translate_vec(conditions, context, Translate::translate)?,
                else_branch: else_branch
                    .as_ref()
                    .map(|inner| translate_vec(&inner, context, I::translate_stmt))
                    .transpose()?,
            },
            HighStatement::For { condition } => HighStatement::For {
                condition: condition.translate(context)?,
            },
            HighStatement::While { condition } => HighStatement::While {
                condition: condition.translate(context)?,
            },
            HighStatement::Loop { body } => HighStatement::Loop {
                body: translate_vec(&body, context, I::translate_stmt)?,
            },
            HighStatement::Terminator(terminator) => {
                HighStatement::Terminator(I::translate_terminator(terminator, context)?)
            }
        })
    }
}
