use crate::structure::visitor::{FileOwner, Translate};
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::SyntaxLevel;
use std::fmt::{Debug, Formatter};
use std::fmt;

pub trait Statement: Debug {}

pub enum HighStatement<T: SyntaxLevel> {
    Expression(T::Expression),
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

#[derive(Debug)]
pub struct Conditional<T: SyntaxLevel> {
    pub condition: T::Expression,
    pub branch: Vec<T::Statement>,
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
            HighStatement::If {
                conditions,
                else_branch,
            } => HighStatement::If {
                conditions: conditions
                    .iter()
                    .map(|condition| {
                        Ok::<_, ParseError>(Conditional {
                            condition: I::translate_expr(&condition.condition, context)?,
                            branch: condition
                                .branch
                                .iter()
                                .map(|statement| I::translate_stmt(statement, context))
                                .collect::<Result<_, _>>()?,
                        })
                    })
                    .collect::<Result<_, _>>()?,
                else_branch: else_branch
                    .as_ref()
                    .map(|inner| {
                        inner
                            .iter()
                            .map(|statement| I::translate_stmt(statement, context))
                            .collect::<Result<_, _>>()
                    })
                    .transpose()?,
            },
            HighStatement::For { condition } => HighStatement::For {
                condition: Conditional {
                    condition: I::translate_expr(&condition.condition, context)?,
                    branch: condition.branch
                        .iter()
                        .map(|inner| I::translate_stmt(inner, context))
                        .collect::<Result<_, _>>()?,
                }

            },
            HighStatement::While { condition } => HighStatement::While {
                condition: Conditional {
                    condition: I::translate_expr(&condition.condition, context)?,
                    branch: condition
                        .branch
                        .iter()
                        .map(|statement| I::translate_stmt(statement, context))
                        .collect::<Result<_, _>>()?,
                },
            },
            HighStatement::Loop { body } => HighStatement::Loop {
                body: body
                    .iter()
                    .map(|inner| I::translate_stmt(inner, context))
                    .collect::<Result<_, _>>()?,
            },
            HighStatement::Terminator(terminator) => {
                HighStatement::Terminator(I::translate_terminator(terminator, context)?)
            }
        })
    }
}
