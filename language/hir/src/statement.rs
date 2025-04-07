use serde::{Deserialize, Serialize};
use std::fmt;
use std::fmt::{Debug, Formatter};
use syntax::SyntaxLevel;
use syntax::structure::FileOwner;
use syntax::structure::traits::Statement;
use syntax::structure::visitor::Translate;
use syntax::util::CompileError;
use syntax::util::translation::{Translatable, translate_vec};

/// A statement in the HIR
#[derive(Serialize, Deserialize)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub enum HighStatement<T: SyntaxLevel> {
    /// An expression, with the returnvalue ignored
    Expression(T::Expression),
    /// A block of code
    CodeBlock(Vec<T::Statement>),
    /// A terminator
    Terminator(T::Terminator),
    /// An if statement
    If {
        /// The possible conditions, starting with an if, with each sequential value being an else if
        conditions: Vec<Conditional<T>>,
        /// The else branch
        else_branch: Option<Vec<T::Statement>>,
    },
    /// A for statement
    For {
        /// The condition of the for statement
        condition: Conditional<T>,
    },
    /// A while statement
    While {
        /// The condition of the while statement
        condition: Conditional<T>,
    },
    /// An infinite loop statement
    Loop {
        /// The body of the loop
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

/// A conditional block
#[derive(Serialize, Deserialize, Debug)]
pub struct Conditional<T: SyntaxLevel> {
    /// The condition to check
    pub condition: T::Expression,
    /// The branch to execute if the condition is true
    pub branch: Vec<T::Statement>,
}

impl<C, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel> Translate<Conditional<O>, C>
    for Conditional<I>
{
    fn translate(&self, context: &mut C) -> Result<Conditional<O>, CompileError> {
        Ok(Conditional {
            condition: I::translate_expr(&self.condition, context)?,
            branch: translate_vec(&self.branch, context, I::translate_stmt)?,
        })
    }
}

// Handle statement translation
impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel>
    Translate<HighStatement<O>, C> for HighStatement<I>
{
    fn translate(&self, context: &mut C) -> Result<HighStatement<O>, CompileError> {
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
