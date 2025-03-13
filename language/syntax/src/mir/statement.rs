use std::fmt;
use std::fmt::Debug;
use crate::hir::statement::{Conditional, HighStatement, Statement};
use crate::structure::visitor::{FileOwner, Translate};
use crate::SyntaxLevel;
use crate::util::ParseError;
use crate::util::translation::Translatable;

pub enum MediumStatement<T: SyntaxLevel> {
    Block(Vec<T::Expression>)
}

impl<T: SyntaxLevel> Statement for MediumStatement<T> {}

impl<T: SyntaxLevel> Debug for MediumStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MediumStatement::Block(_) => write!(f, "MediumStatement::Block(...)")
        }
    }
}

// Handle statement translation
impl<C: FileOwner, I: SyntaxLevel + Translatable<C, I, O>, O: SyntaxLevel> Translate<MediumStatement<O>, C, I, O>
for HighStatement<I>
{
    fn translate(&self,
                 context: &mut C,
    ) -> Result<MediumStatement<O>, ParseError> {
        Ok(match self {
            HighStatement::Expression(expression) => {
                HighStatement::Expression(I::translate_expr(expression, context)?)
            }
            HighStatement::Return => HighStatement::Return,
            HighStatement::Break => HighStatement::Break,
            HighStatement::Continue => HighStatement::Continue,
            HighStatement::If {
                conditions,
                else_branch,
            } => HighStatement::If {
                conditions: conditions
                    .iter()
                    .map(|condition| {
                        Ok::<_, ParseError>(Conditional {
                            condition: I::translate_expr(&condition.condition, context)?,
                            branch: Box::new(I::translate_stmt(&condition.branch, context)?),
                        })
                    })
                    .collect::<Result<_, _>>()?,
                else_branch: else_branch
                    .as_ref()
                    .map(|branch| Ok::<_, ParseError>(Box::new(I::translate_stmt(branch, context)?)))
                    .transpose()?,
            },
            HighStatement::For { iterator, body } => HighStatement::For {
                iterator: I::translate_expr(iterator, context)?,
                body: Box::new(I::translate_stmt(body, context)?),
            },
            HighStatement::While { condition } => HighStatement::While {
                condition: Conditional {
                    condition: I::translate_expr(&condition.condition, context)?,
                    branch: Box::new(I::translate_stmt(&condition.branch, context)?),
                },
            },
            HighStatement::Loop { body } => HighStatement::Loop {
                body: Box::new(I::translate_stmt(body, context)?),
            },
        })
    }
}