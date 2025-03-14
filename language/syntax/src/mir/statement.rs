use crate::hir::statement::{Conditional, HighStatement, Statement};
use crate::mir::MirContext;
use crate::structure::visitor::{FileOwner, Translate};
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::SyntaxLevel;
use std::fmt;
use std::fmt::Debug;

/// The MIR is made up of a series of nodes, each terminated with a jump expression.
pub enum MediumStatement<T: SyntaxLevel> {
    Block {
        body: Vec<T::Expression>,
        next: usize,
        condition: Option<T::Expression>,
    },
    Return {
        body: Vec<T::Expression>,
        returning: Option<T::Expression>,
    },
}

impl<T: SyntaxLevel> Statement for MediumStatement<T> {}

impl<T: SyntaxLevel> Debug for MediumStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MediumStatement::Block { .. } => write!(f, "MediumStatement::Block(...)"),
            MediumStatement::Return { .. } => write!(f, "MediumStatement::Return(...)"),
        }
    }
}

// Handle statement translation
impl<I: SyntaxLevel + Translatable<MirContext, I, O>, O: SyntaxLevel>
    Translate<MediumStatement<O>, MirContext, I, O> for HighStatement<I>
{
    fn translate(&self, context: &mut MirContext) -> Result<MediumStatement<O>, ParseError> {
        Ok(match self {
            HighStatement::Expression(expression) => {
                let mut parents = context.parents.clone();
                parents.push(context.next_block);
                let mut context = MirContext {
                    file: context.file.clone(),
                    next_block: context.next_block + 1,
                    adding_blocks: vec!(),
                    parents,
                    expr_data: (None, 0),
                };
                let mut body = vec![I::translate_expr(expression, &mut context)?];
                body.append(&mut context.adding_blocks);
                MediumStatement::Block {
                    body,
                    condition: context.expr_data.0,
                    next: context.expr_data.1,
                }
            },
            HighStatement::Return(returning) => HighStatement::Return,
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
                    .map(|branch| {
                        Ok::<_, ParseError>(Box::new(I::translate_stmt(branch, context)?))
                    })
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
