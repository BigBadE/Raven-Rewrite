use serde::{Deserialize, Serialize};
use syntax::structure::traits::Statement;
use syntax::structure::visitor::Translate;
use syntax::util::translation::{translate_iterable, Translatable};
use syntax::util::CompileError;
use syntax::{ContextSyntaxLevel, SyntaxLevel};

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

/// A conditional block
#[derive(Serialize, Deserialize)]
pub struct Conditional<T: SyntaxLevel> {
    /// The condition to check
    pub condition: T::Expression,
    /// The branch to execute if the condition is true
    pub branch: Vec<T::Statement>,
}

impl<'ctx, I: SyntaxLevel + Translatable<I, O>, O: ContextSyntaxLevel<I>> Translate<Conditional<O>, O::InnerContext<'ctx>>
    for Conditional<I>
{
    fn translate(&self, context: &mut O::InnerContext<'_>) -> Result<Conditional<O>, CompileError> {
        Ok(Conditional {
            condition: I::translate_expr(&self.condition, context)?,
            branch: translate_iterable(&self.branch, context, I::translate_stmt)?,
        })
    }
}

// Handle statement translation
impl<'ctx, I: SyntaxLevel + Translatable<I, O>, O: ContextSyntaxLevel<I>>
    Translate<HighStatement<O>, O::InnerContext<'ctx>> for HighStatement<I>
{
    fn translate(&self, context: &mut O::InnerContext<'_>) -> Result<HighStatement<O>, CompileError> {
        Ok(match self {
            HighStatement::Expression(expression) => {
                HighStatement::Expression(I::translate_expr(expression, context)?)
            }
            HighStatement::CodeBlock(expressions) => {
                HighStatement::CodeBlock(translate_iterable(expressions, context, I::translate_stmt)?)
            }
            HighStatement::If {
                conditions,
                else_branch,
            } => HighStatement::If {
                conditions: translate_iterable(conditions, context, Translate::translate)?,
                else_branch: else_branch
                    .as_ref()
                    .map(|inner| translate_iterable(inner, context, I::translate_stmt))
                    .transpose()?,
            },
            HighStatement::For { condition } => HighStatement::For {
                condition: condition.translate(context)?,
            },
            HighStatement::While { condition } => HighStatement::While {
                condition: condition.translate(context)?,
            },
            HighStatement::Loop { body } => HighStatement::Loop {
                body: translate_iterable(body, context, I::translate_stmt)?,
            },
            HighStatement::Terminator(terminator) => {
                HighStatement::Terminator(I::translate_terminator(terminator, context)?)
            }
        })
    }
}
