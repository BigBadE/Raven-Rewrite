use hir::statement::HighStatement;
use crate::{
    LocalVar, MediumExpression, MediumSyntaxLevel, MediumTerminator, MirContext, Place,
};
use syntax::structure::visitor::Translate;
use syntax::util::ParseError;
use syntax::util::translation::Translatable;
use syntax::{SyntaxLevel, TypeRef};
use std::fmt::Debug;
use serde::{Deserialize, Serialize};
use syntax::structure::literal::Literal;
use syntax::structure::traits::Statement;

/// The MIR is made up of a series of nodes, each terminated with a jump expression.
#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub enum MediumStatement<T: SyntaxLevel> {
    Assign {
        place: Place,
        value: MediumExpression<T>,
    },
    StorageLive(LocalVar, TypeRef),
    StorageDead(LocalVar),
    Noop,
}

impl<T: SyntaxLevel> Statement for MediumStatement<T> {}

// Handle statement translation
impl<'a, I: SyntaxLevel + Translatable<MirContext<'a>, I, MediumSyntaxLevel>>
    Translate<MediumStatement<MediumSyntaxLevel>, MirContext<'a>, I, MediumSyntaxLevel>
    for HighStatement<I>
{
    fn translate(
        &self,
        context: &mut MirContext<'a>,
    ) -> Result<MediumStatement<MediumSyntaxLevel>, ParseError> {
        match self {
            HighStatement::Expression(expression) => {
                let value = I::translate_expr(expression, context)?;
                let local = context.create_temp(value.get_type(&context));
                context
                    .push_statement(MediumStatement::StorageLive(local, value.get_type(context)));
                context.push_statement(MediumStatement::Assign {
                    place: Place {
                        local,
                        projection: vec![],
                    },
                    value,
                });
            }
            HighStatement::If {
                conditions,
                else_branch,
            } => {
                let mut current = context.create_block();
                let end = context.create_block();
                for condition in conditions {
                    context.switch_to_block(current);
                    let discriminant = I::translate_expr(&condition.condition, context)?;
                    let next = context.create_block();
                    current = context.create_block();
                    context.set_terminator(MediumTerminator::Switch {
                        discriminant,
                        targets: vec![(Literal::U64(0), next)],
                        fallback: current,
                    });

                    // Translate the if body
                    context.switch_to_block(next);
                    for statement in &condition.branch {
                        I::translate_stmt(statement, context)?;
                    }
                    if let MediumTerminator::Unreachable = context.code_blocks[context.current_block].terminator
                    {
                        context.set_terminator(MediumTerminator::Goto(end));
                    }
                }
                context.switch_to_block(current);
                if let Some(else_branch) = else_branch {
                    for statement in else_branch {
                        I::translate_stmt(statement, context)?;
                    }
                }
                if let MediumTerminator::Unreachable = context.code_blocks[context.current_block].terminator
                {
                    context.set_terminator(MediumTerminator::Goto(end));
                }
                context.switch_to_block(end);
            }
            HighStatement::For { condition: _condition } => {
                todo!()
            }
            HighStatement::While { condition } => {
                let top = context.create_block();
                let body = context.create_block();
                let end = context.create_block();
                context.switch_to_block(top);
                // Jump to end if condition is false
                let discriminant = I::translate_expr(&condition.condition, context)?;
                context.set_terminator(MediumTerminator::Switch {
                    discriminant,
                    targets: vec![(Literal::U64(0), end)],
                    fallback: body,
                });
                // Translate the body
                context.switch_to_block(body);
                context.parent_loop = Some(top);
                context.parent_end = Some(end);
                for statement in &condition.branch {
                    I::translate_stmt(statement, context)?;
                }
                if let MediumTerminator::Unreachable = context.code_blocks[context.current_block].terminator
                {
                    context.set_terminator(MediumTerminator::Goto(top));
                }
                context.switch_to_block(end);
            }
            HighStatement::Loop { body } => {
                let top = context.create_block();
                let end = context.create_block();
                context.switch_to_block(top);
                context.parent_loop = Some(top);
                context.parent_end = Some(end);

                // Translate the body
                for statement in body {
                    I::translate_stmt(statement, context)?;
                }
                if let MediumTerminator::Unreachable = context.code_blocks[context.current_block].terminator
                {
                    context.set_terminator(MediumTerminator::Goto(top));
                }
                context.switch_to_block(end);
            }
            HighStatement::Terminator(terminator) => {
                let terminator = I::translate_terminator(terminator, context)?;
                context.set_terminator(terminator)
            }
        }
        // Due to the nature of translating a tree to a graph, we ignore the return type for traversal
        // and instead add whatever we return to the context (since it's not one to one).
        Ok(MediumStatement::Noop)
    }
}
