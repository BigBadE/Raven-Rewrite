use crate::hir::statement::{HighStatement, Statement};
use crate::mir::{
    LocalVar, MediumExpression, MediumSyntaxLevel, MediumTerminator, MirContext, Place,
};
use crate::structure::visitor::Translate;
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::{SyntaxLevel, TypeRef};
use std::fmt::Debug;
use crate::code::literal::Literal;

/// The MIR is made up of a series of nodes, each terminated with a jump expression.
#[derive(Debug)]
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
                context.push_statement(MediumStatement::StorageLive(local, value.get_type(context)));
                context.push_statement(MediumStatement::Assign {
                    place: Place { local, projection: vec![] },
                    value,
                });
            }
            HighStatement::If {
                conditions,
                else_branch,
            } => {

                for condition in conditions {

                }
                todo!()
            }
            HighStatement::For { iterator, body } => {
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
                    targets: vec!((Literal::U64(0), end)),
                    fallback: body
                });
                context.switch_to_block(body);
                context.parent_loop = Some(top);
                context.parent_end = Some(end);

            }
            HighStatement::Loop { body } => {
                let top = context.create_block();
                let end = context.create_block();
                context.switch_to_block(top);
                context.parent_loop = Some(top);
                context.parent_end = Some(end);
                I::translate_stmt(body, context)?;
                // Whatever block ends up at the end should jump back to the top.
                context.set_terminator(MediumTerminator::Goto(top));
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
