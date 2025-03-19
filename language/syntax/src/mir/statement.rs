use crate::hir::statement::{HighStatement, Statement};
use crate::mir::{
    LocalVar, MediumExpression, MediumSyntaxLevel, MediumTerminator, MirContext, Place,
};
use crate::structure::visitor::Translate;
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::{SyntaxLevel, TypeRef};
use std::fmt::Debug;

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
    Translate<MediumStatement<MediumSyntaxLevel>, MirContext<'_>, I, MediumSyntaxLevel>
    for HighStatement<I>
{
    fn translate(
        &self,
        context: &mut MirContext,
    ) -> Result<MediumStatement<MediumSyntaxLevel>, ParseError> {
        match self {
            HighStatement::Expression(expression) => {
                let value = I::translate_expr(expression, context)?;
                let statement = MediumStatement::Assign {
                    place: Place { local: context.create_temp(value.get_type(&context)), projection: vec![] },
                    value,
                };
                context.push_statement(statement);
            }
            HighStatement::If {
                conditions,
                else_branch,
            } => {
                todo!()
            }
            HighStatement::For { iterator, body } => {
                todo!()
            }
            HighStatement::While { condition } => {
                todo!()
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
