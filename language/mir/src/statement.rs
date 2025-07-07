use crate::{
    LocalVar, MediumExpression, MediumSyntaxLevel, MediumTerminator, MirFunctionContext, Place,
};
use hir::statement::{Conditional, HighStatement};
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use syntax::structure::literal::Literal;
use syntax::structure::traits::Statement;
use syntax::structure::visitor::Translate;
use syntax::util::CompileError;
use syntax::util::translation::Translatable;
use syntax::{SyntaxLevel, GenericTypeRef};

/// The MIR is made up of a series of nodes, each terminated with a jump expression.
#[derive(Serialize, Deserialize, Debug)]
#[serde(bound(deserialize = "T: for<'a> Deserialize<'a>"))]
pub enum MediumStatement<T: SyntaxLevel> {
    /// Assigns a value to a place
    Assign {
        /// The place to assign to
        place: Place,
        /// The value to assign
        value: MediumExpression<T>,
    },
    /// Creates a local variable
    StorageLive(LocalVar, GenericTypeRef),
    /// Kills a local variable
    StorageDead(LocalVar),
    /// A NOOP
    Noop,
}

impl<T: SyntaxLevel> Statement for MediumStatement<T> {}

/// Handle statement translation
impl<'a, I: SyntaxLevel + Translatable<I, MediumSyntaxLevel>>
    Translate<MediumStatement<MediumSyntaxLevel>, MirFunctionContext<'a>> for HighStatement<I>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<MediumStatement<MediumSyntaxLevel>, CompileError> {
        match self {
            HighStatement::Expression(expression) => {
                let value = I::translate_expr(expression, context)?;
                if let Some(types) = value.get_type(context) {
                    let local = context.create_temp(types.clone());
                    context.push_statement(MediumStatement::StorageLive(local, types));
                    context.push_statement(MediumStatement::Assign {
                        place: Place {
                            local,
                            projection: vec![],
                        },
                        value,
                    });
                }
            }
            HighStatement::CodeBlock(expressions) => {
                for expression in expressions {
                    I::translate_stmt(expression, context)?;
                }
            }
            HighStatement::If {
                conditions,
                else_branch,
            } => compile_if(conditions, else_branch, context)?,
            HighStatement::For {
                condition: _condition,
            } => {
                todo!()
            }
            HighStatement::While { condition } => compile_while(condition, context)?,
            HighStatement::Loop { body } => compile_loop::<I>(body, context)?,
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

fn compile_if<'a, I: SyntaxLevel + Translatable<I, MediumSyntaxLevel>>(
    conditions: &Vec<Conditional<I>>,
    else_branch: &Option<Vec<I::Statement>>,
    context: &mut MirFunctionContext<'a>,
) -> Result<(), CompileError> {
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
        if matches!(
            context.code_blocks[context.current_block].terminator,
            MediumTerminator::Unreachable
        ) {
            context.set_terminator(MediumTerminator::Goto(end));
        }
    }
    context.switch_to_block(current);
    if let Some(else_branch) = else_branch {
        for statement in else_branch {
            I::translate_stmt(statement, context)?;
        }
    }
    if matches!(
        context.code_blocks[context.current_block].terminator,
        MediumTerminator::Unreachable
    ) {
        context.set_terminator(MediumTerminator::Goto(end));
    }
    context.switch_to_block(end);
    Ok(())
}

fn compile_while<
    'a,
    I: SyntaxLevel + Translatable<I, MediumSyntaxLevel>,
>(
    condition: &Conditional<I>,
    context: &mut MirFunctionContext<'a>,
) -> Result<(), CompileError> {
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
    if matches!(
        context.code_blocks[context.current_block].terminator,
        MediumTerminator::Unreachable
    ) {
        context.set_terminator(MediumTerminator::Goto(top));
    }
    context.switch_to_block(end);
    Ok(())
}

fn compile_loop<'a, I: SyntaxLevel + Translatable<I, MediumSyntaxLevel>>(
    body: &Vec<I::Statement>,
    context: &mut MirFunctionContext<'a>,
) -> Result<(), CompileError> {
    let top = context.create_block();
    let end = context.create_block();
    context.switch_to_block(top);
    context.parent_loop = Some(top);
    context.parent_end = Some(end);

    // Translate the body
    for statement in body {
        I::translate_stmt(statement, context)?;
    }
    if matches!(
        context.code_blocks[context.current_block].terminator,
        MediumTerminator::Unreachable
    ) {
        context.set_terminator(MediumTerminator::Goto(top));
    }
    context.switch_to_block(end);
    Ok(())
}
