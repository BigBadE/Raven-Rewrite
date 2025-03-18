use crate::code::literal::Literal;
use crate::hir::expression::{Expression, HighExpression};
use crate::hir::function::HighTerminator;
use crate::mir::statement::MediumStatement;
use crate::mir::{MediumSyntaxLevel, MediumTerminator, MirContext, Operand, Place};
use crate::structure::visitor::Translate;
use crate::util::translation::Translatable;
use crate::util::ParseError;
use crate::SyntaxLevel;
use lasso::Spur;

#[derive(Debug)]
pub enum MediumExpression<T: SyntaxLevel> {
    Use(Operand),
    Literal(Literal),
    FunctionCall {
        func: T::FunctionReference,
        args: Vec<Operand>,
    },
    CreateStruct {
        struct_type: T::TypeReference,
        fields: Vec<(Spur, Operand)>,
    },
}

impl<T: SyntaxLevel> Expression for MediumExpression<T> {}

// Handle statement translation
impl<I: SyntaxLevel<Terminator=HighTerminator<I>> + Translatable<MirContext, I, MediumSyntaxLevel>>
Translate<MediumExpression<MediumSyntaxLevel>, MirContext, I, MediumSyntaxLevel> for HighExpression<I>
{
    fn translate(&self, context: &mut MirContext) -> Result<MediumExpression<MediumSyntaxLevel>, ParseError> {
        // Helper conversion: converts a translated expression to an operand.
        let convert_expr = |expr: MediumExpression<MediumSyntaxLevel>| -> Operand {
            match expr {
                MediumExpression::Literal(l) => Operand::Constant(l),
                MediumExpression::Use(op) => op,
                _ => Operand::Constant(Literal::Void),
            }
        };

        Ok(match self {
            // Translate literal directly.
            HighExpression::Literal(lit) => MediumExpression::Literal(*lit),
            // Create a new block, using temps for the values until we get what we want
            HighExpression::CodeBlock { body, value } => {
                let start = context.create_block();
                context.set_terminator(MediumTerminator::Goto(start));
                context.switch_to_block(start);

                for statement in body {
                    // Translate each statement in the block.
                    I::translate_stmt(statement, context)?;
                }

                let end = context.create_block();
                context.set_terminator(MediumTerminator::Goto(end));
                context.switch_to_block(end);
                I::translate_expr(value, context)?
            }
            // A variable is translated to a use of a local place.
            HighExpression::Variable(var) =>
                MediumExpression::Use(Operand::Copy(Place {
                    local: context.get_or_create_local(*var),
                    projection: vec!(),
                })),
            // For assignment, translate the right-hand side, emit an assign statement,
            // then return a use of the target variable.
            HighExpression::Assignment { declaration, variable, value } => {
                if context.local_vars.contains_key(variable) && !declaration {
                    return Err(ParseError::ParseError("Unknown variable!".to_string()));
                }

                let place = Place {
                    local: context.get_or_create_local(*variable),
                    projection: Vec::new(),
                };

                // Emit the assignment as a side-effect.
                let assign = MediumStatement::Assign {
                    place: place.clone(),
                    value: I::translate_expr(value, context)?,
                };
                context.push_statement(assign);
                MediumExpression::Use(Operand::Move(place))
            }
            // For function calls, translate the function reference and arguments.
            HighExpression::FunctionCall { function, target, arguments } => {
                let mut args = Vec::new();
                // If there is a target (as in a method call), translate and prepend it.
                if let Some(target_expr) = target {
                    args.push(convert_expr(I::translate_expr(target_expr, context)?));
                }
                // Translate the remaining arguments.
                for arg in arguments {
                    args.push(convert_expr(I::translate_expr(arg, context)?));
                }
                MediumExpression::FunctionCall { func: I::translate_func_ref(function, context)?, args }
            }
            // For create-struct, translate the type and each field.
            HighExpression::CreateStruct { target_struct, fields } =>
                MediumExpression::CreateStruct {
                    struct_type: I::translate_type_ref(target_struct, context)?,
                    fields: fields.iter()
                        .map(|(name, expression)| Ok((*name, convert_expr(I::translate_expr(expression, context)?))))
                        .collect::<Result<_, _>>()?,
            }
        })
    }
}