use crate::statement::MediumStatement;
use crate::{MediumSyntaxLevel, MediumTerminator, MirFunctionContext, Operand, Place};
use hir::expression::HighExpression;
use hir::function::HighTerminator;
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::ops::Deref;
use syntax::structure::literal::Literal;
use syntax::structure::traits::Expression;
use syntax::structure::visitor::Translate;
use syntax::util::translation::{translate_fields, translate_vec, Translatable};
use syntax::util::CompileError;
use syntax::{FunctionRef, SyntaxLevel, TypeRef};

/// An expression in the MIR
#[derive(Serialize, Deserialize, Debug)]
pub enum MediumExpression<T: SyntaxLevel> {
    /// Uses the operand
    Use(Operand),
    /// A literal
    Literal(Literal),
    /// A function call
    FunctionCall {
        /// The function
        func: T::FunctionReference,
        /// The arguments
        args: Vec<Operand>,
    },
    /// Creates a struct
    CreateStruct {
        /// The struct's type
        struct_type: T::TypeReference,
        /// The fields
        fields: Vec<(Spur, Operand)>,
    },
}

impl<T: SyntaxLevel> Expression for MediumExpression<T> {}

impl<T: SyntaxLevel<FunctionReference = FunctionRef, TypeReference = TypeRef>> MediumExpression<T> {
    /// Get the returned type of the expression
    pub fn get_type(&self, context: &MirFunctionContext) -> Option<TypeRef> {
        match self {
            MediumExpression::Use(op) => Some(op.get_type(context)),
            MediumExpression::Literal(lit) => Some(lit.get_type()),
            MediumExpression::FunctionCall { func, .. } => {
                context.source.syntax.functions[func.0].return_type
            }
            MediumExpression::CreateStruct { struct_type, .. } => Some(struct_type.clone()),
        }
    }
}

/// Convert an expression into an operand.
pub fn get_operand(
    expr: MediumExpression<MediumSyntaxLevel>,
    context: &mut MirFunctionContext,
) -> Operand {
    match expr {
        MediumExpression::Literal(lit) => Operand::Constant(lit),
        MediumExpression::Use(op) => op,
        value => {
            // This is checked to be non-void before.
            let ty = value.get_type(context).unwrap();
            let temp = context.create_temp(ty);
            context.push_statement(MediumStatement::Assign {
                place: Place {
                    local: temp,
                    projection: vec![],
                },
                value,
            });
            Operand::Copy(Place {
                local: temp,
                projection: vec![],
            })
        }
    }
}

/// Translates a single function into its MIR equivalent.
pub fn translate_function<
    'a,
    I: SyntaxLevel<Terminator = HighTerminator<I>>
        + Translatable<MirFunctionContext<'a>, I, MediumSyntaxLevel>,
>(
    function: &I::FunctionReference,
    arguments: Vec<&I::Expression>,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    Ok(MediumExpression::FunctionCall {
        func: I::translate_func_ref(function, context)?,
        args: translate_vec(&arguments, context, |arg, context| {
            I::translate_expr(arg, context).map(|expr| get_operand(expr, context))
        })?,
    })
}

/// Handle statement translation
impl<
        'a,
        I: SyntaxLevel<Terminator = HighTerminator<I>, FunctionReference = FunctionRef>
            + Translatable<MirFunctionContext<'a>, I, MediumSyntaxLevel>,
    > Translate<MediumExpression<MediumSyntaxLevel>, MirFunctionContext<'a>> for HighExpression<I>
{
    fn translate(
        &self,
        context: &mut MirFunctionContext<'a>,
    ) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
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
            HighExpression::Variable(var) => {
                let local = context.get_local(*var).cloned();
                MediumExpression::Use(Operand::Copy(Place {
                    local: local.ok_or_else(|| {
                        CompileError::Basic(format!(
                            "Unknown variable: {}",
                            context.source.syntax.symbols.resolve(var)
                        ))
                    })?,
                    projection: vec![],
                }))
            }
            // For assignment, translate the right-hand side, emit an assign statement,
            // then return a use of the target variable.
            HighExpression::Assignment {
                declaration,
                variable,
                value,
            } => translate_assign::<I>(declaration, variable, value, context)?,
            // For function calls, translate the function reference and arguments.
            HighExpression::FunctionCall {
                function,
                target,
                arguments,
            } => translate_function::<I>(
                function,
                target
                    .as_ref()
                    .map(|target| vec![target.deref()])
                    .unwrap_or_default()
                    .into_iter()
                    .chain(arguments)
                    .collect(),
                context,
            )?,
            // For create-struct, translate the type and each field.
            HighExpression::CreateStruct {
                target_struct,
                fields,
            } => MediumExpression::CreateStruct {
                struct_type: I::translate_type_ref(target_struct, context)?,
                fields: translate_fields(fields, context, |field, context| {
                    I::translate_expr(field, context).map(|expr| get_operand(expr, context))
                })?,
            },
            HighExpression::UnaryOperation { pre, symbol, value } => get_operation::<I>(
                if *pre {
                    &context.source.pre_unary_operations
                } else {
                    &context.source.post_unary_operations
                },
                symbol,
                vec![value],
                context,
            )?,
            HighExpression::BinaryOperation {
                symbol,
                first,
                second,
            } => get_operation::<I>(
                &context.source.binary_operations,
                symbol,
                vec![first, second],
                context,
            )?,
        })
    }
}

fn get_operation<
    'a,
    I: SyntaxLevel<FunctionReference = FunctionRef, Terminator = HighTerminator<I>>
        + Translatable<MirFunctionContext<'a>, I, MediumSyntaxLevel>,
>(
    operations: &HashMap<Spur, Vec<FunctionRef>>,
    symbol: &Spur,
    args: Vec<&I::Expression>,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    translate_function::<I>(
        &operations.get(symbol).ok_or_else(|| {
            CompileError::Basic(format!(
                "Unknown operation {}",
                context.source.syntax.symbols.resolve(symbol)
            ))
        })?[0],
        // TODO type check to get the right one
        args,
        context,
    )
}

fn translate_assign<
    'a,
    I: SyntaxLevel + Translatable<MirFunctionContext<'a>, I, MediumSyntaxLevel>,
>(
    declaration: &bool,
    variable: &Spur,
    value: &I::Expression,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    if !context.local_vars.contains_key(variable) && !declaration {
        return Err(CompileError::Basic("Unknown variable!".to_string()));
    }

    let value = I::translate_expr(value, context)?;
    let types = value.get_type(context);
    let Some(types) = types else {
        return Err(CompileError::Basic("Expected non-void type!".to_string()));
    };

    let place = Place {
        local: context.get_or_create_local(*variable, types),
        projection: Vec::new(),
    };

    if *declaration {
        context.push_statement(MediumStatement::StorageLive(place.local, types))
    }

    // Emit the assignment as a side-effect.
    context.push_statement(MediumStatement::Assign {
        place: place.clone(),
        value,
    });

    Ok(MediumExpression::Use(Operand::Move(place)))
}
