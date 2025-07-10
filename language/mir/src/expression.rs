use crate::statement::MediumStatement;
use crate::{MediumSyntaxLevel, MediumTerminator, MirFunctionContext, Operand, Place};
use hir::expression::HighExpression;
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::ops::Deref;
use hir::HighSyntaxLevel;
use hir::statement::HighStatement;
use syntax::structure::literal::Literal;
use syntax::structure::traits::Expression;
use syntax::structure::visitor::Translate;
use syntax::util::translation::{translate_fields, translate_iterable, Translatable};
use syntax::util::CompileError;
use syntax::{FunctionRef, GenericFunctionRef, SyntaxLevel, TypeRef};

/// An expression in the MIR
#[derive(Serialize, Deserialize, Clone)]
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

impl<T: SyntaxLevel<FunctionReference = FunctionRef, TypeReference = TypeRef>,
    > MediumExpression<T> {
    /// Get the returned type of the expression
    pub fn get_type(&self, context: &mut MirFunctionContext) -> Result<Option<TypeRef>, CompileError> {
        Ok(match self {
            MediumExpression::Use(op) => Some(op.get_type(context)),
            MediumExpression::Literal(lit) => Some(lit.get_type(&context.source.syntax.symbols)),
            MediumExpression::FunctionCall { func, .. } => {
                context.output.functions[func].return_type.clone()
            }
            MediumExpression::CreateStruct { struct_type, .. } => Some(struct_type.clone()),
        })
    }
}

/// Convert an expression into an operand.
pub fn get_operand(
    expr: MediumExpression<MediumSyntaxLevel>,
    context: &mut MirFunctionContext,
) -> Result<Operand, CompileError> {
    match expr {
        MediumExpression::Literal(lit) => Ok(Operand::Constant(lit)),
        MediumExpression::Use(op) => Ok(op),
        value => {
            // This is checked to be non-void before.
            let ty = value.get_type(context)?.unwrap();
            let temp = context.create_temp(ty);
            context.push_statement(MediumStatement::Assign {
                place: Place {
                    local: temp,
                    projection: vec![],
                },
                value,
            });
            Ok(Operand::Copy(Place {
                local: temp,
                projection: vec![],
            }))
        }
    }
}

/// Translates a single function into its MIR equivalent.
pub fn translate_function<'a>(
    function: &GenericFunctionRef,
    arguments: Vec<&HighExpression<HighSyntaxLevel>>,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    Ok(MediumExpression::FunctionCall {
        func: HighSyntaxLevel::translate_func_ref(function, context)?,
        args: translate_iterable(&arguments, context, |arg, context| {
            HighSyntaxLevel::translate_expr(arg, context).and_then(|expr| get_operand(expr, context))
        })?,
    })
}

/// Handle statement translation
impl<'a> Translate<MediumExpression<MediumSyntaxLevel>, MirFunctionContext<'a>> for
HighExpression<HighSyntaxLevel>
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
                translate_code_block(body, value, context)?
            }
            // A variable is translated to a use of a local place.
            HighExpression::Variable(var) => translate_variable(var, context)?,
            // For assignment, translate the right-hand side, emit an assign statement,
            // then return a use of the target variable.
            HighExpression::Assignment {
                declaration,
                variable,
                value,
            } => translate_assign(declaration, variable, value, context)?,
            // For function calls, translate the function reference and arguments.
            HighExpression::FunctionCall {
                function,
                target,
                arguments,
            } => translate_function(
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
                struct_type: HighSyntaxLevel::translate_type_ref(target_struct, context)?,
                fields: translate_fields(fields, context, |field, context| {
                    HighSyntaxLevel::translate_expr(field, context).and_then(|expr| get_operand(expr, context))
                })?,
            },
            HighExpression::UnaryOperation { pre, symbol, value } => get_operation(
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
            } => get_operation(
                &context.source.binary_operations,
                symbol,
                vec![first, second],
                context,
            )?,
        })
    }
}

fn translate_variable<'a>(
    var: &Spur,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    let local = context.get_local(*var).cloned();
    Ok(MediumExpression::Use(Operand::Copy(Place {
        local: local.ok_or_else(|| {
            CompileError::Basic(format!(
                "Unknown variable: {}",
                context.source.syntax.symbols.resolve(var)
            ))
        })?,
        projection: vec![],
    })))
}

fn translate_code_block<'a>(
    body: &Vec<HighStatement<HighSyntaxLevel>>,
    value: &HighExpression<HighSyntaxLevel>,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    let start = context.create_block();
    context.set_terminator(MediumTerminator::Goto(start));
    context.switch_to_block(start);

    for statement in body {
        HighSyntaxLevel::translate_stmt(statement, context)?;
    }

    let end = context.create_block();
    context.set_terminator(MediumTerminator::Goto(end));
    context.switch_to_block(end);
    HighSyntaxLevel::translate_expr(value, context)
}

fn get_operation<'a>(
    operations: &HashMap<Spur, Vec<GenericFunctionRef>>,
    symbol: &Spur,
    args: Vec<&HighExpression<HighSyntaxLevel>>,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    translate_function(
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

fn translate_assign<'a>(
    declaration: &bool,
    variable: &Spur,
    value: &HighExpression<HighSyntaxLevel>,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    if !context.local_vars.contains_key(variable) && !declaration {
        return Err(CompileError::Basic("Unknown variable!".to_string()));
    }

    let value = HighSyntaxLevel::translate_expr(value, context)?;
    let types = value.get_type(context)?;
    let Some(types) = types else {
        return Err(CompileError::Basic("Expected non-void type!".to_string()));
    };

    let place = Place {
        local: context.get_or_create_local(*variable, types.clone()),
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
