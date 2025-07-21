use crate::statement::MediumStatement;
use crate::{MediumSyntaxLevel, MediumTerminator, MirFunctionContext, Operand, Place};
use hir::expression::HighExpression;
use hir::function::HighFunction;
use hir::statement::HighStatement;
use hir::HighSyntaxLevel;
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::ops::Deref;
use syntax::structure::literal::Literal;
use syntax::structure::traits::Expression;
use syntax::structure::visitor::Translate;
use syntax::util::translation::{translate_fields, translate_iterable, Translatable};
use syntax::util::CompileError;
use syntax::{FunctionRef, GenericFunctionRef, GenericTypeRef, SyntaxLevel, TypeRef};

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
        /// The return type
        return_type: Option<T::TypeReference>,
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

impl<T: SyntaxLevel<FunctionReference=FunctionRef, TypeReference=TypeRef>,
> MediumExpression<T> {
    /// Get the returned type of the expression
    pub fn get_type(&self, context: &mut MirFunctionContext) -> Result<Option<TypeRef>, CompileError> {
        Ok(match self {
            MediumExpression::Use(op) => Some(op.get_type(context)),
            MediumExpression::Literal(lit) => Some(lit.get_type(&context.source.syntax.symbols)),
            MediumExpression::FunctionCall { return_type, .. } => {
                return_type.clone()
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
    let func_def = &context.source.syntax.functions[function];

    if func_def.generics.is_empty() {
        return create_non_generic_function_call(function, arguments, context);
    }

    let translated_args: Vec<Operand> = translate_iterable(&arguments, context, |arg, context| {
        HighSyntaxLevel::translate_expr(arg, context).and_then(|expr| get_operand(expr, context))
    })?;
    let substitutions = infer_generic_types_with_partial(func_def, &translated_args, &function.generics, context)?;

    if substitutions.is_empty() && function.generics.is_empty() {
        return create_non_generic_function_call(function, arguments, context);
    }

    let complete_generics = build_complete_generics(func_def, &function.generics, &substitutions, context)?;
    create_generic_function_call(function, func_def, complete_generics, translated_args, substitutions, context)
}

/// Creates a function call for non-generic functions or when no generics can be inferred
fn create_non_generic_function_call<'a>(
    function: &GenericFunctionRef,
    arguments: Vec<&HighExpression<HighSyntaxLevel>>,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    let func_def = &context.source.syntax.functions[function];
    let func_ref = HighSyntaxLevel::translate_func_ref(function, context)?;
    let args = translate_iterable(&arguments, context, |arg, context| {
        HighSyntaxLevel::translate_expr(arg, context).and_then(|expr| get_operand(expr, context))
    })?;

    Ok(MediumExpression::FunctionCall {
        func: func_ref,
        return_type: func_def.return_type.as_ref()
            .map(|ret| HighSyntaxLevel::translate_type_ref(ret, context))
            .transpose()?,
        args,
    })
}

/// Creates a function call for generic functions with resolved type parameters
fn create_generic_function_call<'a>(
    function: &GenericFunctionRef,
    func_def: &HighFunction<HighSyntaxLevel>,
    complete_generics: Vec<GenericTypeRef>,
    translated_args: Vec<Operand>,
    substitutions: HashMap<GenericTypeRef, TypeRef>,
    context: &mut MirFunctionContext<'a>,
) -> Result<MediumExpression<MediumSyntaxLevel>, CompileError> {
    let mut function_to_call = function.clone();
    function_to_call.generics = complete_generics;

    let old_generics = context.generics.clone();
    context.generics.extend(substitutions.clone());

    let func_ref = HighSyntaxLevel::translate_func_ref(&function_to_call, context)?;
    context.generics = old_generics;

    let return_type = func_def.return_type.as_ref()
        .map(|ret| {
            let mut return_type_with_substitutions = ret.clone();
            if let Ok(substituted) = return_type_with_substitutions.substitute_generics_in_type(&substitutions) {
                return_type_with_substitutions = substituted;
            }
            HighSyntaxLevel::translate_type_ref(&return_type_with_substitutions, context)
        })
        .transpose()?;

    Ok(MediumExpression::FunctionCall {
        func: func_ref,
        return_type,
        args: translated_args,
    })
}

/// Builds complete generic type list by combining provided and inferred types
fn build_complete_generics(
    func_def: &HighFunction<HighSyntaxLevel>,
    provided_generics: &Vec<GenericTypeRef>,
    substitutions: &HashMap<GenericTypeRef, TypeRef>,
    context: &MirFunctionContext,
) -> Result<Vec<GenericTypeRef>, CompileError> {
    let mut complete_generics = provided_generics.clone();
    for generic_param in func_def.generics.keys().skip(provided_generics.len()) {
        let generic_ref = GenericTypeRef::Generic { reference: vec![*generic_param] };
        complete_generics.push(GenericTypeRef::from(substitutions.get(&generic_ref)
            .ok_or_else(|| CompileError::Basic(format!(
                "Could not infer type for generic parameter: {}",
                context.source.syntax.symbols.resolve(generic_param))))?.clone()));
    }

    Ok(complete_generics)
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
            } => {
                let combined_args = target
                    .as_ref()
                    .map(|target| vec![target.deref()])
                    .unwrap_or_default()
                    .into_iter()
                    .chain(arguments)
                    .collect();
                translate_function(function, combined_args, context)?
            }
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
            HighExpression::UnaryOperation { pre, symbol, value } => {
                let operations = if *pre {
                    &context.source.pre_unary_operations
                } else {
                    &context.source.post_unary_operations
                };
                get_operation(operations, symbol, vec![value], context)?
            }
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


/// Enhanced version that handles partial type specification.
///
/// This function can handle cases where some generic types are explicitly provided
/// and others need to be inferred from arguments.
fn infer_generic_types_with_partial(
    func_def: &HighFunction<HighSyntaxLevel>,
    translated_args: &[Operand],
    provided_generics: &[GenericTypeRef],
    context: &mut MirFunctionContext,
) -> Result<HashMap<GenericTypeRef, TypeRef>, CompileError> {
    // Check that we have the right number of arguments
    if func_def.parameters.len() != translated_args.len() {
        return Err(CompileError::Basic(format!(
            "Function expects {} arguments, got {}",
            func_def.parameters.len(),
            translated_args.len()
        )));
    }

    let mut substitutions = HashMap::new();
    add_provided_generics_to_substitutions(func_def, provided_generics, &mut substitutions)?;

    // Unify each parameter type with its corresponding argument type
    for ((_, param_type), arg_type) in func_def.parameters.iter().zip(translated_args) {
        let actual_type = GenericTypeRef::from(arg_type.get_type(context));
        unify_types(param_type, &actual_type, &mut substitutions)?;
    }

    // Verify that all generic parameters are now resolved
    if let Some(failed) = func_def.generics.keys().find(|generic_param|
        !substitutions.contains_key(&GenericTypeRef::Generic { reference: vec![**generic_param] })) {
        return Err(CompileError::Basic(format!(
            "Could not infer type for generic parameter: {}",
            context.source.syntax.symbols.resolve(failed)
        )));
    }

    Ok(substitutions)
}

/// Performs type unification between a formal parameter type (which may contain
/// generic variables) and an actual argument type (concrete).
///
/// This implements the core unification algorithm that handles:
/// - Basic generic variable substitution: T → i32
/// - Nested generic structures: Vec<T> ∪ Vec<i32> → {T: i32}
/// - Consistency checking: T ∪ i32, then T ∪ f64 → Error
/// - Complex nested cases: Pair<T, Vec<T>> ∪ Pair<i32, Vec<i32>> → {T: i32}
pub fn unify_types(
    formal: &GenericTypeRef,
    actual: &GenericTypeRef,
    substitutions: &mut HashMap<GenericTypeRef, TypeRef>,
) -> Result<(), CompileError> {
    match (formal, actual) {
        (GenericTypeRef::Generic { reference: formal_ref }, actual) => {
            unify_generic_with_actual(formal_ref, actual, substitutions)
        }
        (
            GenericTypeRef::Struct { reference: formal_ref, generics: formal_generics },
            GenericTypeRef::Struct { reference: actual_ref, generics: actual_generics }
        ) => {
            unify_struct_types(formal_ref, formal_generics, actual_ref, actual_generics, substitutions)
        }
        (GenericTypeRef::Struct { .. }, GenericTypeRef::Generic { .. }) => {
            Err(CompileError::Basic(
                "Cannot unify concrete type with generic variable".to_string()
            ))
        }
    }
}

/// Unifies a generic variable with an actual type
fn unify_generic_with_actual(
    formal_ref: &Vec<Spur>,
    actual: &GenericTypeRef,
    substitutions: &mut HashMap<GenericTypeRef, TypeRef>,
) -> Result<(), CompileError> {
    let formal_generic = GenericTypeRef::Generic { reference: formal_ref.clone() };

    let Some(existing_type) = substitutions.get(&formal_generic) else {
        return record_new_substitution(formal_generic, actual, substitutions);
    };

    // Verify consistency: the same generic must always map to the same concrete type
    if !types_equivalent(&GenericTypeRef::from(existing_type.clone()), actual)? {
        return Err(CompileError::Basic(
            "Type conflict: generic parameter inferred as conflicting types".to_string()
        ));
    }
    Ok(())
}


/// Records a new substitution for a generic variable
fn record_new_substitution(
    formal_generic: GenericTypeRef,
    actual: &GenericTypeRef,
    substitutions: &mut HashMap<GenericTypeRef, TypeRef>,
) -> Result<(), CompileError> {
    match actual {
        GenericTypeRef::Struct { reference, generics } => {
            if generics.is_empty() {
                substitutions.insert(formal_generic, reference.clone());
                Ok(())
            } else {
                Err(CompileError::Basic(
                    "Cannot substitute generic variable with parameterized type".to_string()
                ))
            }
        }
        GenericTypeRef::Generic { .. } => {
            Err(CompileError::Basic(
                "Cannot substitute generic variable with another generic".to_string()
            ))
        }
    }
}

/// Unifies two struct types structurally
fn unify_struct_types(
    formal_ref: &TypeRef,
    formal_generics: &[GenericTypeRef],
    actual_ref: &TypeRef,
    actual_generics: &[GenericTypeRef],
    substitutions: &mut HashMap<GenericTypeRef, TypeRef>,
) -> Result<(), CompileError> {
    // Base type constructors must match
    if formal_ref != actual_ref {
        return Err(CompileError::Basic(
            "Type constructor mismatch: cannot unify types".to_string()
        ));
    }

    // Arity must match
    if formal_generics.len() != actual_generics.len() {
        return Err(CompileError::Basic(format!(
            "Arity mismatch: {} vs {} type parameters",
            formal_generics.len(),
            actual_generics.len()
        )));
    }

    // Recursively unify each type parameter
    for (formal_param, actual_param) in formal_generics.iter().zip(actual_generics.iter()) {
        unify_types(formal_param, actual_param, substitutions)?;
    }

    Ok(())
}


/// Checks if two types are equivalent after applying current substitutions.
/// This is used for consistency checking during unification.
pub fn types_equivalent(
    type1: &GenericTypeRef,
    type2: &GenericTypeRef,
) -> Result<bool, CompileError> {
    match (type1, type2) {
        (
            GenericTypeRef::Struct { reference: ref1, generics: gen1 },
            GenericTypeRef::Struct { reference: ref2, generics: gen2 }
        ) => {
            if ref1 != ref2 || gen1.len() != gen2.len() {
                return Ok(false);
            }

            for (g1, g2) in gen1.iter().zip(gen2.iter()) {
                if !types_equivalent(g1, g2)? {
                    return Ok(false);
                }
            }

            Ok(true)
        }
        (
            GenericTypeRef::Generic { reference: ref1 },
            GenericTypeRef::Generic { reference: ref2 }
        ) => Ok(ref1 == ref2),
        _ => Ok(false),
    }
}


/// Adds explicitly provided generic types to the substitutions map
fn add_provided_generics_to_substitutions(
    func_def: &HighFunction<HighSyntaxLevel>,
    provided_generics: &[GenericTypeRef],
    substitutions: &mut HashMap<GenericTypeRef, TypeRef>,
) -> Result<(), CompileError> {
    for (generic_param, provided_generic) in func_def.generics.keys().zip(provided_generics) {
        let generic_key = GenericTypeRef::Generic { reference: vec![*generic_param] };
        convert_and_add_provided_generic(provided_generic, generic_key, substitutions)?;
    }
    Ok(())
}

/// Converts a provided generic to concrete type and adds it to substitutions
fn convert_and_add_provided_generic(
    provided_generic: &GenericTypeRef,
    generic_key: GenericTypeRef,
    substitutions: &mut HashMap<GenericTypeRef, TypeRef>,
) -> Result<(), CompileError> {
    if let GenericTypeRef::Struct { reference, generics } = provided_generic {
        if generics.is_empty() {
            substitutions.insert(generic_key, reference.clone());
            Ok(())
        } else {
            Err(CompileError::Basic(
                "Cannot use parameterized type as explicit generic parameter".to_string()
            ))
        }
    } else {
        Err(CompileError::Basic(
            "Invalid explicit generic parameter".to_string()
        ))
    }
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
