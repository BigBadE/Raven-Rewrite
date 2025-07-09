use crate::util::CompileError;
use crate::{ContextSyntaxLevel, SyntaxLevel};
use lasso::Spur;

/// Translates a vector of fields into fields of the output type.
pub fn translate_fields<C, I, O, F: Fn(&I, &mut C) -> Result<O, CompileError>>(
    fields: &Vec<(Spur, I)>,
    context: &mut C,
    translator: F,
) -> Result<Vec<(Spur, O)>, CompileError> {
    translate_iterable(fields, context, |(name, value), context| {
        Ok::<_, CompileError>((*name, translator(value, context)?))
    })
}

/// Translates a vector into a vector of the output type.
pub fn translate_iterable<'a, Iter: IntoIterator<Item=I>, Out: Default + Extend<O>, C, I: 'a, O, F: FnMut(I, &mut C) -> Result<O, CompileError>>(
    fields: Iter,
    context: &mut C,
    mut translator: F,
) -> Result<Out, CompileError> {
    let (fields, errors) = fields
        .into_iter()
        .map(|input| Ok::<_, CompileError>(translator(input, context)?))
        .fold((Out::default(), vec![]), |mut acc, item| {
            match item {
                Ok(value) => acc.0.extend(Some(value)),
                Err(err) => acc.1.push(err),
            }
            acc
        });
    if !errors.is_empty() {
        Err(CompileError::Multi(errors))
    } else {
        Ok(fields)
    }
}

/// This trait is used to say a Syntax can be translated from one type to another
/// MUST be manually implemented to prevent recursive loops
pub trait Translatable<I: SyntaxLevel, O: ContextSyntaxLevel<I>> {
    /// Translates a statement
    fn translate_stmt(node: &I::Statement, context: &mut O::InnerContext<'_>) -> Result<O::Statement, CompileError>;

    /// Translates an expression
    fn translate_expr(node: &I::Expression, context: &mut O::InnerContext<'_>)
    -> Result<O::Expression, CompileError>;

    /// Translates a type reference
    fn translate_type_ref(
        node: &I::TypeReference,
        context: &mut O::InnerContext<'_>,
    ) -> Result<O::TypeReference, CompileError>;

    /// Translates a function reference
    fn translate_func_ref(
        node: &I::FunctionReference,
        context: &mut O::InnerContext<'_>,
    ) -> Result<O::FunctionReference, CompileError>;

    /// Translates a type
    fn translate_type(node: &I::Type, context: &mut O::InnerContext<'_>) -> Result<(), CompileError>;

    /// Translates a function
    fn translate_func(node: &I::Function, context: &mut O::InnerContext<'_>) -> Result<(), CompileError>;

    /// Translates a terminator
    fn translate_terminator(
        node: &I::Terminator,
        context: &mut O::InnerContext<'_>,
    ) -> Result<O::Terminator, CompileError>;
}
