use crate::SyntaxLevel;
use crate::util::ParseError;
use lasso::Spur;

pub fn translate_fields<C, I, O, F: Fn(&I, &mut C) -> Result<O, ParseError>>(
    fields: &Vec<(Spur, I)>,
    context: &mut C,
    translator: F,
) -> Result<Vec<(Spur, O)>, ParseError> {
    translate_vec(fields, context, |(name, value), context| {
        Ok::<_, ParseError>((*name, translator(value, context)?))
    })
}

pub fn translate_vec<C, I, O, F: Fn(&I, &mut C) -> Result<O, ParseError>>(
    fields: &Vec<I>,
    context: &mut C,
    translator: F,
) -> Result<Vec<O>, ParseError> {
    let (fields, errors) = fields
        .iter()
        .map(|input| Ok::<_, ParseError>(translator(input, context)?))
        .fold((vec![], vec![]), |mut acc, item| {
            match item {
                Ok(value) => acc.0.push(value),
                Err(err) => acc.1.push(err),
            }
            acc
        });
    if !errors.is_empty() {
        Err(ParseError::MultiError(errors))
    } else {
        Ok(fields)
    }
}

/// This trait is used to say a Syntax can be translated from one type to another
/// MUST be manually implemented to prevent recursive loops
pub trait Translatable<C, I: SyntaxLevel, O: SyntaxLevel> {
    fn translate_stmt(node: &I::Statement, context: &mut C) -> Result<O::Statement, ParseError>;

    fn translate_expr(node: &I::Expression, context: &mut C) -> Result<O::Expression, ParseError>;

    fn translate_type_ref(
        node: &I::TypeReference,
        context: &mut C,
    ) -> Result<O::TypeReference, ParseError>;
    fn translate_func_ref(
        node: &I::FunctionReference,
        context: &mut C,
    ) -> Result<O::FunctionReference, ParseError>;
    fn translate_type(node: &I::Type, context: &mut C) -> Result<Option<O::Type>, ParseError>;
    fn translate_func(node: &I::Function, context: &mut C) -> Result<O::Function, ParseError>;
    fn translate_terminator(
        node: &I::Terminator,
        context: &mut C,
    ) -> Result<O::Terminator, ParseError>;
}
