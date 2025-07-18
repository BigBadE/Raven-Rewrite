use indexmap::IndexMap;
use crate::code::function_body;
use crate::errors::{expect, context};
use crate::util::{identifier_symbolic, ignored, modifiers, parameter, tag_parser, type_ref};
use crate::{IResult, Span};
use hir::function::HighFunction;
use hir::{RawSyntaxLevel, RawTypeRef};
use lasso::Spur;
use nom::Parser;
use nom::combinator::{map, opt};
use nom::multi::separated_list0;
use nom::sequence::{delimited, preceded, tuple};
use crate::structure::generics;

/// Parser for function declarations
pub fn function(input: Span) -> IResult<Span, HighFunction<RawSyntaxLevel>> {
    let original_input = input.clone();
    
    let (input, modifiers) = modifiers(input)?;
    let (input, _) = delimited(ignored, tag_parser("fn"), ignored)(input)?;
    let (input, name) = identifier_symbolic(input)?;
    let (input, generics) = generics(input)?;
    let (input, parameters) = parameter_list(input)?;
    let (input, return_type) = return_type(input)?;
    let (input, body) = function_body(input)?;
    
    let mut reference = original_input.extra.file.clone();
    reference.push(name);
    let result = HighFunction {
        reference: reference.into(),
        modifiers,
        generics: IndexMap::from_iter(generics.into_iter()),
        parameters,
        return_type,
        body,
    };
    
    Ok((input, result))
}

/// Parser for parameter lists
fn parameter_list(input: Span) -> IResult<Span, Vec<(Spur, RawTypeRef)>> {
    delimited(
        delimited(ignored, tag_parser("("), ignored),
        separated_list0(delimited(ignored, tag_parser(","), ignored), parameter),
        delimited(ignored, tag_parser(")"), ignored),
    )
    .parse(input)
}

/// Parser for return type (optional)
fn return_type(input: Span) -> IResult<Span, Option<RawTypeRef>> {
    opt(preceded(delimited(ignored, tag_parser("->"), ignored), type_ref))
        .parse(input)
}
