use indexmap::IndexMap;
use crate::code::function_body;
use crate::errors::expect;
use crate::util::{identifier_symbolic, ignored, modifiers, parameter, tag_parser, type_ref};
use crate::{IResult, Span};
use hir::function::HighFunction;
use hir::{RawSyntaxLevel, RawTypeRef};
use lasso::Spur;
use nom::Parser;
use nom::bytes::complete::tag;
use nom::combinator::{map, opt};
use nom::multi::separated_list0;
use nom::sequence::{delimited, preceded, tuple};
use crate::structure::generics;

/// Parser for function declarations
pub fn function(input: Span) -> IResult<Span, HighFunction<RawSyntaxLevel>> {
    map(
        tuple((
            modifiers,
            preceded(delimited(ignored, expect(tag_parser("fn"), "function keyword 'fn'", Some("functions must start with 'fn'")), ignored), identifier_symbolic),
            generics,
            parameter_list,
            return_type,
            function_body,
        )),
        |(modifiers, name, generics, parameters, return_type, body)| {
            let mut reference = input.extra.file.clone();
            reference.push(name);
            HighFunction {
                reference: reference.into(),
                modifiers,
                generics: IndexMap::from_iter(generics.into_iter()),
                parameters,
                return_type,
                body,
            }
        },
    )(input.clone())
}

/// Parser for parameter lists
fn parameter_list(input: Span) -> IResult<Span, Vec<(Spur, RawTypeRef)>> {
    delimited(
        delimited(ignored, expect(tag_parser("("), "opening parenthesis '('", Some("parameter lists must start with '('")), ignored),
        separated_list0(delimited(ignored, tag(","), ignored), parameter),
        delimited(ignored, expect(tag_parser(")"), "closing parenthesis ')'", Some("parameter lists must end with ')'")), ignored),
    )
    .parse(input)
}

/// Parser for return type (optional)
fn return_type(input: Span) -> IResult<Span, Option<RawTypeRef>> {
    opt(preceded(delimited(ignored, expect(tag_parser("->"), "return type arrow '->'", Some("use '->' to specify return type")), ignored), type_ref))
        .parse(input)
}
