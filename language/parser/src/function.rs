use std::collections::HashMap;
use crate::code::function_body;
use crate::util::{identifier_symbolic, ignored, modifiers, parameter, type_ref};
use crate::{IResult, Span};
use hir::function::HighFunction;
use hir::{RawSyntaxLevel, RawTypeRef};
use lasso::Spur;
use nom::Parser;
use nom::bytes::complete::tag;
use nom::combinator::{map, opt};
use nom::multi::separated_list0;
use nom::sequence::{delimited, preceded, tuple};
use nom_supreme::ParserExt;
use crate::structure::generics;

/// Parser for function declarations
pub fn function(input: Span) -> IResult<Span, HighFunction<RawSyntaxLevel>> {
    map(
        tuple((
            modifiers,
            preceded(delimited(ignored, tag("fn"), ignored), identifier_symbolic)
                .context("Keyword"),
            generics,
            parameter_list,
            return_type,
            function_body,
        ))
        .context("Function"),
        |(modifiers, name, generics, parameters, return_type, body)| HighFunction {
            file: input.extra.file.clone(),
            modifiers,
            name,
            generics: HashMap::from_iter(generics.into_iter()),
            parameters,
            return_type,
            body,
        },
    )(input.clone())
}

/// Parser for parameter lists
fn parameter_list(input: Span) -> IResult<Span, Vec<(Spur, RawTypeRef)>> {
    delimited(
        delimited(ignored, tag("("), ignored),
        separated_list0(delimited(ignored, tag(","), ignored), parameter),
        delimited(ignored, tag(")"), ignored),
    )
    .context("Parameters")
    .parse(input)
}

/// Parser for return type (optional)
fn return_type(input: Span) -> IResult<Span, Option<RawTypeRef>> {
    opt(preceded(delimited(ignored, tag("->"), ignored), type_ref))
        .context("ReturnType")
        .parse(input)
}
