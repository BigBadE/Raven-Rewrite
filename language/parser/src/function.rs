use crate::code::function_body;
use crate::util::{identifier, ignored, modifiers, parameter};
use crate::{IResult, Span};
use lasso::Spur;
use nom::bytes::complete::tag;
use nom::combinator::{map, opt};
use nom::multi::separated_list0;
use nom::sequence::{delimited, preceded, tuple};
use nom_supreme::ParserExt;
use hir::function::HighFunction;
use hir::{RawSyntaxLevel, RawTypeRef};

// Parser for function declarations
pub fn function(input: Span) -> IResult<Span, HighFunction<RawSyntaxLevel>> {
    map(
        tuple((
            modifiers.context("Modifiers"),
            preceded(delimited(ignored, tag("fn"), ignored), identifier).context("Keyword"),
            parameter_list.context("Params"),
            return_type.context("Return"),
            function_body.context("Code"),
        ))
        .context("Function"),
        |(modifiers, name, parameters, return_type, body)| HighFunction {
            file: input.extra.file.clone(),
            modifiers,
            name,
            parameters,
            return_type,
            body,
        },
    )(input.clone())
}

// Parser for parameter lists
fn parameter_list(input: Span) -> IResult<Span, Vec<(Spur, RawTypeRef)>> {
    delimited(
        delimited(ignored, tag("("), ignored),
        separated_list0(delimited(ignored, tag(","), ignored), parameter).context("Parameter"),
        delimited(ignored, tag(")"), ignored),
    )(input)
}

// Parser for return type (optional)
fn return_type(input: Span) -> IResult<Span, Option<RawTypeRef>> {
    opt(preceded(
        delimited(ignored, tag("->"), ignored),
        map(identifier, |spur| RawTypeRef(spur)),
    ))(input)
}
