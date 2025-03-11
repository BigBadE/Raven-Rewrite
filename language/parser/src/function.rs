use crate::code::function_body;
use crate::util::{identifier, ignored, modifiers, parameter};
use crate::{IResult, Span};
use lasso::Spur;
use nom::bytes::complete::tag;
use nom::combinator::{map, opt};
use nom::multi::separated_list0;
use nom::sequence::{delimited, preceded, tuple};
use nom_supreme::ParserExt;
use syntax::structure::function::RawFunction;

// Parser for function declarations
pub fn parse_function(input: Span) -> IResult<Span, RawFunction> {
    map(
        tuple((
            modifiers.context("Modifiers"),
            preceded(delimited(ignored, tag("fn"), ignored), identifier).context("Keyword"),
            parameter_list.context("Params"),
            return_type.context("Return"),
            function_body.context("Code"),
        )).context("Function"),
        |(modifiers, name, parameters, return_type, body)| RawFunction {
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
fn parameter_list(input: Span) -> IResult<Span, Vec<(Spur, Spur)>> {
    delimited(
        delimited(ignored, tag("("), ignored),
        separated_list0(delimited(ignored, tag(","), ignored), parameter).context("Parameter"),
        delimited(ignored, tag(")"), ignored),
    )(input)
}

// Parser for return type (optional)
fn return_type(input: Span) -> IResult<Span, Option<Spur>> {
    opt(preceded(delimited(ignored, tag("->"), ignored), identifier))(input)
}