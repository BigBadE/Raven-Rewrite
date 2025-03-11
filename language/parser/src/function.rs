use crate::code::function_body;
use crate::util::ignored;
use crate::{IResult, Span};
use lasso::Spur;
use nom::bytes::complete::tag;
use nom::character::complete::{alpha1, alphanumeric1, multispace0};
use nom::combinator::{map, opt, peek, recognize};
use nom::error;
use nom::multi::{many0, separated_list0};
use nom::sequence::{delimited, pair, preceded, terminated, tuple};
use nom::Err::Error;
use nom_supreme::error::{BaseErrorKind, ErrorTree};
use nom_supreme::ParserExt;
use syntax::structure::function::RawFunction;
use syntax::structure::{Modifier, MODIFIERS};

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

// Parser for identifiers (function names, parameter names)
fn identifier(input: Span) -> IResult<Span, Spur> {
    map(recognize(pair(alpha1, many0(alphanumeric1))), |s: Span| {
        s.extra.intern(s.to_string())
    })(input)
}

// Parser for parameter declarations (identifier: type)
fn parameter(input: Span) -> IResult<Span, (Spur, Spur)> {
    tuple((
        identifier,
        delimited(ignored, tag(":"), ignored),
        identifier,
    ))(input)
        .map(|(remaining, (name, _, type_name))| (remaining, (name, type_name)))
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

// Parser for modifiers
fn modifiers(input: Span) -> IResult<Span, Vec<Modifier>> {
    many0(modifier)(input)
}

fn modifier(input: Span) -> IResult<Span, Modifier> {
    // Peek to check if the next identifier is a valid modifier.
    let (i, id) = peek(identifier)(input)?;
    if let Some(&modif) = MODIFIERS.get(i.extra.interner.resolve(&id)) {
        // Consume the identifier and following whitespace.
        let (i, _) = terminated(identifier, multispace0)(i)?;
        Ok((i, modif))
    } else {
        // Return an error without consuming input.
        Err(Error(ErrorTree::Base { location: i, kind: BaseErrorKind::Kind(error::ErrorKind::Tag) }))
    }
}