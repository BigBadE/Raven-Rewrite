use crate::{IResult, Span};
use hir::RawTypeRef;
use lasso::Spur;
use nom::branch::alt;
use nom::bytes::complete::{tag, take_till, take_until, take_while1};
use nom::character::complete::{alpha1, alphanumeric0, multispace0, multispace1};
use nom::combinator::{eof, map, opt, peek, recognize, value};
use nom::multi::{many0, separated_list0, separated_list1};
use nom::sequence::{delimited, pair, preceded, terminated, tuple};
use nom::Err::Error;
use nom::{error, Parser};
use syntax::structure::{Modifier, MODIFIERS};
use syntax::util::path::FilePath;
use crate::errors::ParserError;
use nom::error::ParseError;

/// For parsing file paths like foo::bar::baz
pub fn file_path(input: Span) -> IResult<Span, FilePath> {
    separated_list1(tag("::"), identifier)(input)
}

/// Parses a type ref like foo::bar::Baz<Trait, Trait>
pub fn type_ref(input: Span) -> IResult<Span, RawTypeRef> {
    map(
        tuple((
            file_path,
            opt(delimited(tag("<"), separated_list0(delimited(ignored, tag(","), ignored), type_ref), tag(">"))),
        )),
        |(path, generics)| RawTypeRef { path, generics: generics.unwrap_or_default() },
    )(input)
}

/// Parser for identifiers (function names, parameter names)
pub fn identifier(input: Span) -> IResult<Span, Spur> {
    map(recognize(pair(alpha1, many0(alt((tag("_"), alphanumeric0))))), |s: Span| {
        s.extra.intern(s.to_string())
    })
        .parse(input)
}

/// Parses either an identifier or a symbolic operator
pub fn identifier_symbolic(input: Span) -> IResult<Span, Spur> {
    alt((identifier, symbolic))
        .parse(input)
}

/// Parses a symbolic operator, which is composed entirely of symbols
pub fn symbolic(input: Span) -> IResult<Span, Spur> {
    map(
        take_while1(|c: char| "+-*/%&|^!~=<>?:".contains(c)),
        |s: Span| s.extra.intern(s.to_string()),
    )
        .parse(input)
}

/// Parser for parameter declarations (identifier: type)
pub fn parameter(input: Span) -> IResult<Span, (Spur, RawTypeRef)> {
    tuple((
        identifier,
        preceded(delimited(ignored, tag(":"), ignored), type_ref),
    ))
        .parse(input)
}

/// Parser for modifiers
pub fn modifiers(input: Span) -> IResult<Span, Vec<Modifier>> {
    many0(modifier).parse(input)
}

/// Parser for a single modifier
fn modifier(input: Span) -> IResult<Span, Modifier> {
    // Peek to check if the next identifier is a valid modifier.
    let (i, id) = peek(identifier)(input.clone())?;
    if let Some(&modif) = MODIFIERS.get(i.extra.interner.resolve(&id)) {
        // Consume the identifier and following whitespace.
        let (i, _) = terminated(identifier, multispace0)(i)?;
        Ok((i, modif))
    } else {
        // Return an error without consuming input.
        Err(Error(ParserError::from_error_kind(input, error::ErrorKind::Tag)))
    }
}

/// Parser for single-line comments (// ...)
fn single_line_comment(input: Span) -> IResult<Span, ()> {
    value(
        (), // We don't need to capture the comment content
        delimited(tag("//"), take_till(|c| c == '\n'), alt((tag("\n"), eof))),
    )(input)
}

/// Parser for multi-line comments (/* ... */)
fn multi_line_comment(input: Span) -> IResult<Span, ()> {
    value((), delimited(tag("/*"), take_until("*/"), tag("*/")))(input)
}

/// Parser for whitespace and comments
fn whitespace_or_comment(input: Span) -> IResult<Span, ()> {
    alt((
        value((), multispace1), // Matches whitespace (including newlines)
        single_line_comment,
        multi_line_comment,
    ))(input)
}

/// Parser that consumes any amount of whitespace and comments
pub fn ignored(input: Span) -> IResult<Span, ()> {
    value((), many0(whitespace_or_comment))
        .parse(input)
}
