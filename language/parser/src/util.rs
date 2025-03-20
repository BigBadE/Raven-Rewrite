use crate::{IResult, Span};
use lasso::Spur;
use nom::branch::alt;
use nom::bytes::complete::{tag, take_till, take_until};
use nom::character::complete::{alpha1, alphanumeric1, multispace0, multispace1};
use nom::combinator::{eof, map, peek, recognize, value};
use nom::multi::{many0, separated_list1};
use nom::sequence::{delimited, pair, terminated, tuple};
use nom::Err::Error;
use nom::{error, Parser};
use nom_supreme::error::{BaseErrorKind, ErrorTree};
use nom_supreme::ParserExt;
use hir::RawTypeRef;
use syntax::structure::{Modifier, MODIFIERS};
use syntax::util::path::FilePath;

// For parsing file paths like foo::bar::baz
pub fn file_path(input: Span) -> IResult<Span, FilePath> {
    separated_list1(
        tag("::"),
        map(recognize(pair(alpha1, many0(alphanumeric1))), |s: Span| {
            s.extra.intern(s.to_string())
        }),
    )(input)
}

// Parser for identifiers (function names, parameter names)
pub fn identifier(input: Span) -> IResult<Span, Spur> {
    map(recognize(pair(alpha1, many0(alphanumeric1))), |s: Span| {
        s.extra.intern(s.to_string())
    })(input)
}

// Parser for parameter declarations (identifier: type)
pub fn parameter(input: Span) -> IResult<Span, (Spur, RawTypeRef)> {
    tuple((
        identifier,
        delimited(ignored, tag(":"), ignored),
        identifier,
    ))(input)
    .map(|(remaining, (name, _, type_name))| (remaining, (name, RawTypeRef(type_name))))
}

// Parser for modifiers
pub fn modifiers(input: Span) -> IResult<Span, Vec<Modifier>> {
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
        Err(Error(ErrorTree::Base {
            location: i,
            kind: BaseErrorKind::Kind(error::ErrorKind::Tag),
        }))
    }
}

// Parser for single-line comments (// ...)
fn single_line_comment(input: Span) -> IResult<Span, ()> {
    value(
        (), // We don't need to capture the comment content
        delimited(tag("//"), take_till(|c| c == '\n'), alt((tag("\n"), eof))),
    )(input)
}

// Parser for multi-line comments (/* ... */)
fn multi_line_comment(input: Span) -> IResult<Span, ()> {
    value((), delimited(tag("/*"), take_until("*/"), tag("*/")))(input)
}

// Parser for whitespace and comments
fn whitespace_or_comment(input: Span) -> IResult<Span, ()> {
    alt((
        value((), multispace1), // Matches whitespace (including newlines)
        single_line_comment,
        multi_line_comment,
    ))(input)
}

// Parser that consumes any amount of whitespace and comments
pub fn ignored(input: Span) -> IResult<Span, ()> {
    value((), many0(whitespace_or_comment))
        .context("Ignored")
        .parse(input)
}
