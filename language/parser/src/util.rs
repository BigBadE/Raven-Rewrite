use crate::{IResult, Span};
use nom::branch::alt;
use nom::bytes::complete::{tag, take_till, take_until};
use nom::character::complete::multispace1;
use nom::combinator::{eof, value};
use nom::multi::many0;
use nom::sequence::delimited;

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
    value((), many0(whitespace_or_comment))(input)
}
