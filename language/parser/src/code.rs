use crate::statements::statement;
use crate::util::ignored;
use crate::{IResult, Span};
use nom::bytes::complete::tag;
use nom::multi::many0;
use nom::sequence::{delimited, terminated};
use nom::Parser;
use syntax::hir::function::{CodeBlock, HighTerminator};
use syntax::hir::RawSyntaxLevel;

// Parser for function bodies
pub fn function_body(input: Span) -> IResult<Span, CodeBlock<RawSyntaxLevel>> {
    delimited(
        delimited(ignored, tag("{"), ignored),
        parse_code, //very basic body parser
        delimited(ignored, tag("}"), ignored),
    )(input)
    .map(|(remaining, body)| (remaining, body))
}

pub fn parse_code(input: Span) -> IResult<Span, CodeBlock<RawSyntaxLevel>> {
    many0(terminated(statement, ignored))
        .map(|statements| CodeBlock { statements, terminator: HighTerminator::None })
        .parse(input)
}
