use crate::statements::statement;
use crate::util::ignored;
use crate::{IResult, Span};
use nom::bytes::complete::tag;
use nom::multi::many0;
use nom::sequence::{delimited, terminated};
use nom::Parser;
use hir::function::{CodeBlock, HighTerminator};
use hir::RawSyntaxLevel;
use hir::statement::HighStatement;

// Parser for function bodies
pub fn function_body(input: Span) -> IResult<Span, CodeBlock<RawSyntaxLevel>> {
    parse_code.map(|statements| CodeBlock {
        statements,
        terminator: HighTerminator::None,
    }).parse(input)
}

pub fn parse_code(input: Span) -> IResult<Span, Vec<HighStatement<RawSyntaxLevel>>> {
    delimited(delimited(ignored, tag("{"), ignored),
              many0(terminated(statement, ignored)),
              delimited(ignored, tag("}"), ignored))
        .parse(input)
}
