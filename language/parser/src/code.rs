use crate::statements::statement;
use crate::util::ignored;
use crate::{IResult, Span};
use nom::bytes::complete::tag;
use nom::multi::many0;
use nom::sequence::{delimited, terminated};
use nom::Parser;
use syntax::code::expression::HighExpression;
use syntax::code::statement::HighStatement;
use syntax::hir::RawSyntaxLevel;

// Parser for function bodies
pub fn function_body(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    delimited(
        delimited(ignored, tag("{"), ignored),
        parse_code, //very basic body parser
        delimited(ignored, tag("}"), ignored),
    )(input).map(|(remaining, body)| (remaining, body))
}

pub fn parse_code(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    many0(terminated(statement, ignored)).map(|statement| HighStatement::Expression(HighExpression::CodeBlock(statement))).parse(input)
}