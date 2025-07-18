use crate::expressions::expression;
use crate::statements::statement;
use crate::util::{ignored, tag_parser};
use crate::{IResult, Span};
use hir::RawSyntaxLevel;
use hir::expression::HighExpression;
use hir::function::{CodeBlock, HighTerminator};
use hir::statement::HighStatement;
use nom::Parser;
use nom::combinator::opt;
use nom::multi::many0;
use nom::sequence::{delimited, terminated, tuple};

/// Parser for function bodies
pub fn function_body(input: Span) -> IResult<Span, CodeBlock<RawSyntaxLevel>> {
    code_block
        .map(|(statements, returning)| CodeBlock {
            statements,
            terminator: returning
                .map(|value| HighTerminator::Return(Some(value)))
                .unwrap_or(HighTerminator::None),
        })
        .parse(input)
}

/// Parser for code blocks
pub fn code_block(
    input: Span,
) -> IResult<
    Span,
    (
        Vec<HighStatement<RawSyntaxLevel>>,
        Option<HighExpression<RawSyntaxLevel>>,
    ),
> {
    delimited(
        delimited(ignored, tag_parser("{"), ignored),
        tuple((many0(statement), opt(expression))),
        delimited(ignored, tag_parser("}"), ignored),
    )
    .parse(input)
}

/// Parser for code blocks (with no return)
pub fn code_block_returnless(input: Span) -> IResult<Span, Vec<HighStatement<RawSyntaxLevel>>> {
    delimited(
        delimited(ignored, tag_parser("{"), ignored),
        many0(statement),
        delimited(ignored, tag_parser("}"), ignored),
    )
    .parse(input)
}
