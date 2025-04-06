use crate::expressions::expression;
use crate::statements::statement;
use crate::util::ignored;
use crate::{IResult, Span};
use hir::RawSyntaxLevel;
use hir::expression::HighExpression;
use hir::function::{CodeBlock, HighTerminator};
use hir::statement::HighStatement;
use nom::Parser;
use nom::bytes::complete::tag;
use nom::combinator::opt;
use nom::multi::many0;
use nom::sequence::{delimited, terminated, tuple};
use nom_supreme::ParserExt;

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
        delimited(ignored, tag("{"), ignored),
        tuple((many0(terminated(statement, ignored)), opt(expression))),
        delimited(ignored, tag("}"), ignored),
    )
    .context("Code")
    .parse(input)
}

/// Parser for code blocks
pub fn code_block_returnless(
    input: Span,
) -> IResult<
    Span,
        Vec<HighStatement<RawSyntaxLevel>>,
> {
    delimited(
        delimited(ignored, tag("{"), ignored),
        many0(terminated(statement, ignored)),
        delimited(ignored, tag("}"), ignored),
    )
        .context("Code Returnless")
        .parse(input)
}
