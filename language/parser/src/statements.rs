use crate::code::code_block_returnless;
use crate::errors::expect;
use crate::expressions::expression;
use crate::util::{ignored, tag_parser, deepest_alt};
use crate::{IResult, Span};
use hir::RawSyntaxLevel;
use hir::function::HighTerminator;
use hir::statement::{Conditional, HighStatement};
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::combinator::{map, opt};
use nom::multi::many0;
use nom::sequence::{delimited, preceded, terminated, tuple};

/// Parses a statement, which ends with a semicolon
pub fn statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    terminated(delimited(
        ignored,
        alt((
            flow_changer,
            if_statement,
            for_statement,
            while_statement,
            loop_statement,
            map(expression, HighStatement::Expression),
        )),
        ignored,
    ), delimited(ignored, expect(tag_parser(";"), "semicolon ';'", Some("statements must end with ';'")), ignored))
        .parse(input)
}

/// Parses a flow-changing statement like a return or break statement
pub fn flow_changer(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    alt((
        preceded(tag_parser("return"), delimited(ignored, expression, ignored))
            .map(|expression| HighStatement::Terminator(HighTerminator::Return(Some(expression)))),
        map(tag_parser("return"), |_| HighStatement::Terminator(HighTerminator::Return(None))),
        map(tag_parser("break"), |_| HighStatement::Terminator(HighTerminator::Break)),
        map(tag_parser("continue"), |_| HighStatement::Terminator(HighTerminator::Continue)),
    ))
        .parse(input)
}

/// Parses an if statement
pub fn if_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    preceded(tag("if"),
             tuple((parse_conditional, many0(parse_else_if), opt(parse_else))).map(
                 |(first_cond, extra_conds, else_branch)| {
                     let mut conditions = vec![first_cond];
                     conditions.extend(extra_conds);
                     HighStatement::If {
                         conditions,
                         else_branch,
                     }
                 },
             ),
    )
        .parse(input)
}

/// Parses a for statement
pub fn for_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    preceded(
        tag("for"),
        parse_conditional.map(|condition| HighStatement::For { condition }),
    )
        .parse(input)
}

/// Parses a while statement
pub fn while_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    preceded(
        tag("while"),
        parse_conditional.map(|condition| HighStatement::While { condition }),
    )
        .parse(input)
}

/// Parses a loop statement
pub fn loop_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    preceded(tag("loop"), code_block_returnless.map(|body| HighStatement::Loop { body }))
        .parse(input)
}

/// Parses a conditional block: a condition and its branch.
fn parse_conditional(input: Span) -> IResult<Span, Conditional<RawSyntaxLevel>> {
    tuple((
        delimited(ignored, expression, ignored),
        code_block_returnless,
    ))
        .map(|(condition, branch)| Conditional { condition, branch })
        .parse(input)
}

/// Parses an "else if" clause.
fn parse_else_if(input: Span) -> IResult<Span, Conditional<RawSyntaxLevel>> {
    preceded(preceded(tag("else"), delimited(ignored, tag("if"), ignored)), parse_conditional)
        .parse(input)
}

/// Parses an "else" clause.
fn parse_else(input: Span) -> IResult<Span, Vec<HighStatement<RawSyntaxLevel>>> {
    preceded(tag("else"), code_block_returnless).parse(input)
}
