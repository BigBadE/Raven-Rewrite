use crate::code::parse_code;
use crate::expressions::expression;
use crate::util::ignored;
use crate::{IResult, Span};
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::combinator::{map, opt};
use nom::multi::many0;
use nom::sequence::{delimited, preceded, tuple};
use nom_supreme::ParserExt;
use hir::function::HighTerminator;
use hir::RawSyntaxLevel;
use hir::statement::{Conditional, HighStatement};

pub fn statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    delimited(
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
    )
    .terminated(delimited(ignored, tag(";"), ignored))
    .parse(input)
}

pub fn flow_changer(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    alt((
        preceded(tag("return"), delimited(ignored, expression, ignored))
            .map(|expression| HighStatement::Terminator(HighTerminator::Return(Some(expression)))),
        tag("return").map(|_| HighStatement::Terminator(HighTerminator::Return(None))),
        tag("break").map(|_| HighStatement::Terminator(HighTerminator::Break)),
        tag("continue").map(|_| HighStatement::Terminator(HighTerminator::Continue)),
    ))
    .parse(input)
}

pub fn if_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    tag("if")
        .precedes(
            tuple((
                parse_conditional,
                many0(parse_else_if),
                opt(parse_else),
            ))
            .map(|(first_cond, extra_conds, else_branch)| {
                let mut conditions = vec![first_cond];
                conditions.extend(extra_conds);
                HighStatement::If {
                    conditions,
                    else_branch,
                }
            }),
        )
        .parse(input)
}

pub fn for_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    preceded(
        tag("for"),
        parse_conditional.map(|condition| HighStatement::For { condition }),
    )
    .parse(input)
}

pub fn while_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    preceded(
        tag("while"),
        parse_conditional.map(|condition| HighStatement::While { condition }),
    )
    .parse(input)
}

pub fn loop_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    tag("loop")
        .precedes(parse_code.map(|body| HighStatement::Loop { body }))
        .parse(input)
}

/// Parses a conditional block: a condition and its branch.
fn parse_conditional(input: Span) -> IResult<Span, Conditional<RawSyntaxLevel>> {
    tuple((delimited(ignored, expression, ignored), parse_code))
        .map(|(condition, branch)| Conditional { condition, branch })
        .parse(input)
}

/// Parses an "else if" clause.
fn parse_else_if(input: Span) -> IResult<Span, Conditional<RawSyntaxLevel>> {
    tag("else")
        .precedes(delimited(ignored, tag("if"), ignored))
        .precedes(parse_conditional)
        .parse(input)
}

/// Parses an "else" clause.
fn parse_else(input: Span) -> IResult<Span, Vec<HighStatement<RawSyntaxLevel>>> {
    tag("else").precedes(parse_code).parse(input)
}
