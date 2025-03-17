use crate::expressions::expression;
use crate::util::ignored;
use crate::{IResult, Span};
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::combinator::{map, opt};
use nom::multi::many0;
use nom::sequence::delimited;
use nom::Parser;
use syntax::hir::function::HighTerminator;
use syntax::hir::RawSyntaxLevel;
use syntax::hir::statement::{Conditional, HighStatement};

pub fn statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    let (input, statement) = delimited(
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
    )(input)?;

    let (input, _) = opt(delimited(ignored, tag(";"), ignored))(input)?;
    Ok((input, statement))
}

pub fn flow_changer(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    alt((
        tag("return").map(|_| HighStatement::Terminator(HighTerminator::Return(None))),
        tag("break").map(|_| HighStatement::Terminator(HighTerminator::Break)),
        tag("continue").map(|_| HighStatement::Terminator(HighTerminator::Continue)),
    ))
    .parse(input)
}

pub fn if_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    // Parse the initial "if" clause
    let (input, _) = tag("if")(input)?;
    let (input, first_cond) = parse_conditional(input)?;

    // Parse zero or more "else if" clauses
    let (input, mut extra_conds) = many0(parse_else_if)(input)?;

    // Combine all conditionals
    let mut conditions = vec![first_cond];
    conditions.append(&mut extra_conds);

    // Optionally parse an "else" clause
    let (input, else_branch) = opt(parse_else)(input)?;

    Ok((
        input,
        HighStatement::If {
            conditions,
            else_branch: else_branch.map(Box::new),
        },
    ))
}

pub fn for_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    let (input, _) = tag("for")(input)?;
    let (input, iterator) = parse_conditional(input)?;

    Ok((
        input,
        HighStatement::For {
            iterator: iterator.condition,
            body: iterator.branch,
        },
    ))
}

pub fn while_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    let (input, _) = tag("while")(input)?;
    let (input, condition) = parse_conditional(input)?;

    Ok((input, HighStatement::While { condition }))
}

pub fn loop_statement(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    let (input, _) = tag("loop")(input)?;
    let (input, condition) = statement(input)?;

    Ok((
        input,
        HighStatement::Loop {
            body: Box::new(condition),
        },
    ))
}

/// Parses a conditional block: a condition and its branch.
fn parse_conditional(input: Span) -> IResult<Span, Conditional<RawSyntaxLevel>> {
    let (input, _) = ignored(input)?;
    // Parse the condition expression
    let (input, condition) = expression(input)?;
    let (input, _) = ignored(input)?;
    // Parse the branch statement
    let (input, branch) = statement(input)?;
    Ok((
        input,
        Conditional {
            condition,
            branch: Box::new(branch),
        },
    ))
}

/// Parses an "else if" clause.
fn parse_else_if(input: Span) -> IResult<Span, Conditional<RawSyntaxLevel>> {
    // Parse "else if" then similar to parse_conditional.
    let (input, _) = tag("else")(input)?;
    let (input, _) = ignored(input)?;
    let (input, _) = tag("if")(input)?;
    parse_conditional(input)
}

/// Parses an "else" clause.
fn parse_else(input: Span) -> IResult<Span, HighStatement<RawSyntaxLevel>> {
    let (input, _) = tag("else")(input)?;
    let (input, _) = ignored(input)?;
    statement(input)
}
