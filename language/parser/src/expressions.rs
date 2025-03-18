use crate::statements::statement;
use crate::util::ignored;
use crate::{IResult, Span};
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{alphanumeric1, digit1};
use nom::combinator::{map, opt};
use nom::multi::{many0, separated_list0};
use nom::sequence::{delimited, preceded, terminated, tuple};
use syntax::code::literal::Literal;
use syntax::hir::{RawFunctionRef, RawSyntaxLevel, RawTypeRef};
use syntax::hir::expression::HighExpression;

pub fn expression(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    delimited(
        ignored,
        alt((
            literal,
            block,
            assignment,
            function,
            create_struct,
            variable,
        )),
        ignored,
    )(input)
}

/// Parses a variable name into an Expression::Variable.
pub fn variable(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(alphanumeric1, |ident: Span| {
        HighExpression::Variable(input.extra.intern(ident.to_string()))
    })(input.clone())
}

/// Parses a digit literal into an Expression::Literal.
pub fn literal(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(digit1, |digits: Span| {
        // Note: unwrap is used for simplicity.
        HighExpression::Literal(Literal::I64(digits.parse().unwrap()))
    })(input)
}

/// Parses a block of statements enclosed in braces into a CodeBlock.
pub fn block(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    delimited(
        tag("{"),
        map(many0(statement), |stmts| HighExpression::CodeBlock {
            body: stmts,
            value: Box::new(HighExpression::Literal(Literal::Void))
        }),
        tag("}"),
    )(input)
}

/// Parses an assignment expression, optionally with a "let" declaration keyword.
/// Grammar: ["let"] identifier "=" expression
pub fn assignment(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    let (input, declaration) = opt(tag("let"))(input)?;
    let (input, _) = ignored(input)?;
    let (input, var) = alphanumeric1(input)?;
    let (input, _) = ignored(input)?;
    let (input, _) = tag("=")(input)?;
    let (input, _) = ignored(input)?;
    let (input, expr) = expression(input)?;
    let expression = HighExpression::Assignment {
        declaration: declaration.is_some(),
        variable: input.extra.intern(var.to_string()),
        value: Box::new(expr),
    };
    Ok((input, expression))
}

/// Parses a function call expression with a target identifier,
/// a dot, a function name, and a parenthesized, comma-separated list of expressions.
/// Grammar: identifier \".\" identifier \"(\" [expression {\",\" expression}] \")\"
pub fn function(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    let (input, target_id) = opt(terminated(alphanumeric1, tag(".")))(input)?;
    let (input, func_name) = alphanumeric1(input)?;
    let (input, args) = delimited(
        tag("("),
        separated_list0(tag(","), preceded(ignored, expression)),
        tag(")"),
    )(input)?;
    let expression = HighExpression::FunctionCall {
        function: RawFunctionRef(input.extra.intern(func_name.to_string())),
        target: target_id.map(|span| {
            Box::new(HighExpression::Variable(
                input.extra.intern(span.to_string()),
            ))
        }),
        arguments: args,
    };
    Ok((input, expression))
}

/// Parses a struct creation expression.
/// Grammar: identifier \"{\" [identifier \":\" expression {\",\" identifier \":\" expression}] \"}\"
pub fn create_struct(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    let (input, struct_name) = alphanumeric1(input)?;
    let (input, fields) = delimited(
        tag("{"),
        separated_list0(
            tag(","),
            map(
                tuple((
                    preceded(ignored, alphanumeric1),
                    preceded(preceded(ignored, tag(":")), preceded(ignored, expression)),
                )),
                |(field, expr)| (input.extra.intern(field.to_string()), expr),
            ),
        ),
        tag("}"),
    )(input.clone())?;
    let expression = HighExpression::CreateStruct {
        target_struct: RawTypeRef(input.extra.intern(struct_name.to_string())),
        fields,
    };
    Ok((input, expression))
}
