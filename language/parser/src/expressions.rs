use std::mem;
use crate::errors::{expect, context};
use crate::statements::statement;
use crate::util::{file_path, identifier, ignored, symbolic, tag_parser, type_ref};
use crate::{IResult, Span};
use hir::expression::HighExpression;
use hir::{RawFunctionRef, RawSyntaxLevel};
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{alphanumeric1, digit1};
use nom::combinator::{map, opt};
use nom::multi::{many0, separated_list0};
use nom::sequence::{delimited, preceded, terminated, tuple};
use syntax::structure::literal::Literal;

/// Parses a term, an expression that can't be recursive
pub fn term(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    // First parse atoms (non-postfix expressions)
    let (input, base) = alt((
        standalone_function_call,
        create_struct,
        literal,
        variable,
        block,
    ))(input)?;

    // Then handle postfix operations (field access and method calls)
    parse_postfix(input, base)
}

/// Parse postfix operations like field access and method calls
fn parse_postfix(mut input: Span, mut expr: HighExpression<RawSyntaxLevel>) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    loop {
        let Ok((after_ident, ident)) = preceded(tag_parser("."), identifier)(input.clone()) else {
            break;
        };

        // Check if this is a method call (has parentheses) or field access
        let paren_result = tag_parser("(")(after_ident.clone());
        if let Ok((after_paren, _)) = paren_result {
            // This is a method call
            let (after_close, args) = terminated(separated_list0(
                delimited(ignored, tag_parser(","), ignored),
                delimited(ignored, expression, ignored),
            ), tag_parser(")")).parse(after_paren)?;

            expr = HighExpression::FunctionCall {
                function: RawFunctionRef {
                    path: vec![ident],
                    generics: vec![],
                },
                target: Some(Box::new(expr)),
                arguments: args,
            };
            input = after_close;
        } else {
            // This is field access
            expr = HighExpression::FieldAccess {
                object: Box::new(expr),
                field: ident,
            };
            input = after_ident;
        }
    }

    Ok((input, expr))
}

/// Parses an expression, which can be recursive
pub fn expression(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    delimited(ignored, alt((assignment, operation, term)), ignored)
        .parse(input)
}

/// Parses a variable name into an Expression::Variable
pub fn variable(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(alphanumeric1, |ident: Span| {
        HighExpression::Variable(ident.extra.intern(ident.fragment()))
    })(input)
}

/// Parses a digit literal into an Expression::Literal
/// TODO handle more literals
pub fn literal(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(digit1, |digits: Span| {
        let value = digits.fragment().parse::<i64>().unwrap_or(0);
        HighExpression::Literal(Literal::I64(value))
    })(input)
}

/// Parses a block of statements enclosed in braces into a CodeBlock
pub fn block(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    delimited(
        context(tag_parser("{"), "opening brace '{'", Some("blocks must start with '{'")),
        map(tuple((many0(statement), expression)), |(body, value)| {
            HighExpression::CodeBlock {
                body,
                value: Box::new(value),
            }
        }),
        expect(tag_parser("}"), "closing brace '}'", Some("blocks must end with '}'")),
    )(input)
}

/// Parses an assignment expression, optionally with a "let" declaration keyword.
/// Grammar: ["let"] identifier "=" expression
pub fn assignment(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(
        tuple((
            opt(terminated(tag_parser("let"), ignored)),
            identifier,
            preceded(delimited(ignored, tag_parser("="), ignored), expression),
        )),
        |(declaration, variable, value)| HighExpression::Assignment {
            declaration: declaration.is_some(),
            variable,
            value: Box::new(value),
        },
    )
        .parse(input)
}

/// Parses a standalone function call expression (not a method call)
/// Grammar: file_path [\"<\" type_list \">\"] \"(\" [expression_list] \")\"
pub fn standalone_function_call(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(
        tuple((
            file_path,
            opt(delimited(tag_parser("<"), separated_list0(
                tag(","),
                delimited(ignored, type_ref, ignored),
            ), tag_parser(">"))),
            delimited(
                tag_parser("("),
                separated_list0(delimited(ignored, tag_parser(","), ignored), delimited(ignored, expression, ignored)),
                tag_parser(")"),
            ),
        )),
        |(function, generics, args)| HighExpression::FunctionCall {
            function: RawFunctionRef {
                path: function,
                generics: generics.unwrap_or_default(),
            },
            target: None,
            arguments: args,
        },
    )(input)
}

/// Parses a struct creation expression.
/// Grammar: identifier \"{\" [identifier \":\" expression {\",\" identifier \":\" expression}] \"}\"
pub fn create_struct(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    // Use a complete parser that only succeeds if the entire pattern matches
    let (input, target_struct) = type_ref(input)?;
    let (input, _) = delimited(ignored, tag_parser("{"), ignored)(input)?;

    let (input, fields) = separated_list0(
        tag_parser(","),
        tuple((
            preceded(ignored, identifier),
            preceded(preceded(ignored, expect(tag_parser(":"), "colon ':'", Some("struct fields use ':' to separate name and value"))), preceded(ignored, expression)),
        )),
    )(input)?;

    let (input, _) = delimited(ignored, expect(tag_parser("}"), "closing brace '}'", Some("struct creation ends with '}'")), ignored)(input)?;

    Ok((input, HighExpression::CreateStruct {
        target_struct,
        fields,
    }))
}

/// Parses an operation from left to right, such as +, -, *, /, !, etc.
/// Uses term to prevent infinite recursion
pub fn operation(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(
        tuple((
            delimited(ignored, term, ignored),
            symbolic,
            delimited(ignored, term, ignored)
        )),
        |(first, symbol, second)| HighExpression::BinaryOperation {
            symbol,
            first: Box::new(first),
            second: Box::new(second),
        },
    )
        .parse(input)
}
