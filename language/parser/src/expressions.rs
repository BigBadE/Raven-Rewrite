use crate::errors::expect;
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
    alt((
        literal,
        block,
        assignment,
        function_call,
        create_struct,
        variable,
    ))(input)
}

/// Parses an expression, which can be recursive
pub fn expression(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    delimited(ignored, alt((operation, term)), ignored)
        .parse(input)
}

/// Parses a variable name into an Expression::Variable
pub fn variable(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(alphanumeric1, |ident: Span| {
        HighExpression::Variable(input.extra.intern(ident.to_string()))
    })(input.clone())
}

/// Parses a digit literal into an Expression::Literal
/// TODO handle more literals
pub fn literal(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(digit1, |digits: Span| {
        HighExpression::Literal(Literal::I64(digits.parse().unwrap()))
    })(input)
}

/// Parses a block of statements enclosed in braces into a CodeBlock
pub fn block(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    delimited(
        expect(tag_parser("{"), "opening brace '{'", Some("blocks must start with '{'")),
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
            opt(tag("let")),
            delimited(ignored, identifier, ignored),
            preceded(expect(tag_parser("="), "assignment operator '='", Some("use '=' to assign values")), expression),
        )),
        |(declaration, variable, value)| HighExpression::Assignment {
            declaration: declaration.is_some(),
            variable,
            value: Box::new(value),
        },
    )
    .parse(input)
}

/// Parses a function call expression with a target identifier,
/// a dot, a function name, and a parenthesized, comma-separated list of expressions.
/// Grammar: identifier \".\" identifier \"(\" [expression {\",\" expression}] \")\"
pub fn function_call(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(
        tuple((
            opt(terminated(identifier, expect(tag_parser("."), "dot '.' for method calls", Some("use '.' to call methods on objects")))),
            file_path,
            opt(delimited(expect(tag_parser("<"), "opening angle bracket '<'", Some("generic arguments start with '<'")), separated_list0(
                tag(","),
                delimited(ignored, type_ref, ignored),
            ), expect(tag_parser(">"), "closing angle bracket '>'", Some("generic arguments end with '>'")))),
            delimited(
                expect(tag_parser("("), "opening parenthesis '('", Some("function arguments must be enclosed in parentheses")),
                separated_list0(tag(","), preceded(ignored, expression)),
                expect(tag_parser(")"), "closing parenthesis ')'", Some("function arguments must end with ')'")),
            ),
        )),
        |(target, function, generics, args)| HighExpression::FunctionCall {
            function: RawFunctionRef {
                path: function,
                generics: generics.unwrap_or_default(),
            },
            target: target.map(|span| Box::new(HighExpression::Variable(span))),
            arguments: args,
        },
    )(input)
}

/// Parses a struct creation expression.
/// Grammar: identifier \"{\" [identifier \":\" expression {\",\" identifier \":\" expression}] \"}\"
pub fn create_struct(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(
        tuple((
            type_ref,
            delimited(
                delimited(ignored, expect(tag_parser("{"), "opening brace '{'", Some("struct creation starts with '{'")), ignored),
                separated_list0(
                    tag(","),
                    tuple((
                        preceded(ignored, identifier),
                        preceded(preceded(ignored, expect(tag_parser(":"), "colon ':'", Some("struct fields use ':' to separate name and value"))), preceded(ignored, expression)),
                    )),
                ),
                delimited(ignored, expect(tag_parser("}"), "closing brace '}'", Some("struct creation ends with '}'")), ignored),
            ),
        )),
        |(target_struct, fields)| HighExpression::CreateStruct {
            target_struct,
            fields,
        },
    )(input)
}

/// Parses an operation from left to right, such as +, -, *, /, !, etc.
/// Works on unary and binary
/// Uses term to prevent infinite recursion
pub fn operation(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    alt((
        map(
            tuple((opt(term), symbolic, expression)),
            |(first, symbol, second)| match first {
                Some(first) => HighExpression::BinaryOperation {
                    symbol,
                    first: Box::new(first),
                    second: Box::new(second),
                },
                None => HighExpression::UnaryOperation {
                    pre: true,
                    symbol,
                    value: Box::new(second),
                },
            },
        ),
        map(tuple((term, symbolic)), |(value, symbol)| {
            HighExpression::UnaryOperation {
                pre: false,
                symbol,
                value: Box::new(value),
            }
        }),
    ))
    .parse(input)
}
