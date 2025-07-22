use crate::errors::{expect, context};
use crate::statements::statement;
use crate::util::{file_path, identifier, ignored, symbolic, tag_parser, type_ref};
use crate::{IResult, Span};
use hir::expression::HighExpression;
use hir::{RawFunctionRef, RawSyntaxLevel};
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::{tag, take_until, take_while_m_n};
use nom::character::complete::{alphanumeric1, digit1, char as nom_char};
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

/// Parses all literal types: numbers, strings, booleans, characters
pub fn literal(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    alt((
        boolean_literal,
        string_literal,
        character_literal,
        float_literal,
        integer_literal,
    ))(input)
}

/// Parses boolean literals: true, false
fn boolean_literal(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    alt((
        map(tag("true"), |_| HighExpression::Literal(Literal::Bool(true))),
        map(tag("false"), |_| HighExpression::Literal(Literal::Bool(false))),
    ))(input)
}

/// Parses string literals: "hello world"
fn string_literal(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    let input_clone = input.clone();
    let (remaining, content) = delimited(nom_char('"'), take_until("\""), nom_char('"'))(input)?;
    let string_content = content.fragment().to_string();
    let interned = input_clone.extra.intern(string_content);
    Ok((remaining, HighExpression::Literal(Literal::String(interned))))
}

/// Parses character literals: 'a', '\n', '\t'
fn character_literal(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    map(
        delimited(
            nom_char('\''),
            alt((
                // Escape sequences
                preceded(nom_char('\\'), alt((
                    map(nom_char('n'), |_| '\n'),
                    map(nom_char('t'), |_| '\t'),
                    map(nom_char('r'), |_| '\r'),
                    map(nom_char('\\'), |_| '\\'),
                    map(nom_char('\''), |_| '\''),
                    map(nom_char('"'), |_| '"'),
                ))),
                // Regular character
                map(take_while_m_n(1, 1, |c| c != '\''), |s: Span| {
                    s.fragment().chars().next().unwrap_or('\0')
                }),
            )),
            nom_char('\'')
        ),
        |ch| HighExpression::Literal(Literal::Char(ch))
    )(input)
}

/// Parses floating point literals: 3.14, 2.0f32
fn float_literal(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    let (remaining, (whole, _, frac, suffix)) = tuple((
        digit1,
        nom_char('.'),
        digit1,
        opt(alt((tag("f32"), tag("f64")))),
    ))(input)?;
    
    let float_str = format!("{}.{}", whole.fragment(), frac.fragment());
    let literal = match suffix.as_ref().map(|s| s.fragment()) {
        Some(&"f32") => {
            let value = float_str.parse::<f32>().unwrap_or(0.0);
            HighExpression::Literal(Literal::F32(value))
        }
        _ => {
            let value = float_str.parse::<f64>().unwrap_or(0.0);
            HighExpression::Literal(Literal::F64(value))
        }
    };
    
    Ok((remaining, literal))
}

/// Parses integer literals: 42, 123i32, 456u64
fn integer_literal(input: Span) -> IResult<Span, HighExpression<RawSyntaxLevel>> {
    let (remaining, (digits, suffix)) = tuple((
        digit1,
        opt(alt((tag("i64"), tag("i32"), tag("u64"), tag("u32")))),
    ))(input)?;
    
    let int_str = digits.fragment();
    let literal = match suffix.as_ref().map(|s| s.fragment()) {
        Some(&"i32") => {
            let value = int_str.parse::<i32>().unwrap_or(0);
            HighExpression::Literal(Literal::I32(value))
        }
        Some(&"u64") => {
            let value = int_str.parse::<u64>().unwrap_or(0);
            HighExpression::Literal(Literal::U64(value))
        }
        Some(&"u32") => {
            let value = int_str.parse::<u32>().unwrap_or(0);
            HighExpression::Literal(Literal::U32(value))
        }
        _ => {
            // Default to i64
            let value = int_str.parse::<i64>().unwrap_or(0);
            HighExpression::Literal(Literal::I64(value))
        }
    };
    
    Ok((remaining, literal))
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
