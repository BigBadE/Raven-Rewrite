//! Builtin macro implementations

use crate::ast::{BuiltinMacroKind, Delimiter, LiteralKind, Token, TokenStream};
use crate::error::MacroExpansionError;
use rv_span::FileSpan;

/// Expand a builtin macro
///
/// # Errors
///
/// Returns an error if the builtin macro expansion fails
pub fn expand_builtin(
    kind: BuiltinMacroKind,
    arguments: TokenStream,
    span: FileSpan,
    interner: &rv_intern::Interner,
) -> Result<TokenStream, MacroExpansionError> {
    match kind {
        BuiltinMacroKind::Println => expand_println(arguments, interner),
        BuiltinMacroKind::Vec => expand_vec(arguments, interner),
        BuiltinMacroKind::Assert => expand_assert(arguments, interner),
        BuiltinMacroKind::Format => expand_format(arguments, span),
    }
}

/// Expand println! macro
///
/// println!("format", args...) -> print(format!("format\n", args...))
fn expand_println(arguments: TokenStream, interner: &rv_intern::Interner) -> Result<TokenStream, MacroExpansionError> {
    let mut result = TokenStream::new();

    // print(
    result.push(Token::Ident(interner.intern("print")));

    // Add format call with newline
    let mut format_args = TokenStream::new();
    format_args.push(Token::Ident(interner.intern("format")));
    format_args.push(Token::Punct('!'));

    // Arguments in parentheses
    let mut paren_contents = TokenStream::new();

    // Find the format string and append \n
    if let Some(first_token) = arguments.tokens.first() {
        if let Token::Literal(LiteralKind::String(original_str)) = first_token {
            let mut new_str = original_str.clone();
            new_str.push_str("\\n");
            paren_contents.push(Token::Literal(LiteralKind::String(new_str)));
        } else {
            paren_contents.push(first_token.clone());
        }
    }

    // Add remaining arguments
    for token in arguments.tokens.iter().skip(1) {
        paren_contents.push(token.clone());
    }

    format_args.push(Token::Group {
        delim: Delimiter::Paren,
        stream: paren_contents,
    });

    // Wrap in parentheses for print call
    result.push(Token::Group {
        delim: Delimiter::Paren,
        stream: format_args,
    });

    Ok(result)
}

/// Expand vec! macro
///
/// vec![elem1, elem2, ...] -> { let mut temp_vec = Vec::new(); temp_vec.push(elem1); ... temp_vec }
fn expand_vec(arguments: TokenStream, interner: &rv_intern::Interner) -> Result<TokenStream, MacroExpansionError> {
    let mut result = TokenStream::new();

    // Split arguments by comma
    let elements = split_by_comma(&arguments);

    // { let mut temp_vec = Vec::new();
    result.push(Token::Punct('{'));
    result.push(Token::Ident(interner.intern("let")));
    result.push(Token::Ident(interner.intern("mut")));
    result.push(Token::Ident(interner.intern("temp_vec")));
    result.push(Token::Punct('='));
    result.push(Token::Ident(interner.intern("Vec")));
    result.push(Token::Punct(':'));
    result.push(Token::Punct(':'));
    result.push(Token::Ident(interner.intern("new")));
    result.push(Token::Group {
        delim: Delimiter::Paren,
        stream: TokenStream::new(),
    });
    result.push(Token::Punct(';'));

    // temp_vec.push(elem); for each element
    for element in &elements {
        result.push(Token::Ident(interner.intern("temp_vec")));
        result.push(Token::Punct('.'));
        result.push(Token::Ident(interner.intern("push")));
        result.push(Token::Group {
            delim: Delimiter::Paren,
            stream: element.clone(),
        });
        result.push(Token::Punct(';'));
    }

    // temp_vec }
    result.push(Token::Ident(interner.intern("temp_vec")));
    result.push(Token::Punct('}'));

    Ok(result)
}

/// Expand assert! macro
///
/// assert!(condition) -> if !condition { panic!("assertion failed: condition"); }
fn expand_assert(arguments: TokenStream, interner: &rv_intern::Interner) -> Result<TokenStream, MacroExpansionError> {
    let mut result = TokenStream::new();

    // if !(condition) {
    result.push(Token::Ident(interner.intern("if")));
    result.push(Token::Punct('!'));
    result.push(Token::Group {
        delim: Delimiter::Paren,
        stream: arguments.clone(),
    });

    // panic!("assertion failed")
    let mut panic_block = TokenStream::new();
    panic_block.push(Token::Ident(interner.intern("panic")));
    panic_block.push(Token::Punct('!'));

    let mut panic_args = TokenStream::new();
    panic_args.push(Token::Literal(LiteralKind::String(
        "assertion failed".to_string(),
    )));

    panic_block.push(Token::Group {
        delim: Delimiter::Paren,
        stream: panic_args,
    });
    panic_block.push(Token::Punct(';'));

    result.push(Token::Group {
        delim: Delimiter::Brace,
        stream: panic_block,
    });

    Ok(result)
}

/// Expand format! macro (simplified)
///
/// For now, just return the arguments as-is
fn expand_format(arguments: TokenStream, _span: FileSpan) -> Result<TokenStream, MacroExpansionError> {
    // Simplified: just return the arguments
    // A full implementation would parse format strings and generate formatting code
    Ok(arguments)
}

/// Split token stream by comma
fn split_by_comma(stream: &TokenStream) -> Vec<TokenStream> {
    let mut result = Vec::new();
    let mut current = TokenStream::new();
    let mut depth = 0;

    for token in &stream.tokens {
        match token {
            Token::Group { .. } => {
                depth += 1;
                current.push(token.clone());
            }
            Token::Punct(',') if depth == 0 => {
                if !current.is_empty() {
                    result.push(current.clone());
                    current = TokenStream::new();
                }
            }
            _ => {
                current.push(token.clone());
            }
        }
    }

    if !current.is_empty() {
        result.push(current);
    }

    result
}
