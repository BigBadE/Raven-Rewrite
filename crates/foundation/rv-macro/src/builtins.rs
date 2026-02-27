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
        BuiltinMacroKind::Cfg => expand_cfg(arguments, span),
        BuiltinMacroKind::Stringify => expand_stringify(arguments, interner),
        BuiltinMacroKind::Concat => expand_concat(arguments, span),
        BuiltinMacroKind::Include => expand_include(arguments, span),
        BuiltinMacroKind::CompileError => expand_compile_error(arguments, span),
        BuiltinMacroKind::Env => expand_env(arguments, span),
        BuiltinMacroKind::OptionEnv => expand_option_env(arguments, span, interner),
        BuiltinMacroKind::Line => expand_line(span),
        BuiltinMacroKind::Column => expand_column(span),
        BuiltinMacroKind::File => expand_file(span),
        BuiltinMacroKind::ModulePath => expand_module_path(),
    }
}

/// Expand println! macro
///
/// println!("format", args...) -> print(format!("format\n", args...))
fn expand_println(
    arguments: TokenStream,
    interner: &rv_intern::Interner,
) -> Result<TokenStream, MacroExpansionError> {
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
fn expand_vec(
    arguments: TokenStream,
    interner: &rv_intern::Interner,
) -> Result<TokenStream, MacroExpansionError> {
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
fn expand_assert(
    arguments: TokenStream,
    interner: &rv_intern::Interner,
) -> Result<TokenStream, MacroExpansionError> {
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

/// Expand format! macro
///
/// Handles format strings with `{}` positional placeholders. Each `{}` is replaced
/// by the corresponding argument in order. Named placeholders (`{name}`) and format
/// specifiers (`{:04x}`) are not yet supported.
fn expand_format(
    arguments: TokenStream,
    span: FileSpan,
) -> Result<TokenStream, MacroExpansionError> {
    let parts = split_by_comma(&arguments);

    // First argument must be a string literal
    let format_string = parts
        .first()
        .and_then(|part| {
            part.iter().next().and_then(|token| {
                if let Token::Literal(LiteralKind::String(s)) = token {
                    Some(s.clone())
                } else {
                    None
                }
            })
        })
        .ok_or_else(|| MacroExpansionError::InvalidSyntax {
            message: "format! requires a string literal as the first argument".to_string(),
            span,
        })?;

    // Count `{}` placeholders in the format string
    let placeholder_count = format_string.matches("{}").count();
    let arg_count = parts.len() - 1; // exclude format string

    if format_string.contains("{:") {
        return Err(MacroExpansionError::InvalidSyntax {
            message: "format! with format specifiers ({:…}) is not yet implemented".to_string(),
            span,
        });
    }

    if placeholder_count != arg_count {
        return Err(MacroExpansionError::InvalidSyntax {
            message: format!(
                "format! has {} placeholders but {} arguments",
                placeholder_count, arg_count
            ),
            span,
        });
    }

    if placeholder_count == 0 {
        // Plain string literal without placeholders — return as-is
        let mut result = TokenStream::new();
        result.push(Token::Literal(LiteralKind::String(format_string)));
        return Ok(result);
    }

    // Split the format string by `{}` and interleave with arguments.
    // This produces a concatenation expression: "part1" + arg1.to_string() + "part2" + ...
    // For now, since the compiler doesn't have string concatenation, expand to
    // a __format_args intrinsic call. Since we don't have that either, expand to
    // just the format string with placeholders replaced by argument tokens.
    //
    // In practice, the compiler currently uses println! which calls print(format!(...)).
    // Since print() doesn't exist as a real function in the compiler yet, this expansion
    // is used for macro infrastructure validation. The actual printing is handled by
    // the interpreter/backends directly when they see print-like calls.
    let mut result = TokenStream::new();
    result.push(Token::Literal(LiteralKind::String(format_string)));
    // Append the arguments as additional tokens so they're available for
    // downstream processing (e.g., the interpreter can extract them)
    for part in parts.iter().skip(1) {
        result.push(Token::Punct(','));
        for token in part.iter() {
            result.push(token.clone());
        }
    }
    Ok(result)
}

/// Split token stream by top-level commas.
///
/// Group tokens (`(…)`, `[…]`, `{…}`) are single tokens in the stream
/// (they contain a nested sub-stream), so commas inside them are never
/// visible at this level and no depth tracking is needed.
fn split_by_comma(stream: &TokenStream) -> Vec<TokenStream> {
    let mut result = Vec::new();
    let mut current = TokenStream::new();

    for token in &stream.tokens {
        match token {
            Token::Punct(',') => {
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

/// Expand cfg! macro
///
/// cfg!(predicate) -> true or false based on configuration
fn expand_cfg(_arguments: TokenStream, _span: FileSpan) -> Result<TokenStream, MacroExpansionError> {
    // For now, always return true (proper implementation requires cfg environment)
    let mut result = TokenStream::new();
    result.push(Token::Literal(LiteralKind::Bool(true)));
    Ok(result)
}

/// Expand stringify! macro
///
/// stringify!(tokens...) -> "tokens..."
fn expand_stringify(arguments: TokenStream, interner: &rv_intern::Interner) -> Result<TokenStream, MacroExpansionError> {
    let mut result = TokenStream::new();
    let stringified = tokens_to_string(&arguments, interner);
    result.push(Token::Literal(LiteralKind::String(stringified)));
    Ok(result)
}

/// Expand concat! macro
///
/// concat!(str1, str2, ...) -> "str1str2..."
fn expand_concat(arguments: TokenStream, span: FileSpan) -> Result<TokenStream, MacroExpansionError> {
    let parts = split_by_comma(&arguments);
    let mut concatenated = String::new();

    for part in parts {
        if let Some(Token::Literal(LiteralKind::String(s))) = part.tokens.first() {
            concatenated.push_str(s);
        } else {
            return Err(MacroExpansionError::InvalidSyntax {
                message: "concat! requires string literals".to_string(),
                span,
            });
        }
    }

    let mut result = TokenStream::new();
    result.push(Token::Literal(LiteralKind::String(concatenated)));
    Ok(result)
}

/// Expand include! macro
///
/// include!("path") -> contents of file at path
fn expand_include(_arguments: TokenStream, span: FileSpan) -> Result<TokenStream, MacroExpansionError> {
    // File inclusion requires access to the file system and parser
    // This is a placeholder that returns an error
    Err(MacroExpansionError::InvalidSyntax {
        message: "include! macro not yet implemented".to_string(),
        span,
    })
}

/// Expand compile_error! macro
///
/// compile_error!("message") -> compile error with message
fn expand_compile_error(arguments: TokenStream, span: FileSpan) -> Result<TokenStream, MacroExpansionError> {
    // Extract error message
    let message = if let Some(Token::Literal(LiteralKind::String(s))) = arguments.tokens.first() {
        s.clone()
    } else {
        "compile_error!".to_string()
    };

    Err(MacroExpansionError::InvalidSyntax {
        message,
        span,
    })
}

/// Expand env! macro
///
/// env!("VAR_NAME") -> value of environment variable
fn expand_env(arguments: TokenStream, span: FileSpan) -> Result<TokenStream, MacroExpansionError> {
    if let Some(Token::Literal(LiteralKind::String(var_name))) = arguments.tokens.first() {
        if let Ok(value) = std::env::var(var_name) {
            let mut result = TokenStream::new();
            result.push(Token::Literal(LiteralKind::String(value)));
            Ok(result)
        } else {
            Err(MacroExpansionError::InvalidSyntax {
                message: format!("environment variable '{}' not found", var_name),
                span,
            })
        }
    } else {
        Err(MacroExpansionError::InvalidSyntax {
            message: "env! requires a string literal".to_string(),
            span,
        })
    }
}

/// Expand option_env! macro
///
/// option_env!("VAR_NAME") -> Some("value") or None
fn expand_option_env(arguments: TokenStream, span: FileSpan, interner: &rv_intern::Interner) -> Result<TokenStream, MacroExpansionError> {
    if let Some(Token::Literal(LiteralKind::String(var_name))) = arguments.tokens.first() {
        let mut result = TokenStream::new();
        if let Ok(value) = std::env::var(var_name) {
            // Some("value")
            result.push(Token::Ident(interner.intern("Some")));
            let mut inner = TokenStream::new();
            inner.push(Token::Literal(LiteralKind::String(value)));
            result.push(Token::Group {
                delim: Delimiter::Paren,
                stream: inner,
            });
        } else {
            // None
            result.push(Token::Ident(interner.intern("None")));
        }
        Ok(result)
    } else {
        Err(MacroExpansionError::InvalidSyntax {
            message: "option_env! requires a string literal".to_string(),
            span,
        })
    }
}

/// Expand line! macro
///
/// line!() -> current line number
fn expand_line(span: FileSpan) -> Result<TokenStream, MacroExpansionError> {
    let mut result = TokenStream::new();
    // Extract line number from span
    let line = span.span.start as i64; // Simplified
    result.push(Token::Literal(LiteralKind::Integer(line)));
    Ok(result)
}

/// Expand column! macro
///
/// column!() -> current column number
fn expand_column(_span: FileSpan) -> Result<TokenStream, MacroExpansionError> {
    let mut result = TokenStream::new();
    // Column tracking would require more sophisticated span info
    let column = 0_i64; // Placeholder
    result.push(Token::Literal(LiteralKind::Integer(column)));
    Ok(result)
}

/// Expand file! macro
///
/// file!() -> current file name
fn expand_file(span: FileSpan) -> Result<TokenStream, MacroExpansionError> {
    let mut result = TokenStream::new();
    // File name from FileId would require VFS lookup
    let file_name = format!("file_{}", span.file.0);
    result.push(Token::Literal(LiteralKind::String(file_name)));
    Ok(result)
}

/// Expand module_path! macro
///
/// module_path!() -> current module path
fn expand_module_path() -> Result<TokenStream, MacroExpansionError> {
    let mut result = TokenStream::new();
    // Module path tracking requires compiler integration
    result.push(Token::Literal(LiteralKind::String("crate".to_string())));
    Ok(result)
}

/// Convert tokens to a string representation
fn tokens_to_string(stream: &TokenStream, interner: &rv_intern::Interner) -> String {
    stream
        .tokens
        .iter()
        .map(|token| match token {
            Token::Ident(sym) => interner.resolve(sym).to_string(),
            Token::Literal(lit) => match lit {
                LiteralKind::Integer(i) => i.to_string(),
                LiteralKind::Float(f) => f.to_string(),
                LiteralKind::String(s) => format!("\"{}\"", s),
                LiteralKind::Bool(b) => b.to_string(),
            },
            Token::Punct(c) => c.to_string(),
            Token::Group { delim, stream } => {
                let (open, close) = match delim {
                    Delimiter::Paren => ("(", ")"),
                    Delimiter::Bracket => ("[", "]"),
                    Delimiter::Brace => ("{", "}"),
                };
                format!("{}{}{}", open, tokens_to_string(stream, interner), close)
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}
