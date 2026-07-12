//! Hand-written lexer for the surface language.
//!
//! Produces a flat `Vec<SpannedTok>` (token + line number) which the parser then
//! consumes. Whitespace is insignificant and `//` introduces a line comment.

/// A lexical token.
// Note: not `Eq` because `Float(f64)` is only `PartialEq`. Token comparisons use `==`/`matches!`.
#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    // Literals / identifiers.
    /// Carries a full 128-bit magnitude as an `i128` *bit pattern*: literals up
    /// to `i128::MAX` parse as their natural value, and literals in
    /// `(i128::MAX, u128::MAX]` (only reachable as an unsigned-typed literal)
    /// are stored via `u128 as i128` bit-reinterpretation — i.e. they land as
    /// the corresponding negative `i128`. Downstream (infer/codegen) reinterprets
    /// the bits as unsigned when the literal's inferred type is unsigned.
    Int(i128),
    Float(f64),
    Str(String),
    Ident(String),

    // Keywords.
    Fn,
    Let,
    If,
    Else,
    While,
    Return,
    Assert,
    Requires,
    Ensures,
    True,
    False,
    Struct,
    Enum,
    Match,
    Invariant,
    Trait,
    Impl,
    For,
    Panic,

    // Punctuation / delimiters.
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    ColonColon, // ::
    Semi,
    Dot,        // .
    FatArrow,   // =>
    Arrow,      // ->
    Eq,    // = (assignment)

    // Operators.
    OrOr,   // ||
    AndAnd, // &&
    EqEq,   // ==
    NotEq,  // !=
    Lt,     // <
    Le,     // <=
    Gt,     // >
    Ge,     // >=
    Plus,   // +
    Minus,  // -
    Star,   // *
    Slash,  // /
    Percent,// %
    Bang,   // !
    Amp,    // & (shared borrow / reference type)
    Question, // ? (error-propagation postfix operator)
    Pipe,   // | (single bar — closure delimiter)

    /// End of input (always the final token).
    Eof,
}

/// A token tagged with the (1-based) source line it began on, for diagnostics.
#[derive(Clone, Debug, PartialEq)]
pub struct SpannedTok {
    pub tok: Tok,
    pub line: u32,
}

/// Tokenize `src` into a vector of spanned tokens ending in `Tok::Eof`.
///
/// Returns `Err` with a line-tagged message on an unexpected character.
pub fn lex(src: &str) -> Result<Vec<SpannedTok>, String> {
    let bytes = src.as_bytes();
    let mut i = 0usize;
    let mut line = 1u32;
    let mut out = Vec::new();

    // Helper to push a token at the current line.
    macro_rules! push {
        ($t:expr) => {
            out.push(SpannedTok { tok: $t, line })
        };
    }

    while i < bytes.len() {
        let c = bytes[i] as char;

        // Whitespace (track newlines for diagnostics).
        if c == '\n' {
            line += 1;
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            continue;
        }

        // Line comments: `// ... <newline>`.
        if c == '/' && i + 1 < bytes.len() && bytes[i + 1] as char == '/' {
            while i < bytes.len() && bytes[i] as char != '\n' {
                i += 1;
            }
            continue;
        }

        // Multi-character operators / punctuation. Check two-char forms first.
        let two = if i + 1 < bytes.len() {
            Some((c, bytes[i + 1] as char))
        } else {
            None
        };
        match two {
            Some(('-', '>')) => {
                push!(Tok::Arrow);
                i += 2;
                continue;
            }
            Some(('|', '|')) => {
                push!(Tok::OrOr);
                i += 2;
                continue;
            }
            Some(('&', '&')) => {
                push!(Tok::AndAnd);
                i += 2;
                continue;
            }
            Some(('=', '=')) => {
                push!(Tok::EqEq);
                i += 2;
                continue;
            }
            Some(('=', '>')) => {
                push!(Tok::FatArrow);
                i += 2;
                continue;
            }
            Some((':', ':')) => {
                push!(Tok::ColonColon);
                i += 2;
                continue;
            }
            Some(('!', '=')) => {
                push!(Tok::NotEq);
                i += 2;
                continue;
            }
            Some(('<', '=')) => {
                push!(Tok::Le);
                i += 2;
                continue;
            }
            Some(('>', '=')) => {
                push!(Tok::Ge);
                i += 2;
                continue;
            }
            _ => {}
        }

        // Single-character tokens.
        let single = match c {
            '(' => Some(Tok::LParen),
            ')' => Some(Tok::RParen),
            '{' => Some(Tok::LBrace),
            '}' => Some(Tok::RBrace),
            ',' => Some(Tok::Comma),
            ':' => Some(Tok::Colon),
            ';' => Some(Tok::Semi),
            '.' => Some(Tok::Dot),
            '=' => Some(Tok::Eq),
            '<' => Some(Tok::Lt),
            '>' => Some(Tok::Gt),
            '+' => Some(Tok::Plus),
            '-' => Some(Tok::Minus),
            '*' => Some(Tok::Star),
            '/' => Some(Tok::Slash),
            '%' => Some(Tok::Percent),
            '!' => Some(Tok::Bang),
            '&' => Some(Tok::Amp),
            '?' => Some(Tok::Question),
            '|' => Some(Tok::Pipe),
            _ => None,
        };
        if let Some(t) = single {
            push!(t);
            i += 1;
            continue;
        }

        // String literals: `"..."` with `\n`, `\t`, `\"`, `\\` escapes.
        if c == '"' {
            i += 1; // opening quote
            let mut s = String::new();
            loop {
                if i >= bytes.len() {
                    return Err(format!("line {line}: unterminated string literal"));
                }
                let d = bytes[i] as char;
                if d == '"' {
                    i += 1; // closing quote
                    break;
                }
                if d == '\\' && i + 1 < bytes.len() {
                    let e = bytes[i + 1] as char;
                    s.push(match e {
                        'n' => '\n',
                        't' => '\t',
                        '"' => '"',
                        '\\' => '\\',
                        other => other,
                    });
                    i += 2;
                    continue;
                }
                if d == '\n' {
                    line += 1;
                }
                s.push(d);
                i += 1;
            }
            push!(Tok::Str(s));
            continue;
        }

        // Numeric literals: integer, or float when a `.` is followed by a digit (so `1.5` is a
        // float but `t.0` / `1..5` keep the `.` as its own token).
        if c.is_ascii_digit() {
            let start = i;
            while i < bytes.len() && (bytes[i] as char).is_ascii_digit() {
                i += 1;
            }
            let is_float = i + 1 < bytes.len()
                && bytes[i] as char == '.'
                && (bytes[i + 1] as char).is_ascii_digit();
            if is_float {
                i += 1; // consume '.'
                while i < bytes.len() && (bytes[i] as char).is_ascii_digit() {
                    i += 1;
                }
                let text = &src[start..i];
                let value: f64 = text
                    .parse()
                    .map_err(|_| format!("line {line}: float literal `{text}` out of range"))?;
                push!(Tok::Float(value));
                continue;
            }
            let text = &src[start..i];
            // Parse as `u128` first to admit the full unsigned 128-bit magnitude
            // (`0..=u128::MAX`), then reinterpret the bit pattern as `i128`. This
            // keeps literals in `i128`'s natural range numerically unchanged while
            // still allowing `u128` literals above `i128::MAX` to round-trip (as a
            // negative `i128` bit pattern; see `Tok::Int`'s doc comment).
            let value: u128 = text
                .parse()
                .map_err(|_| format!("line {line}: integer literal `{text}` out of range"))?;
            push!(Tok::Int(value as i128));
            continue;
        }

        // Identifiers / keywords: [A-Za-z_][A-Za-z0-9_]*
        if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            while i < bytes.len() {
                let d = bytes[i] as char;
                if d.is_ascii_alphanumeric() || d == '_' {
                    i += 1;
                } else {
                    break;
                }
            }
            let word = &src[start..i];
            let tok = keyword(word).unwrap_or_else(|| Tok::Ident(word.to_string()));
            push!(tok);
            continue;
        }

        return Err(format!("line {line}: unexpected character `{c}`"));
    }

    out.push(SpannedTok { tok: Tok::Eof, line });
    Ok(out)
}

/// Map a word to its keyword token, or `None` if it is an ordinary identifier.
/// Note: `result` is intentionally NOT reserved — it is an ordinary identifier
/// that only carries special meaning inside `ensures` (handled at lowering).
fn keyword(word: &str) -> Option<Tok> {
    Some(match word {
        "fn" => Tok::Fn,
        "let" => Tok::Let,
        "if" => Tok::If,
        "else" => Tok::Else,
        "while" => Tok::While,
        "return" => Tok::Return,
        "assert" => Tok::Assert,
        "requires" => Tok::Requires,
        "ensures" => Tok::Ensures,
        "true" => Tok::True,
        "false" => Tok::False,
        "struct" => Tok::Struct,
        "enum" => Tok::Enum,
        "match" => Tok::Match,
        "invariant" => Tok::Invariant,
        "trait" => Tok::Trait,
        "impl" => Tok::Impl,
        "for" => Tok::For,
        "panic" => Tok::Panic,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexes_operators_and_comments() {
        let toks = lex("// hi\nfn f() -> i64 { return 1 + 2; }").unwrap();
        let kinds: Vec<&Tok> = toks.iter().map(|s| &s.tok).collect();
        assert_eq!(kinds[0], &Tok::Fn);
        assert!(kinds.contains(&&Tok::Arrow));
        assert!(kinds.contains(&&Tok::Plus));
        assert_eq!(kinds.last().unwrap(), &&Tok::Eof);
    }

    #[test]
    fn tracks_lines() {
        let toks = lex("\n\nfn").unwrap();
        assert_eq!(toks[0].line, 3);
    }

    #[test]
    fn rejects_bad_char() {
        assert!(lex("fn f() { @ }").is_err());
    }
}
