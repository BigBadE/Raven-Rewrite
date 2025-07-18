use std::fmt;
use std::fmt::{Error, Formatter};
use std::fmt::Write;
use lasso::ThreadedRodeo;
use crate::{IResult, Span};
use nom::error::{ErrorKind, ParseError};
use owo_colors::OwoColorize;
use syntax::util::CompileError;
use syntax::util::pretty_print::{NestedWriter, PrettyPrint};

pub fn print_err(err: &nom::Err<ParserError>) -> Result<String, CompileError> {
    match err {
        nom::Err::Failure(err) | nom::Err::Error(err) => {
            let interner = &err.span.extra.interner;
            Ok(err.format_top(interner, String::new())?)
        },
        nom::Err::Incomplete(_) => unreachable!(),
    }
}
#[derive(Debug)]
pub struct ParserError<'a> {
    pub span: Span<'a>,
    pub kind: ParserErrorKind,
    pub context: Vec<String>,
    pub suggestions: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum ParserErrorKind {
    ExpectedToken(String),
    UnexpectedToken(String),
    InvalidSyntax(String),
    Custom(String),
}

impl<'a> ParseError<Span<'a>> for ParserError<'a> {
    fn from_error_kind(input: Span<'a>, kind: ErrorKind) -> Self {
        ParserError {
            span: input,
            kind: ParserErrorKind::Custom(format!("{:?}", kind)),
            context: Vec::new(),
            suggestions: Vec::new(),
        }
    }

    fn append(_input: Span, kind: ErrorKind, mut other: Self) -> Self {
        // Filter out unfriendly nom parser error kinds from being shown to users
        match kind {
            // Skip these technical parser details that aren't helpful to end users
            ErrorKind::Tag | ErrorKind::TakeWhile1 | ErrorKind::TakeUntil | 
            ErrorKind::Many0 | ErrorKind::Many1 | ErrorKind::Alt | 
            ErrorKind::Complete | ErrorKind::Verify => {
                // Don't add these to context
            }
            // Only add meaningful error kinds that help users understand the issue
            _ => {
                let friendly_msg = match kind {
                    ErrorKind::Digit => "expected a number".to_string(),
                    ErrorKind::Alpha => "expected a letter".to_string(),
                    ErrorKind::AlphaNumeric => "expected a letter or number".to_string(),
                    ErrorKind::Space => "expected whitespace".to_string(),
                    ErrorKind::Eof => "unexpected end of file".to_string(),
                    _ => return other, // Skip other unfriendly error kinds
                };
                other.context.push(friendly_msg);
            }
        }
        other
    }
}

impl ParserError<'_> {
    fn get_source_line(&self) -> &str {
        let offset = self.span.location_offset();
        let full_input = unsafe {
            // Get the full input by going back to the start
            std::str::from_utf8_unchecked(
                std::slice::from_raw_parts(
                    self.span.fragment().as_ptr().sub(offset),
                    self.span.extra.parsing.len()
                )
            )
        };

        full_input.lines()
            .nth(self.span.location_line() as usize - 1)
            .unwrap_or("")
    }

    pub fn with_suggestion(mut self, suggestion: String) -> Self {
        self.suggestions.push(suggestion);
        self
    }

    pub fn with_context(mut self, context: String) -> Self {
        self.context.push(context);
        self
    }
}

impl<W: Write> PrettyPrint<W> for ParserError<'_> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        let line_num = self.span.location_line();
        let col_num = self.span.get_utf8_column();
        let source_line = self.get_source_line();

        // Main error message (like Rust's format)
        writeln!(writer, "{}: {}", "error".red().bold(), self.kind.to_string().red())?;
        write!(writer, "  {} ", "-->".blue().bold())?;
        self.span.extra.file.format(interner, writer)?;
        writeln!(writer, ":{}:{}", line_num.to_string().blue(), col_num.to_string().blue())?;

        writeln!(writer, "   {}", "|".blue().bold())?;
        writeln!(writer, "{:2} {} {}", line_num.to_string().blue(), "|".blue().bold(), source_line)?;
        writeln!(writer, "   {}", "|".blue().bold())?;

        // Add context if available
        if !self.context.is_empty() {
            writeln!(writer, "   {}", "|".blue().bold())?;
            for ctx in &self.context {
                writeln!(writer, "   {} {}: {}", "=".blue().bold(), "note".blue().bold(), ctx.yellow())?;
            }
        }

        // Add suggestions
        for suggestion in &self.suggestions {
            writeln!(writer, "   {} {}: {}", "=".blue().bold(), "help".green().bold(), suggestion.green())?;
        }

        Ok(())
    }
}

impl fmt::Display for ParserErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ParserErrorKind::ExpectedToken(token) => write!(f, "expected {}", token),
            ParserErrorKind::UnexpectedToken(token) => write!(f, "unexpected token '{}'", token),
            ParserErrorKind::InvalidSyntax(msg) => write!(f, "invalid syntax: {}", msg),
            ParserErrorKind::Custom(msg) => write!(f, "{}", msg),
        }
    }
}

pub fn expect<'a, I, O, E, F>(
    mut parser: F,
    expected: &'static str,
    suggestion: Option<&'static str>,
) -> impl FnMut(I) -> IResult<'a, I, O>
where
    F: FnMut(I) -> IResult<'a, I, O, E>,
    I: Clone,
    ParserError<'a>: ParseError<I>,
{
    move |input: I| {
        match parser(input.clone()) {
            Ok(result) => Ok(result),
            Err(nom::Err::Error(_)) | Err(nom::Err::Failure(_)) => {
                let mut error = ParserError::from_error_kind(
                    input,
                    ErrorKind::Tag
                );
                error.kind = ParserErrorKind::ExpectedToken(expected.to_string());

                if let Some(sugg) = suggestion {
                    error = error.with_suggestion(sugg.to_string());
                }

                Err(nom::Err::Failure(error))
            }
            // Should never happen, since
            Err(_) => unreachable!(),
        }
    }
}

pub fn context<'a, I, O, F>(
    mut parser: F,
    expected: &'static str,
    suggestion: Option<&'static str>,
) -> impl FnMut(I) -> IResult<'a, I, O>
where
    F: FnMut(I) -> IResult<'a, I, O>,
    I: Clone,
    ParserError<'a>: ParseError<I>,
{
    move |input: I| {
        match parser(input.clone()) {
            Ok(result) => Ok(result),
            Err(nom::Err::Error(_)) => {
                let mut error = ParserError::from_error_kind(
                    input,
                    ErrorKind::Tag
                );
                error.kind = ParserErrorKind::ExpectedToken(expected.to_string());

                if let Some(sugg) = suggestion {
                    error = error.with_suggestion(sugg.to_string());
                }

                // Key difference: returns Error, not Failure
                Err(nom::Err::Error(error))
            }
            Err(nom::Err::Failure(err)) => Err(nom::Err::Failure(err)),
            Err(nom::Err::Incomplete(needed)) => Err(nom::Err::Incomplete(needed)),
        }
    }
}