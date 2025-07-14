use std::fmt;
use std::fmt::{Error, Formatter};
use std::fmt::Write;
use lasso::ThreadedRodeo;
use crate::{IResult, Span};
use nom::error::{ErrorKind, ParseError};
use syntax::util::pretty_print::{NestedWriter, PrettyPrint};

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
        other.context.push(format!("{:?}", kind));
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
        writeln!(writer, "error: {}", self.kind)?;
        writeln!(writer, "  --> ")?;
        self.span.extra.file.format(interner, writer)?;
        writeln!(writer, ":{}:{}", line_num, col_num)?;

        writeln!(writer, "   |")?;
        writeln!(writer, "{:2} | {}", line_num, source_line)?;
        writeln!(writer, "   | {}{}",
                 " ".repeat(col_num - 1),
                 "^".repeat(self.span.fragment().len().max(1)))?;

        // Add context if available
        if !self.context.is_empty() {
            writeln!(writer, "   |")?;
            for ctx in &self.context {
                writeln!(writer, "   = note: {}", ctx)?;
            }
        }

        // Add suggestions
        for suggestion in &self.suggestions {
            writeln!(writer, "   = help: {}", suggestion)?;
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