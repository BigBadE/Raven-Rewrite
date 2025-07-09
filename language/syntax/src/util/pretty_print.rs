use crate::structure::literal::Literal;
use crate::{GenericTypeRef, Syntax, SyntaxLevel};
use lasso::{Spur, ThreadedRodeo};
use std::fmt;
use std::fmt::{Arguments, Display, Write};
use indexmap::IndexMap;
use crate::structure::traits::TypeReference;

/// Trait for pretty printing with string interpolation
pub trait PrettyPrint<W: Write> {
    /// Format this item as a human-readable string
    fn format(&self, interner: &ThreadedRodeo, writer: &mut W) -> Result<(), fmt::Error>;
}

/// Implementation for Syntax
impl<T: SyntaxLevel, W: Write> PrettyPrint<W> for Syntax<T>
where
    T::Type: PrettyPrint<W>,
    T::Function: PrettyPrint<W>,
{
    fn format(&self, interner: &ThreadedRodeo, writer: &mut W) -> Result<(), fmt::Error> {
        for (_, types) in self.types {
            types.format(interner, writer)?;
        }

        // Add separator between types and functions
        if !self.types.is_empty() && !self.functions.is_empty() {
            write!(writer, "\n")?;
        }

        // Format functions
        for (_, function) in self.functions {
            function.format(interner, writer)?;
        }

        Ok(())
    }
}

/// Implement Display for Syntax when its types implement PrettyPrint
impl<T: SyntaxLevel> Display for Syntax<T>
where
    T::Type: PrettyPrint<String>,
    T::Function: PrettyPrint<String>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let mut output = String::new();
        self.format(&self.symbols, &mut output)?;
        write!(f, "{}", output)
    }
}

/// Implementation for Literal
impl<W: Write> PrettyPrint<W> for Literal {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut W) -> Result<(), fmt::Error> {
        match self {
            Literal::String(spur) => write!(writer, "\"{}\"", interner.resolve(spur)),
            Literal::F64(value) => write!(writer, "{}f64", value),
            Literal::F32(value) => write!(writer, "{}f32", value),
            Literal::I64(value) => write!(writer, "{}i64", value),
            Literal::I32(value) => write!(writer, "{}i32", value),
            Literal::U64(value) => write!(writer, "{}u64", value),
            Literal::U32(value) => write!(writer, "{}u32", value),
            Literal::Bool(value) => write!(writer, "{}", value),
            Literal::Char(value) => write!(writer, "'{}'", value),
        }
    }
}

pub fn write_generic_header<W: Write>(interner: &ThreadedRodeo, generics: &IndexMap<Spur, Vec<GenericTypeRef>>, writer: &mut W) -> Result<(), fmt::Error> {
    if !generics.is_empty() {
        write!(writer, "<")?;
        for (name, generics) in generics {
            write!(writer, "{}: ", interner.resolve(name))?;
            for (i, generic) in generics.iter().enumerate() {
                if i > 0 {
                    write!(writer, " + ")?;
                }
                generic.format(interner, writer)?;
            }
        }
        write!(writer, ">")?;
    }
    Ok(())
}

pub fn write_generics<W: Write, T: PrettyPrint<W>>(interner: &ThreadedRodeo, generics: &Vec<T>, writer: &mut W) -> Result<(), fmt::Error> {
    if !generics.is_empty() {
        write!(writer, "<")?;
        for (i, generic) in generics.iter().enumerate() {
            if i > 0 {
                write!(writer, ", ")?;
            }
            generic.format(interner, writer)?;
        }
        write!(writer, ">")?;
    }
    Ok(())
}

pub fn write_parameters<T: TypeReference, W: Write>(interner: &ThreadedRodeo, parameters: &Vec<(Spur, T)>, writer: &mut W) -> Result<(), fmt::Error> {
    for (i, (name, ty)) in parameters.iter().enumerate() {
        if i > 0 {
            write!(writer, ", ")?;
        }
        write!(writer, "{}: ", interner.resolve(name))?;
        ty.format(interner, writer)?;
    }
    Ok(())
}

pub struct NestedWriter<W> {
    pub writer: W,
    pub depth: usize
}

impl<W: Write> NestedWriter<W> {
    pub fn indent(&mut self) -> fmt::Result {
        for _ in 0..self.depth {
            write!(self.writer, "    ")?;
        }
        Ok(())
    }

    pub fn indent_lower(&mut self) -> fmt::Result {
        for _ in 0..self.depth - 1 {
            write!(self.writer, "    ")?;
        }
        Ok(())
    }
}

impl<W: Write> Write for NestedWriter<W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.writer.write_str(s)
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
        self.writer.write_char(c)
    }

    fn write_fmt(&mut self, args: Arguments<'_>) -> fmt::Result {
        self.writer.write_fmt(args)
    }
}