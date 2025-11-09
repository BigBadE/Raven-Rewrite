//! Runtime value representation

#![allow(
    clippy::min_ident_chars,
    reason = "Short identifiers like i, f, b, s are conventional in value implementations"
)]

use rv_intern::Symbol;
use std::fmt;

/// Runtime value
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Unit value
    Unit,
    /// Boolean value
    Bool(bool),
    /// Integer value (i64)
    Int(i64),
    /// Float value (f64)
    Float(f64),
    /// String value
    String(String),
    /// Tuple value
    Tuple(Vec<Self>),
    /// Struct value
    Struct {
        /// Struct name
        name: Symbol,
        /// Field values
        fields: Vec<Self>,
    },
    /// Enum variant value
    Enum {
        /// Enum name
        name: Symbol,
        /// Variant index
        variant_idx: usize,
        /// Field values
        fields: Vec<Self>,
    },
    /// Array value
    Array(Vec<Self>),
}

impl Value {
    /// Get the value as a boolean, if possible
    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Get the value as an integer, if possible
    #[must_use]
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Self::Int(i) => Some(*i),
            _ => None,
        }
    }

    /// Get the value as a float, if possible
    #[must_use]
    pub fn as_float(&self) -> Option<f64> {
        match self {
            Self::Float(f) => Some(*f),
            _ => None,
        }
    }

    /// Check if value is truthy (for conditionals)
    #[must_use]
    pub fn is_truthy(&self) -> bool {
        match self {
            Self::Bool(b) => *b,
            Self::Int(i) => *i != 0,
            Self::Unit => false,
            _ => true,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(i) => write!(f, "{i}"),
            Self::Float(fl) => write!(f, "{fl}"),
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Tuple(elements) => {
                write!(f, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{elem}")?;
                }
                write!(f, ")")
            }
            Self::Struct { name, fields } => {
                write!(f, "{name:?} {{ ")?;
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{field}")?;
                }
                write!(f, " }}")
            }
            Self::Enum {
                name,
                variant_idx,
                fields,
            } => {
                write!(f, "{name:?}::variant{variant_idx}")?;
                if !fields.is_empty() {
                    write!(f, "(")?;
                    for (i, field) in fields.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{field}")?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Self::Array(elements) => {
                write!(f, "[")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{elem}")?;
                }
                write!(f, "]")
            }
        }
    }
}
