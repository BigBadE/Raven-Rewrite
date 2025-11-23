//! Const value representation

use rv_intern::Symbol;

/// A compile-time constant value
#[derive(Debug, Clone, PartialEq)]
pub enum ConstValue {
    /// Integer constant
    Int(i64),
    /// Floating-point constant
    Float(f64),
    /// Boolean constant
    Bool(bool),
    /// String constant
    String(String),
    /// Unit constant (())
    Unit,
    /// Tuple constant
    Tuple(Vec<ConstValue>),
    /// Struct constant with named fields
    Struct {
        /// Field values
        fields: Vec<(Symbol, ConstValue)>,
    },
    /// Array constant
    Array(Vec<ConstValue>),
}

impl ConstValue {
    /// Returns true if this is an integer value
    #[must_use]
    pub fn is_int(&self) -> bool {
        matches!(self, Self::Int(_))
    }

    /// Returns true if this is a boolean value
    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool(_))
    }

    /// Returns the integer value if this is an integer
    #[must_use]
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Self::Int(value) => Some(*value),
            _ => None,
        }
    }

    /// Returns the boolean value if this is a boolean
    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }

    /// Returns the float value if this is a float
    #[must_use]
    pub fn as_float(&self) -> Option<f64> {
        match self {
            Self::Float(value) => Some(*value),
            _ => None,
        }
    }
}
