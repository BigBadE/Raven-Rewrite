use crate::structure::literal::Literal;
use crate::{Syntax, SyntaxLevel};
use lasso::ThreadedRodeo;
use crate::structure::Modifier;

/// Trait for pretty printing with string interpolation
pub trait PrettyPrint {
    /// Format this item as a human-readable string
    fn format(&self, interner: &ThreadedRodeo) -> String;
}

/// Enhanced trait for context-aware pretty printing that can resolve references
pub trait PrettyPrintWithContext<T: SyntaxLevel> {
    /// Format this item with full syntax context for reference resolution
    fn format_with_context(&self, syntax: &Syntax<T>, interner: &ThreadedRodeo) -> String;
}

/// Implementation for Syntax
impl<T: SyntaxLevel> PrettyPrint for Syntax<T>
where
    T::Type: PrettyPrint,
    T::Function: PrettyPrint,
{
    fn format(&self, interner: &ThreadedRodeo) -> String {
        let mut output = String::new();
        
        // Format types
        for (i, type_def) in self.types.iter().enumerate() {
            if i > 0 { output.push('\n'); }
            output.push_str(&type_def.format(interner));
            output.push('\n');
        }
        
        // Add separator between types and functions
        if !self.types.is_empty() && !self.functions.is_empty() {
            output.push('\n');
        }
        
        // Format functions
        for (i, function) in self.functions.iter().enumerate() {
            if i > 0 { output.push('\n'); }
            output.push_str(&function.format(interner));
            output.push('\n');
        }
        
        if output.trim().is_empty() {
            output.push_str("// Empty syntax\n");
        }
        
        output
    }
}

/// Enhanced implementation for Syntax with context-aware formatting
impl<T: SyntaxLevel> PrettyPrintWithContext<T> for Syntax<T>
where
    T::Type: PrettyPrintWithContext<T>,
    T::Function: PrettyPrintWithContext<T>,
{
    fn format_with_context(&self, _syntax: &Syntax<T>, interner: &ThreadedRodeo) -> String {
        let mut output = String::new();
        
        // Format types with context
        for (i, type_def) in self.types.iter().enumerate() {
            if i > 0 { output.push('\n'); }
            output.push_str(&type_def.format_with_context(self, interner));
            output.push('\n');
        }
        
        // Add separator between types and functions
        if !self.types.is_empty() && !self.functions.is_empty() {
            output.push('\n');
        }
        
        // Format functions with context
        for (i, function) in self.functions.iter().enumerate() {
            if i > 0 { output.push('\n'); }
            output.push_str(&function.format_with_context(self, interner));
            output.push('\n');
        }
        
        if output.trim().is_empty() {
            output.push_str("// Empty syntax\n");
        }
        
        output
    }
}

/// Implement Display for Syntax when its types implement PrettyPrint
impl<T: SyntaxLevel> std::fmt::Display for Syntax<T>
where
    T::Type: PrettyPrintWithContext<T>,
    T::Function: PrettyPrintWithContext<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format_with_context(self, &self.symbols))
    }
}

/// Implementation for Literal
impl PrettyPrint for Literal {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        match self {
            Literal::String(spur) => format!("\"{}\"", interner.resolve(spur)),
            Literal::F64(value) => format!("{}f64", value),
            Literal::F32(value) => format!("{}f32", value),
            Literal::I64(value) => format!("{}i64", value),
            Literal::I32(value) => format!("{}i32", value),
            Literal::U64(value) => format!("{}u64", value),
            Literal::U32(value) => format!("{}u32", value),
            Literal::Bool(value) => value.to_string(),
            Literal::Char(value) => format!("'{}'", value),
        }
    }
}

/// Helper function to format a list of modifiers
pub fn format_modifiers(modifiers: &[Modifier]) -> String {
    let mut result = String::new();
    for modifier in modifiers {
        match modifier {
            Modifier::PUBLIC => result.push_str("pub "),
            Modifier::OPERATION => result.push_str("operation "),
        }
    }
    result
}

/// Helper function to format a path (list of Spurs) as a string
pub fn format_path(path: &[lasso::Spur], interner: &ThreadedRodeo) -> String {
    let mut result = String::new();
    for (i, part) in path.iter().enumerate() {
        if i > 0 {
            result.push_str("::");
        }
        result.push_str(interner.resolve(part));
    }
    result
}