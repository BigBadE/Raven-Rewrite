use std::fmt::{Error, Write};
use crate::expression::HighExpression;
use crate::function::HighFunction;
use crate::function::{CodeBlock, HighTerminator};
use crate::statement::HighStatement;
use crate::types::{HighType, TypeData};
use crate::{HighSyntaxLevel, RawFunctionRef, RawSyntaxLevel, RawTypeRef};
use indexmap::IndexMap;
use lasso::{Spur, ThreadedRodeo};
use syntax::util::pretty_print::{write_generic_header, write_generics, write_parameters, NestedWriter, PrettyPrint};
use syntax::{GenericFunctionRef, GenericTypeRef, Syntax};

/// Enhanced function that can resolve generic names when provided with generic context
pub fn format_generic_type_ref_with_generics_context(
    type_ref: &GenericTypeRef,
    interner: &ThreadedRodeo,
    generics_context: &IndexMap<Spur, Vec<GenericTypeRef>>
) -> String {
    match type_ref {
        GenericTypeRef::Struct { reference, generics } => {
            let mut code = reference.format(interner);
            if !generics.is_empty() {
                code.push('<');
                let generic_strs: Vec<String> = generics.iter()
                    .map(|g| format_generic_type_ref_with_generics_context(g, interner, generics_context))
                    .collect();
                code.push_str(&generic_strs.join(", "));
                code.push('>');
            }
            code
        },
        GenericTypeRef::Generic { reference } => {
            // Try to resolve the generic name from context
            if let Some((generic_name, _)) = generics_context.get_index(*reference) {
                interner.resolve(generic_name).to_string()
            } else {
                format!("T{}", reference)
            }
        }
    }
}

/// Helper function to format a GenericTypeRef with function generics context
pub fn format_generic_type_ref_with_function_context(
    type_ref: &GenericTypeRef,
    syntax: &Syntax<HighSyntaxLevel>, 
    interner: &ThreadedRodeo,
    function_generics: &IndexMap<lasso::Spur, Vec<GenericTypeRef>>
) -> String {
    format_generic_type_ref_with_generics_context(type_ref, syntax, interner, function_generics)
}

/// Helper function to format a GenericTypeRef with type generics context
pub fn format_generic_type_ref_with_type_context(
    type_ref: &GenericTypeRef,
    syntax: &Syntax<HighSyntaxLevel>,
    interner: &ThreadedRodeo,
    type_generics: &IndexMap<Spur, Vec<GenericTypeRef>>
) -> String {
    format_generic_type_ref_with_generics_context(type_ref, syntax, interner, type_generics)
}

/// Implement context-aware PrettyPrint for HIR functions (high level)
impl<W: Write> PrettyPrint<W> for HighFunction<HighSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut W) -> Result<(), Error> {
        write!(writer, "{} fn ", self.modifiers.join(" "))?;
        self.reference.format(interner, writer)?;

        write_generic_header(interner, &self.generics, writer)?;

        write!(writer, "(")?;
        write_parameters(interner, &self.parameters, writer)?;
        write!(writer, ") ")?;

        // Add return type if present with resolved name (including generics)
        if let Some(return_type) = &self.return_type {
            write!(writer, "-> ")?;
            return_type.format(interner, writer)?;
        }

        self.body.format(interner, writer)
    }
}

/// Implement PrettyPrint for HIR functions (raw level)
impl PrettyPrint for HighFunction<RawSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();
        
        // Add modifiers
        code.push_str(&format_modifiers(&self.modifiers));
        
        code.push_str("fn ");
        code.push_str(&self.reference.format(interner));
        
        // Add generics if any
        if !self.generics.is_empty() {
            code.push('<');
            let generic_names: Vec<String> = self.generics.keys()
                .map(|spur| interner.resolve(spur).to_string())
                .collect();
            code.push_str(&generic_names.join(", "));
            code.push('>');
        }
        
        // Add parameters
        code.push('(');
        let param_strs: Vec<String> = self.parameters.iter()
            .map(|(name, type_ref)| {
                format!("{}: {}", interner.resolve(name), type_ref.format(interner))
            })
            .collect();
        code.push_str(&param_strs.join(", "));
        code.push(')');
        
        // Add return type if present
        if let Some(return_type) = &self.return_type {
            code.push_str(" -> ");
            code.push_str(&return_type.format(interner));
        }
        
        code.push_str(" {\n    // Function body\n}");
        code
    }
}

/// Implement context-aware PrettyPrint for HIR functions (raw level)
impl PrettyPrintWithContext<RawSyntaxLevel> for HighFunction<RawSyntaxLevel> {
    fn format_with_context(&self, _syntax: &Syntax<RawSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        self.format(interner)
    }
}

/// Implement context-aware PrettyPrint for HIR types (high level)
impl PrettyPrintWithContext<HighSyntaxLevel> for HighType<HighSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();
        
        // Add modifiers
        code.push_str(&format_modifiers(&self.modifiers));
        
        match &self.data {
            TypeData::Struct { fields } => {
                code.push_str("struct ");
                code.push_str(&self.reference.format(interner));
                
                // Add generics if any with their actual names
                if !self.generics.is_empty() {
                    code.push('<');
                    let generic_names: Vec<String> = self.generics.keys()
                        .map(|spur| interner.resolve(spur).to_string())
                        .collect();
                    code.push_str(&generic_names.join(", "));
                    code.push('>');
                }
                
                code.push_str(" {\n");
                for (field_name, field_type) in fields {
                    code.push_str("    ");
                    code.push_str(interner.resolve(field_name));
                    code.push_str(": ");
                    // Use type's generic context for field type resolution
                    code.push_str(&format_generic_type_ref_with_type_context(field_type, syntax, interner, &self.generics));
                    code.push_str(",\n");
                }
                code.push('}');
            },
            TypeData::Trait { functions } => {
                code.push_str("trait ");
                code.push_str(&self.reference.format(interner));
                
                // Add generics if any with their actual names
                if !self.generics.is_empty() {
                    code.push('<');
                    let generic_names: Vec<String> = self.generics.keys()
                        .map(|spur| interner.resolve(spur).to_string())
                        .collect();
                    code.push_str(&generic_names.join(", "));
                    code.push('>');
                }
                
                code.push_str(" {\n");
                for func in functions {
                    code.push_str("    ");
                    code.push_str(&func.format_with_context(syntax, interner));
                    code.push('\n');
                }
                code.push('}');
            }
        }
        
        code
    }
}

/// Implement PrettyPrint for HIR types (raw level)
impl PrettyPrint for HighType<RawSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();
        
        // Add modifiers
        code.push_str(&format_modifiers(&self.modifiers));
        
        match &self.data {
            TypeData::Struct { fields } => {
                code.push_str("struct ");
                code.push_str(&self.reference.format(interner));
                
                // Add generics if any
                if !self.generics.is_empty() {
                    code.push('<');
                    let generic_names: Vec<String> = self.generics.keys()
                        .map(|spur| interner.resolve(spur).to_string())
                        .collect();
                    code.push_str(&generic_names.join(", "));
                    code.push('>');
                }
                
                code.push_str(" {\n");
                for (field_name, field_type) in fields {
                    code.push_str("    ");
                    code.push_str(interner.resolve(field_name));
                    code.push_str(": ");
                    code.push_str(&field_type.format(interner));
                    code.push_str(",\n");
                }
                code.push('}');
            },
            TypeData::Trait { functions } => {
                code.push_str("trait ");
                code.push_str(&self.reference.format(interner));
                
                // Add generics if any
                if !self.generics.is_empty() {
                    code.push('<');
                    let generic_names: Vec<String> = self.generics.keys()
                        .map(|spur| interner.resolve(spur).to_string())
                        .collect();
                    code.push_str(&generic_names.join(", "));
                    code.push('>');
                }
                
                code.push_str(" {\n");
                for func in functions {
                    code.push_str("    ");
                    code.push_str(&func.format(interner));
                    code.push('\n');
                }
                code.push('}');
            }
        }
        
        code
    }
}

/// Implement context-aware PrettyPrint for HIR types (raw level)
impl PrettyPrintWithContext<RawSyntaxLevel> for HighType<RawSyntaxLevel> {
    fn format_with_context(&self, _syntax: &Syntax<RawSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        self.format(interner)
    }
}

/// Implement context-aware PrettyPrint for CodeBlock
impl<W: Write> PrettyPrint<NestedWriter<W>> for CodeBlock<HighSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        write!(writer, "{{\n")?;

        // Generate statements with context-aware formatting
        for stmt in &self.statements {
            writer.indent()?;
            stmt.format(interner, &mut writer.writer)?;
            write!(writer, "\n")?;
        }

        writer.indent()?;
        self.terminator.format(interner, writer)?;
        writer.indent()?;
        write!(writer, "}}")
    }
}

/// Implement context-aware PrettyPrint for HIR expressions
impl PrettyPrintWithContext<HighSyntaxLevel> for HighExpression<HighSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        match self {
            HighExpression::Literal(literal) => {
                literal.format(interner)
            },
            HighExpression::Variable(name) => interner.resolve(name).to_string(),
            HighExpression::CodeBlock { body, value } => {
                let mut code = String::new();
                code.push_str("{\n");
                for stmt in body {
                    code.push_str("    ");
                    code.push_str(&stmt.format_with_context(syntax, interner));
                    code.push('\n');
                }
                code.push_str("    ");
                code.push_str(&value.format_with_context(syntax, interner));
                code.push('\n');
                code.push_str("}");
                code
            },
            HighExpression::Assignment { declaration, variable, value } => {
                let mut code = String::new();
                if *declaration {
                    code.push_str("let ");
                }
                code.push_str(interner.resolve(variable));
                code.push_str(" = ");
                code.push_str(&value.format_with_context(syntax, interner));
                code
            },
            HighExpression::FunctionCall { function, target, arguments } => {
                let mut code = String::new();
                if let Some(target) = target {
                    code.push_str(&target.format_with_context(syntax, interner));
                    code.push('.');
                }
                // Use enhanced function reference formatting
                code.push_str(&function.format(interner));
                code.push('(');
                let arg_strs: Vec<String> = arguments.iter()
                    .map(|arg| arg.format_with_context(syntax, interner))
                    .collect();
                code.push_str(&arg_strs.join(", "));
                code.push(')');
                code
            },
            HighExpression::UnaryOperation { pre, symbol, value } => {
                let symbol_str = interner.resolve(symbol);
                if *pre {
                    format!("{}{}", symbol_str, value.format_with_context(syntax, interner))
                } else {
                    format!("{}{}", value.format_with_context(syntax, interner), symbol_str)
                }
            },
            HighExpression::BinaryOperation { symbol, first, second } => {
                format!("{} {} {}",
                    first.format_with_context(syntax, interner),
                    interner.resolve(symbol),
                    second.format_with_context(syntax, interner)
                )
            },
            HighExpression::CreateStruct { target_struct, fields } => {
                let mut code = String::new();
                // Use enhanced type reference formatting
                code.push_str(&format_generic_type_ref_with_generics_context(target_struct, syntax, interner, &IndexMap::new()));
                code.push_str(" { ");
                let field_strs: Vec<String> = fields.iter()
                    .map(|(name, expr)| {
                        format!("{}: {}", interner.resolve(name), expr.format_with_context(syntax, interner))
                    })
                    .collect();
                code.push_str(&field_strs.join(", "));
                code.push_str(" }");
                code
            },
        }
    }
}

/// Implement context-aware PrettyPrint for HIR statements
impl<W: Write> PrettyPrint<NestedWriter<W>> for HighStatement<HighSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        match self {
            HighStatement::Expression(expr) => {
                expr.format(interner, writer)?;
                write!(writer, ";")?
            },
            HighStatement::CodeBlock(statements) => {
                write!(writer, "{{\n")?;
                for stmt in statements {
                    writer.indent()?;
                    stmt.format(interner, &mut writer.writer)?;
                    write!(writer, "\n")?;
                }
                writer.indent_lower()?;
                write!(writer, "}}")
            },
            HighStatement::Terminator(terminator) => {
                terminator.format(interner, &mut writer.writer)
            },
            HighStatement::If { conditions, else_branch } => {
                for (i, conditional) in conditions.iter().enumerate() {
                    if i != 0 {
                        write!(writer, " else ")?;
                    }
                    write!(writer, "if ")?;
                    conditional.condition.format(interner, &mut writer.writer)?;
                    write!(writer, " {{\n")?;
                    for stmt in &conditional.branch {
                        writer.indent()?;
                        stmt.format(interner, &mut writer.writer)?;
                        write!(writer, "\n")?;
                    }
                    writer.indent_lower()?;
                    write!(writer, "}}")?;
                }
                if let Some(else_stmts) = else_branch {
                    write!(writer, " else {{\n")?;
                    for stmt in else_stmts {
                        code.push_str("    ");
                        code.push_str(&stmt.format_with_context(syntax, interner));
                        code.push('\n');
                    }
                    code.push_str("}");
                }
                code
            },
            HighStatement::While { condition } => {
                let mut code = String::new();
                code.push_str("while ");
                code.push_str(&condition.condition.format_with_context(syntax, interner));
                code.push_str(" {\n");
                for stmt in &condition.branch {
                    code.push_str("    ");
                    code.push_str(&stmt.format_with_context(syntax, interner));
                    code.push('\n');
                }
                code.push_str("}");
                code
            },
            HighStatement::For { condition } => {
                let mut code = String::new();
                code.push_str("for ");
                code.push_str(&condition.condition.format_with_context(syntax, interner));
                code.push_str(" {\n");
                for stmt in &condition.branch {
                    code.push_str("    ");
                    code.push_str(&stmt.format_with_context(syntax, interner));
                    code.push('\n');
                }
                code.push_str("}");
                code
            },
            HighStatement::Loop { body } => {
                let mut code = String::new();
                code.push_str("loop {\n");
                for stmt in body {
                    code.push_str("    ");
                    code.push_str(&stmt.format_with_context(syntax, interner));
                    code.push('\n');
                }
                code.push_str("}");
                code
            },
        }
    }
}

/// Implement context-aware PrettyPrint for HIR terminators
impl<W: Write> PrettyPrint<W> for HighTerminator<HighSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut W) -> Result<(), Error> {
        match self {
            HighTerminator::Return(expr) => {
                write!(writer, "return ")?;
                if let Some(expr) = expr {
                    write!(writer, " ")?;
                    expr.format(interner, writer)?;
                }
                write!(writer, ";\n")?;
            },
            HighTerminator::Break => write!(writer, "break;\n"),
            HighTerminator::Continue => write!(writer, "continue;\n"),
            HighTerminator::None => Ok(()),
        }
    }
}

/// Implement PrettyPrint for raw type references
impl<W: Write> PrettyPrint<W> for RawTypeRef {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut W) -> Result<(), Error> {
        self.path.format(interner, writer)?;
        write_generics(interner, &self.generics, writer)
    }
}

/// Implement PrettyPrint for raw function references
impl<W: Write> PrettyPrint<W> for RawFunctionRef {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut W) -> Result<(), Error> {
        self.path.format(interner, writer)?;
        write_generics(interner, &self.generics, writer)
    }
}