use crate::expression::HighExpression;
use crate::function::HighFunction;
use crate::function::{CodeBlock, HighTerminator};
use crate::statement::HighStatement;
use crate::types::{HighType, TypeData};
use crate::{RawFunctionRef, RawTypeRef};
use lasso::ThreadedRodeo;
use std::fmt::{Error, Write};
use syntax::util::pretty_print::{format_modifiers, write_comma_list, write_generic_header, write_generics, write_parameters, NestedWriter, PrettyPrint};
use syntax::PrettyPrintableSyntaxLevel;
use syntax::structure::traits::Terminator;

/// Implement PrettyPrint for HIR functions
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for HighFunction<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        format_modifiers(&self.modifiers, writer)?;
        write!(writer, "fn ")?;
        self.reference.format(interner, writer)?;

        write_generic_header(interner, &self.generics, writer)?;

        write!(writer, "(")?;
        write_parameters(interner, &self.parameters, writer)?;
        write!(writer, ")")?;

        // Add return type if present
        if let Some(return_type) = &self.return_type {
            write!(writer, " -> ")?;
            return_type.format(interner, writer)?;
        }

        write!(writer, " ")?;
        self.body.format(interner, writer)
    }
}

/// Implement PrettyPrint for HIR types (high level)
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for HighType<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        format_modifiers(&self.modifiers, writer)?;

        match &self.data {
            TypeData::Struct { fields } => {
                write!(writer, "struct ")?;
                self.reference.format(interner, writer)?;

                write_generic_header(interner, &self.generics, writer)?;

                write!(writer, " {{")?;
                writer.deepen(|writer| {
                    for (field_name, field_type) in fields {
                        write!(writer, "\n")?;
                        writer.indent()?;
                        write!(writer, "{}: ", interner.resolve(field_name))?;
                        field_type.format(interner, writer)?;
                        write!(writer, ",")?;
                    }
                    Ok(())
                })?;
                if !fields.is_empty() {
                    write!(writer, "\n")?;
                    writer.indent()?;
                }
                write!(writer, "}}")
            }
            TypeData::Trait { functions } => {
                write!(writer, "trait ")?;
                self.reference.format(interner, writer)?;

                write_generic_header(interner, &self.generics, writer)?;

                write!(writer, " {{\n")?;
                for func in functions {
                    write!(writer, "    ")?;
                    func.format(interner, writer)?;
                    write!(writer, "\n")?;
                }
                write!(writer, "}}")
            }
        }
    }
}

/// Implement PrettyPrint for CodeBlock
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for CodeBlock<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        write!(writer, "{{")?;
        writer.deepen(|writer| {
            for stmt in &self.statements {
                write!(writer, "\n")?;
                writer.indent()?;
                stmt.format(interner, writer)?;
            }

            self.terminator.format(interner, writer)?;
            if !self.terminator.is_none() {
                write!(writer, "\n")?;
            }
            Ok(())
        })?;

        if !self.statements.is_empty() {
            writer.indent()?;
        }

        write!(writer, "}}")
    }
}

/// Implement PrettyPrint for HIR expressions (high level)
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for HighExpression<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        match self {
            HighExpression::Literal(literal) => {
                literal.format(interner, writer)
            }
            HighExpression::Variable(name) => {
                write!(writer, "{}", interner.resolve(name))
            }
            HighExpression::CodeBlock { body, value } => {
                write!(writer, "{{\n")?;
                writer.deepen(|writer| {
                    for stmt in body {
                        writer.indent()?;
                        stmt.format(interner, writer)?;
                        write!(writer, "\n")?;
                    }
                    writer.indent()?;
                    value.format(interner, writer)?;
                    write!(writer, "\n")?;
                    Ok(())
                })?;
                writer.indent()?;
                write!(writer, "}}")
            }
            HighExpression::Assignment { declaration, variable, value } => {
                if *declaration {
                    write!(writer, "let ")?;
                }
                write!(writer, "{} = ", interner.resolve(variable))?;
                value.format(interner, writer)
            }
            HighExpression::FunctionCall { function, target, arguments } => {
                if let Some(target) = target {
                    target.format(interner, writer)?;
                    write!(writer, ".")?;
                }
                function.format(interner, writer)?;
                write!(writer, "(")?;
                write_comma_list(interner, arguments, writer)?;
                write!(writer, ")")
            }
            HighExpression::UnaryOperation { pre, symbol, value } => {
                let symbol_str = interner.resolve(symbol);
                if *pre {
                    write!(writer, "{}", symbol_str)?;
                    value.format(interner, writer)
                } else {
                    value.format(interner, writer)?;
                    write!(writer, "{}", symbol_str)
                }
            }
            HighExpression::BinaryOperation { symbol, first, second } => {
                first.format(interner, writer)?;
                write!(writer, " {} ", interner.resolve(symbol))?;
                second.format(interner, writer)
            }
            HighExpression::CreateStruct { target_struct, fields } => {
                target_struct.format(interner, writer)?;
                write!(writer, " {{ ")?;
                write_parameters(interner, fields, writer)?;
                write!(writer, " }}")
            }
        }
    }
}

/// Implement PrettyPrint for HIR statements (high level)
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for HighStatement<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        match self {
            HighStatement::Expression(expr) => {
                expr.format(interner, writer)?;
                write!(writer, ";")
            }
            HighStatement::CodeBlock(statements) => {
                write!(writer, "{{\n")?;
                writer.deepen(|writer| {
                    for stmt in statements {
                        writer.indent()?;
                        stmt.format(interner, writer)?;
                        write!(writer, "\n")?;
                    }
                    Ok(())
                })?;
                writer.indent()?;
                write!(writer, "}}")
            }
            HighStatement::Terminator(terminator) => {
                terminator.format(interner, writer)?;
                if !terminator.is_none() {
                    write!(writer, "\n")?;
                }
                Ok(())
            }
            HighStatement::If { conditions, else_branch } => {
                for (i, conditional) in conditions.iter().enumerate() {
                    if i > 0 {
                        write!(writer, " else ")?;
                    }
                    write!(writer, "if ")?;
                    conditional.condition.format(interner, writer)?;
                    write!(writer, " {{\n")?;
                    writer.deepen(|writer| {
                        for stmt in &conditional.branch {
                            writer.indent()?;
                            stmt.format(interner, writer)?;
                            write!(writer, "\n")?;
                        }
                        Ok(())
                    })?;
                    writer.indent()?;
                    write!(writer, "}}")?;
                }
                if let Some(else_stmts) = else_branch {
                    write!(writer, " else {{\n")?;
                    writer.deepen(|writer| {
                        for stmt in else_stmts {
                            writer.indent()?;
                            stmt.format(interner, writer)?;
                            write!(writer, "\n")?;
                        }
                        Ok(())
                    })?;
                    writer.indent()?;
                    write!(writer, "}}")?;
                }
                Ok(())
            }
            HighStatement::While { condition } => {
                write!(writer, "while ")?;
                condition.condition.format(interner, writer)?;
                write!(writer, " {{\n")?;
                writer.deepen(|writer| {
                    for stmt in &condition.branch {
                        writer.indent()?;
                        stmt.format(interner, writer)?;
                        write!(writer, "\n")?;
                    }
                    Ok(())
                })?;
                writer.indent()?;
                write!(writer, "}}")
            }
            HighStatement::For { condition } => {
                write!(writer, "for ")?;
                condition.condition.format(interner, writer)?;
                write!(writer, " {{\n")?;
                writer.deepen(|writer| {
                    for stmt in &condition.branch {
                        writer.indent()?;
                        stmt.format(interner, writer)?;
                        write!(writer, "\n")?;
                    }
                    Ok(())
                })?;
                writer.indent()?;
                write!(writer, "}}")
            }
            HighStatement::Loop { body } => {
                write!(writer, "loop {{\n")?;
                writer.deepen(|writer| {
                    for stmt in body {
                        writer.indent()?;
                        stmt.format(interner, writer)?;
                        write!(writer, "\n")?;
                    }
                    Ok(())
                })?;
                writer.indent()?;
                write!(writer, "}}")
            }
        }
    }
}

/// Implement PrettyPrint for HIR terminators (high level)
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for HighTerminator<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        match self {
            HighTerminator::Return(expr) => {
                write!(writer, "return")?;
                if let Some(expr) = expr {
                    write!(writer, " ")?;
                    expr.format(interner, writer)?;
                }
                write!(writer, ";")
            }
            HighTerminator::Break => write!(writer, "break;"),
            HighTerminator::Continue => write!(writer, "continue;"),
            HighTerminator::None => Ok(()),
        }
    }
}

/// Implement PrettyPrint for raw type references
impl<W: Write> PrettyPrint<W> for RawTypeRef {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        // Format the path
        for (i, segment) in self.path.iter().enumerate() {
            if i > 0 {
                write!(writer, "::")?;
            }
            write!(writer, "{}", interner.resolve(segment))?;
        }

        write_generics(interner, &self.generics, writer)
    }
}

/// Implement PrettyPrint for raw function references
impl<W: Write> PrettyPrint<W> for RawFunctionRef {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        self.path.format(interner, writer)?;
        write_generics(interner, &self.generics, writer)
    }
}