use crate::expression::MediumExpression;
use crate::function::MediumFunction;
use crate::statement::MediumStatement;
use crate::types::MediumType;
use crate::{MediumSyntaxLevel, MediumTerminator, Operand, Place, PlaceElem};
use lasso::ThreadedRodeo;
use std::fmt::{Error, Write};
use syntax::util::pretty_print::{format_modifiers, write_comma_list, write_parameters, NestedWriter, PrettyPrint};
use syntax::PrettyPrintableSyntaxLevel;

/// Implement PrettyPrint for MIR functions
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for MediumFunction<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        format_modifiers(&self.modifiers, writer)?;
        write!(writer, "fn ")?;
        self.reference.format(interner, writer)?;

        // Add parameters
        write!(writer, "(")?;
        write_comma_list(interner, &self.parameters, writer)?;
        write!(writer, ")")?;
        
        // Add return type if present
        if let Some(return_type) = &self.return_type {
            write!(writer, " -> ")?;
            return_type.format(interner, writer)?;
        }
        
        write!(writer, " {{\n")?;
        
        // Format basic blocks
        for (block_id, block) in self.body.iter().enumerate() {
            write!(writer, "  bb{}:\n", block_id)?;
            
            // Format statements
            for statement in &block.statements {
                write!(writer, "    ")?;
                statement.format(interner, writer)?;
                write!(writer, "\n")?;
            }
            
            // Format terminator
            write!(writer, "    ")?;
            block.terminator.format(interner, writer)?;
            write!(writer, "\n")?;
            
            if block_id < self.body.len() - 1 {
                write!(writer, "\n")?;
            }
        }
        
        write!(writer, "}}")
    }
}

/// Implement PrettyPrint for MIR types
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for MediumType<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        format_modifiers(&self.modifiers, writer)?;
        write!(writer, "struct ")?;
        self.reference.format(interner, writer)?;

        write!(writer, " {{\n")?;
        write_comma_list(interner, &self.fields, writer)?;
        write!(writer, "}}")
    }
}

/// Implement PrettyPrint for MIR statements
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for MediumStatement<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        match self {
            MediumStatement::Assign { place, value } => {
                place.format(interner, writer)?;
                write!(writer, " = ")?;
                value.format(interner, writer)?;
                write!(writer, ";")
            },
            MediumStatement::StorageLive(local, type_ref) => {
                write!(writer, "StorageLive(_{}: ", local)?;
                type_ref.format(interner, writer)?;
                write!(writer, ");")
            },
            MediumStatement::StorageDead(local) => {
                write!(writer, "StorageDead(_{});", local)
            },
            MediumStatement::Noop => write!(writer, "noop;"),
        }
    }
}

/// Implement PrettyPrint for MIR expressions
impl<T: PrettyPrintableSyntaxLevel<W>, W: Write> PrettyPrint<W> for MediumExpression<T> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        match self {
            MediumExpression::Use(operand) => operand.format(interner, writer),
            MediumExpression::Literal(literal) => literal.format(interner, writer),
            MediumExpression::FunctionCall { func, args } => {
                func.format(interner, writer)?;
                write!(writer, "(")?;
                write_comma_list(interner, args, writer)?;
                write!(writer, ")")
            },
            MediumExpression::CreateStruct { struct_type, fields } => {
                struct_type.format(interner, writer)?;
                write!(writer, " {{ ")?;
                write_parameters(interner, fields, writer)?;
                write!(writer, " }}")
            }
        }
    }
}

/// Implement PrettyPrint for MIR terminators
impl<W: Write> PrettyPrint<W> for MediumTerminator<MediumSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        match self {
            MediumTerminator::Goto(block_id) => {
                write!(writer, "goto -> bb{};", block_id)
            },
            MediumTerminator::Switch { discriminant, targets, fallback } => {
                write!(writer, "switchInt(")?;
                discriminant.format(interner, writer)?;
                write!(writer, ") -> [")?;
                for (i, (literal, block_id)) in targets.iter().enumerate() {
                    if i > 0 {
                        write!(writer, ", ")?;
                    }
                    literal.format(interner, writer)?;
                    write!(writer, ": bb{}", block_id)?;
                }
                write!(writer, ", otherwise: bb{}];", fallback)
            },
            MediumTerminator::Return(expr) => {
                write!(writer, "return")?;
                if let Some(expr) = expr {
                    write!(writer, " ")?;
                    expr.format(interner, writer)?;
                }
                write!(writer, ";")
            },
            MediumTerminator::Unreachable => write!(writer, "unreachable;"),
        }
    }
}

/// Implement PrettyPrint for Operands
impl<W: Write> PrettyPrint<W> for Operand {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        match self {
            Operand::Copy(place) => {
                write!(writer, "copy ")?;
                place.format(interner, writer)
            },
            Operand::Move(place) => {
                write!(writer, "move ")?;
                place.format(interner, writer)
            },
            Operand::Constant(literal) => literal.format(interner, writer),
        }
    }
}

/// Implement PrettyPrint for Places
impl<W: Write> PrettyPrint<W> for Place {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), Error> {
        write!(writer, "_{}", self.local)?;
        for projection in &self.projection {
            match projection {
                PlaceElem::Deref => write!(writer, "*")?,
                PlaceElem::Field(field_name) => {
                    write!(writer, ".")?;
                    write!(writer, "{}", interner.resolve(field_name))?;
                },
                PlaceElem::Index(index) => {
                    write!(writer, "[{}]", index)?;
                }
            }
        }
        Ok(())
    }
}