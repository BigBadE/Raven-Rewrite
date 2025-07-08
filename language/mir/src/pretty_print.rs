use crate::expression::MediumExpression;
use crate::function::MediumFunction;
use crate::statement::MediumStatement;
use crate::types::MediumType;
use crate::{MediumSyntaxLevel, MediumTerminator, Operand, Place, PlaceElem};
use lasso::ThreadedRodeo;
use syntax::util::pretty_print::{format_modifiers, PrettyPrint, PrettyPrintWithContext};
use syntax::{FunctionRef, Syntax, TypeRef};

/// Implement PrettyPrint for MIR functions
impl PrettyPrint for MediumFunction<MediumSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();
        
        // Add modifiers
        code.push_str(&format_modifiers(&self.modifiers));
        
        code.push_str("fn ");
        code.push_str(interner.resolve(&self.name));
        
        // Add parameters
        code.push('(');
        let param_strs: Vec<String> = self.parameters.iter()
            .enumerate()
            .map(|(i, type_ref)| {
                format!("param_{}: Type{}", i, type_ref)
            })
            .collect();
        code.push_str(&param_strs.join(", "));
        code.push(')');
        
        // Add return type if present
        if let Some(return_type) = &self.return_type {
            code.push_str(" -> Type");
            code.push_str(&return_type.to_string());
        }
        
        code.push_str(" {\n");
        
        // Format basic blocks
        for (block_id, block) in self.body.iter().enumerate() {
            code.push_str(&format!("  bb{}:\n", block_id));
            
            // Format statements
            for statement in &block.statements {
                code.push_str("    ");
                code.push_str(&statement.format(interner));
                code.push('\n');
            }
            
            // Format terminator
            code.push_str("    ");
            code.push_str(&block.terminator.format(interner));
            code.push('\n');
            
            if block_id < self.body.len() - 1 {
                code.push('\n');
            }
        }
        
        code.push('}');
        code
    }
}

/// Implement context-aware PrettyPrint for MIR functions
impl PrettyPrintWithContext<MediumSyntaxLevel> for MediumFunction<MediumSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<MediumSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();
        
        // Add modifiers
        code.push_str(&format_modifiers(&self.modifiers));
        
        code.push_str("fn ");
        code.push_str(interner.resolve(&self.name));
        
        // Add parameters with resolved type names
        code.push('(');
        let param_strs: Vec<String> = self.parameters.iter()
            .enumerate()
            .map(|(i, type_ref)| {
                let type_name = resolve_type_name(type_ref, syntax, interner);
                format!("param_{}: {}", i, type_name)
            })
            .collect();
        code.push_str(&param_strs.join(", "));
        code.push(')');
        
        // Add return type if present
        if let Some(return_type) = &self.return_type {
            code.push_str(" -> ");
            code.push_str(&resolve_type_name(return_type, syntax, interner));
        }
        
        code.push_str(" {\n");
        
        // Format basic blocks with context
        for (block_id, block) in self.body.iter().enumerate() {
            code.push_str(&format!("  bb{}:\n", block_id));
            
            // Format statements with context
            for statement in &block.statements {
                code.push_str("    ");
                code.push_str(&statement.format_with_context(syntax, interner));
                code.push('\n');
            }
            
            // Format terminator with context
            code.push_str("    ");
            code.push_str(&block.terminator.format_with_context(syntax, interner));
            code.push('\n');
            
            if block_id < self.body.len() - 1 {
                code.push('\n');
            }
        }
        
        code.push('}');
        code
    }
}

/// Implement PrettyPrint for MIR types
impl PrettyPrint for MediumType<MediumSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();
        
        // Add modifiers
        code.push_str(&format_modifiers(&self.modifiers));
        
        code.push_str("struct ");
        code.push_str(interner.resolve(&self.name));
        
        code.push_str(" {\n");
        for (i, field_type) in self.fields.iter().enumerate() {
            code.push_str(&format!("    field_{}: Type{},\n", i, field_type));
        }
        code.push('}');
        
        code
    }
}

/// Implement context-aware PrettyPrint for MIR types
impl PrettyPrintWithContext<MediumSyntaxLevel> for MediumType<MediumSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<MediumSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();
        
        // Add modifiers
        code.push_str(&format_modifiers(&self.modifiers));
        
        code.push_str("struct ");
        code.push_str(interner.resolve(&self.name));
        
        code.push_str(" {\n");
        for (i, field_type) in self.fields.iter().enumerate() {
            let type_name = resolve_type_name(field_type, syntax, interner);
            code.push_str(&format!("    field_{}: {},\n", i, type_name));
        }
        code.push('}');
        
        code
    }
}

/// Implement PrettyPrint for MIR statements
impl PrettyPrint for MediumStatement<MediumSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        match self {
            MediumStatement::Assign { place, value } => {
                format!("{} = {};", place.format(interner), value.format(interner))
            },
            MediumStatement::StorageLive(local, type_ref) => {
                format!("StorageLive(_{}: Type{});", local, type_ref)
            },
            MediumStatement::StorageDead(local) => {
                format!("StorageDead(_{});", local)
            },
            MediumStatement::Noop => "noop;".to_string(),
        }
    }
}

/// Implement context-aware PrettyPrint for MIR statements
impl PrettyPrintWithContext<MediumSyntaxLevel> for MediumStatement<MediumSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<MediumSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        match self {
            MediumStatement::Assign { place, value } => {
                format!("{} = {};", 
                    place.format_with_context(syntax, interner), 
                    value.format_with_context(syntax, interner))
            },
            MediumStatement::StorageLive(local, type_ref) => {
                let type_name = resolve_type_name(type_ref, syntax, interner);
                format!("StorageLive(_{}: {});", local, type_name)
            },
            MediumStatement::StorageDead(local) => {
                format!("StorageDead(_{});", local)
            },
            MediumStatement::Noop => "noop;".to_string(),
        }
    }
}

/// Implement PrettyPrint for MIR expressions
impl PrettyPrint for MediumExpression<MediumSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        match self {
            MediumExpression::Use(operand) => operand.format(interner),
            MediumExpression::Literal(literal) => literal.format(interner),
            MediumExpression::FunctionCall { func, args } => {
                let mut code = format!("func_{}", func.reference);
                code.push('(');
                let arg_strs: Vec<String> = args.iter()
                    .map(|arg| arg.format(interner))
                    .collect();
                code.push_str(&arg_strs.join(", "));
                code.push(')');
                code
            },
            MediumExpression::CreateStruct { struct_type, fields } => {
                let mut code = format!("Type{}", struct_type);
                code.push_str(" { ");
                let field_strs: Vec<String> = fields.iter()
                    .map(|(name, operand)| {
                        format!("{}: {}", interner.resolve(name), operand.format(interner))
                    })
                    .collect();
                code.push_str(&field_strs.join(", "));
                code.push_str(" }");
                code
            }
        }
    }
}

/// Implement context-aware PrettyPrint for MIR expressions
impl PrettyPrintWithContext<MediumSyntaxLevel> for MediumExpression<MediumSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<MediumSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        match self {
            MediumExpression::Use(operand) => operand.format_with_context(syntax, interner),
            MediumExpression::Literal(literal) => literal.format(interner),
            MediumExpression::FunctionCall { func, args } => {
                let function_name = resolve_function_name(func, syntax, interner);
                let mut code = function_name;
                code.push('(');
                let arg_strs: Vec<String> = args.iter()
                    .map(|arg| arg.format_with_context(syntax, interner))
                    .collect();
                code.push_str(&arg_strs.join(", "));
                code.push(')');
                code
            },
            MediumExpression::CreateStruct { struct_type, fields } => {
                let type_name = resolve_type_name(struct_type, syntax, interner);
                let mut code = type_name;
                code.push_str(" { ");
                let field_strs: Vec<String> = fields.iter()
                    .map(|(name, operand)| {
                        format!("{}: {}", interner.resolve(name), operand.format_with_context(syntax, interner))
                    })
                    .collect();
                code.push_str(&field_strs.join(", "));
                code.push_str(" }");
                code
            }
        }
    }
}

/// Implement PrettyPrint for MIR terminators
impl PrettyPrint for MediumTerminator<MediumSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        match self {
            MediumTerminator::Goto(block_id) => format!("goto -> bb{};", block_id),
            MediumTerminator::Switch { discriminant, targets, fallback } => {
                let mut code = format!("switchInt({}) -> [", discriminant.format(interner));
                let target_strs: Vec<String> = targets.iter()
                    .map(|(literal, block_id)| {
                        format!("{}: bb{}", literal.format(interner), block_id)
                    })
                    .collect();
                code.push_str(&target_strs.join(", "));
                code.push_str(&format!(", otherwise: bb{}];", fallback));
                code
            },
            MediumTerminator::Return(expr) => {
                if let Some(expr) = expr {
                    format!("return {};", expr.format(interner))
                } else {
                    "return;".to_string()
                }
            },
            MediumTerminator::Unreachable => "unreachable;".to_string(),
        }
    }
}

/// Implement context-aware PrettyPrint for MIR terminators
impl PrettyPrintWithContext<MediumSyntaxLevel> for MediumTerminator<MediumSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<MediumSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        match self {
            MediumTerminator::Goto(block_id) => format!("goto -> bb{};", block_id),
            MediumTerminator::Switch { discriminant, targets, fallback } => {
                let mut code = format!("switchInt({}) -> [", discriminant.format_with_context(syntax, interner));
                let target_strs: Vec<String> = targets.iter()
                    .map(|(literal, block_id)| {
                        format!("{}: bb{}", literal.format(interner), block_id)
                    })
                    .collect();
                code.push_str(&target_strs.join(", "));
                code.push_str(&format!(", otherwise: bb{}];", fallback));
                code
            },
            MediumTerminator::Return(expr) => {
                if let Some(expr) = expr {
                    format!("return {};", expr.format_with_context(syntax, interner))
                } else {
                    "return;".to_string()
                }
            },
            MediumTerminator::Unreachable => "unreachable;".to_string(),
        }
    }
}

/// Implement PrettyPrint for Operands
impl PrettyPrint for Operand {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        match self {
            Operand::Copy(place) => format!("copy {}", place.format(interner)),
            Operand::Move(place) => format!("move {}", place.format(interner)),
            Operand::Constant(literal) => literal.format(interner),
        }
    }
}

/// Implement context-aware PrettyPrint for Operands
impl PrettyPrintWithContext<MediumSyntaxLevel> for Operand {
    fn format_with_context(&self, syntax: &Syntax<MediumSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        match self {
            Operand::Copy(place) => format!("copy {}", place.format_with_context(syntax, interner)),
            Operand::Move(place) => format!("move {}", place.format_with_context(syntax, interner)),
            Operand::Constant(literal) => literal.format(interner),
        }
    }
}

/// Implement PrettyPrint for Places
impl PrettyPrint for Place {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        let mut code = format!("_{}", self.local);
        for projection in &self.projection {
            match projection {
                PlaceElem::Deref => code.push_str("*"),
                PlaceElem::Field(field_name) => {
                    code.push('.');
                    code.push_str(interner.resolve(field_name));
                },
                PlaceElem::Index(index) => {
                    code.push_str(&format!("[{}]", index));
                }
            }
        }
        code
    }
}

/// Implement context-aware PrettyPrint for Places
impl PrettyPrintWithContext<MediumSyntaxLevel> for Place {
    fn format_with_context(&self, _syntax: &Syntax<MediumSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        let mut code = format!("_{}", self.local);
        for projection in &self.projection {
            match projection {
                PlaceElem::Deref => code.push_str("*"),
                PlaceElem::Field(field_name) => {
                    code.push('.');
                    code.push_str(interner.resolve(field_name));
                },
                PlaceElem::Index(index) => {
                    code.push_str(&format!("[{}]", index));
                }
            }
        }
        code
    }
}

/// Helper function to resolve a TypeRef to its actual name
fn resolve_type_name(type_ref: &TypeRef, syntax: &Syntax<MediumSyntaxLevel>, interner: &ThreadedRodeo) -> String {
    if let Some(type_def) = syntax.types.get(*type_ref) {
        interner.resolve(&type_def.name).to_string()
    } else {
        format!("Type{}", type_ref)
    }
}

/// Helper function to resolve a FunctionRef to its actual name
fn resolve_function_name(func_ref: &FunctionRef, syntax: &Syntax<MediumSyntaxLevel>, interner: &ThreadedRodeo) -> String {
    if let Some(func_def) = syntax.functions.get(func_ref.reference) {
        let mut name = interner.resolve(&func_def.name).to_string();
        if !func_ref.generics.is_empty() {
            name.push('<');
            let generic_strs: Vec<String> = func_ref.generics.iter()
                .map(|g| match g {
                    syntax::GenericTypeRef::Struct { reference, .. } => {
                        if let Some(type_def) = syntax.types.get(*reference) {
                            interner.resolve(&type_def.name).to_string()
                        } else {
                            format!("Type{}", reference)
                        }
                    },
                    syntax::GenericTypeRef::Generic { reference } => format!("T{}", reference),
                })
                .collect();
            name.push_str(&generic_strs.join(", "));
            name.push('>');
        }
        name
    } else {
        format!("func_{}", func_ref.reference)
    }
}