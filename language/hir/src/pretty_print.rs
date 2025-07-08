use crate::function::HighFunction;
use crate::types::{HighType, TypeData};
use crate::{HighSyntaxLevel, RawFunctionRef, RawSyntaxLevel, RawTypeRef};
use crate::expression::HighExpression;
use crate::statement::HighStatement;
use crate::function::{HighTerminator, CodeBlock};
use lasso::{Spur, ThreadedRodeo};
use syntax::util::pretty_print::{format_modifiers, format_path, PrettyPrint, PrettyPrintWithContext};
use syntax::{Syntax, GenericTypeRef, FunctionRef};
use indexmap::IndexMap;

/// Extension trait for HIR-specific pretty printing
pub trait HirPrettyPrint {
    /// Generate complete source code for HIR syntax with properly resolved names
    fn generate_hir_code(&self) -> String;
    
    /// Print HIR syntax as reconstructed source code
    fn print_hir_pretty(&self);
}

impl HirPrettyPrint for Syntax<HighSyntaxLevel> {
    fn generate_hir_code(&self) -> String {
        let mut output = String::new();
        
        // Generate types first
        for (i, type_def) in self.types.iter().enumerate() {
            if i > 0 { output.push('\n'); }
            output.push_str(&type_def.format_with_context(self, &self.symbols));
            output.push('\n');
        }
        
        // Add separator between types and functions
        if !self.types.is_empty() && !self.functions.is_empty() {
            output.push('\n');
        }
        
        // Generate functions
        for (i, function) in self.functions.iter().enumerate() {
            if i > 0 { output.push('\n'); }
            output.push_str(&function.format_with_context(self, &self.symbols));
            output.push('\n');
        }
        
        if output.trim().is_empty() {
            output.push_str("// Empty HIR\n");
        }
        
        output
    }
    
    fn print_hir_pretty(&self) {
        println!("{}", self.generate_hir_code());
    }
}

/// Implement PrettyPrint for HIR functions (high level)
impl PrettyPrint for HighFunction<HighSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        // Note: This is a fallback implementation without full context
        // For better output, use format_with_context instead
        format!("fn {} {{ /* body requires context */ }}", interner.resolve(&self.name))
    }
}

/// Enhanced function that can resolve generic names when provided with generic context
pub fn format_generic_type_ref_with_generics_context(
    type_ref: &GenericTypeRef,
    syntax: &Syntax<HighSyntaxLevel>,
    interner: &ThreadedRodeo,
    generics_context: &IndexMap<Spur, Vec<GenericTypeRef>>
) -> String {
    match type_ref {
        GenericTypeRef::Struct { reference, generics } => {
            // Try to resolve the actual type name
            let type_name = if let Some(type_def) = syntax.types.get(*reference) {
                interner.resolve(&type_def.name).to_string()
            } else {
                format!("Type{}", reference)
            };

            let mut code = type_name;
            if !generics.is_empty() {
                code.push('<');
                let generic_strs: Vec<String> = generics.iter()
                    .map(|g| format_generic_type_ref_with_generics_context(g, syntax, interner, generics_context))
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
    type_generics: &IndexMap<lasso::Spur, Vec<GenericTypeRef>>
) -> String {
    format_generic_type_ref_with_generics_context(type_ref, syntax, interner, type_generics)
}

/// Implement context-aware PrettyPrint for HIR functions (high level)
impl PrettyPrintWithContext<HighSyntaxLevel> for HighFunction<HighSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();
        
        // Add modifiers
        code.push_str(&format_modifiers(&self.modifiers));
        
        code.push_str("fn ");
        code.push_str(interner.resolve(&self.name));
        
        // Add generics if any with their actual names
        if !self.generics.is_empty() {
            code.push('<');
            let generic_names: Vec<String> = self.generics.keys()
                .map(|spur| interner.resolve(spur).to_string())
                .collect();
            code.push_str(&generic_names.join(", "));
            code.push('>');
        }
        
        // Add parameters with resolved type names (including generics)
        code.push('(');
        let param_strs: Vec<String> = self.parameters.iter()
            .map(|(name, type_ref)| {
                let type_name = format_generic_type_ref_with_function_context(type_ref, syntax, interner, &self.generics);
                format!("{}: {}", interner.resolve(name), type_name)
            })
            .collect();
        code.push_str(&param_strs.join(", "));
        code.push(')');
        
        // Add return type if present with resolved name (including generics)
        if let Some(return_type) = &self.return_type {
            code.push_str(" -> ");
            code.push_str(&format_generic_type_ref_with_function_context(return_type, syntax, interner, &self.generics));
        }
        
        // Generate body with existing formatting
        code.push_str(" ");
        code.push_str(&self.body.format_with_context(syntax, interner));
        
        code
    }
}

/// Implement PrettyPrint for HIR functions (raw level)
impl PrettyPrint for HighFunction<RawSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();
        
        // Add modifiers
        code.push_str(&format_modifiers(&self.modifiers));
        
        code.push_str("fn ");
        code.push_str(interner.resolve(&self.name));
        
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

/// Implement PrettyPrint for HIR types (high level)
impl PrettyPrint for HighType<HighSyntaxLevel> {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        // Note: This is a fallback implementation without full context
        // For better output, use format_with_context instead
        format!("struct {} {{ /* fields require context */ }}", interner.resolve(&self.name))
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
                code.push_str(interner.resolve(&self.name));
                
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
                code.push_str(interner.resolve(&self.name));
                
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
                code.push_str(interner.resolve(&self.name));
                
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
                code.push_str(interner.resolve(&self.name));
                
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
impl PrettyPrintWithContext<HighSyntaxLevel> for CodeBlock<HighSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        let mut code = String::new();

        code.push_str("{\n");
        
        // Generate statements with context-aware formatting
        for stmt in &self.statements {
            code.push_str("    ");
            code.push_str(&stmt.format_with_context(syntax, interner));
            code.push('\n');
        }

        // Generate terminator with context-aware formatting
        code.push_str("    ");
        code.push_str(&self.terminator.format_with_context(syntax, interner));
        code.push('\n');
        
        code.push_str("}");

        code
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
                code.push_str(&format_function_ref_with_context(function, syntax, interner));
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
impl PrettyPrintWithContext<HighSyntaxLevel> for HighStatement<HighSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        match self {
            HighStatement::Expression(expr) => {
                format!("{};", expr.format_with_context(syntax, interner))
            },
            HighStatement::CodeBlock(statements) => {
                let mut code = String::new();
                code.push_str("{\n");
                for stmt in statements {
                    code.push_str("    ");
                    code.push_str(&stmt.format_with_context(syntax, interner));
                    code.push('\n');
                }
                code.push_str("}");
                code
            },
            HighStatement::Terminator(terminator) => {
                terminator.format_with_context(syntax, interner)
            },
            HighStatement::If { conditions, else_branch } => {
                let mut code = String::new();
                for (i, conditional) in conditions.iter().enumerate() {
                    if i == 0 {
                        code.push_str("if ");
                    } else {
                        code.push_str(" else if ");
                    }
                    code.push_str(&conditional.condition.format_with_context(syntax, interner));
                    code.push_str(" {\n");
                    for stmt in &conditional.branch {
                        code.push_str("    ");
                        code.push_str(&stmt.format_with_context(syntax, interner));
                        code.push('\n');
                    }
                    code.push_str("}");
                }
                if let Some(else_stmts) = else_branch {
                    code.push_str(" else {\n");
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
impl PrettyPrintWithContext<HighSyntaxLevel> for HighTerminator<HighSyntaxLevel> {
    fn format_with_context(&self, syntax: &Syntax<HighSyntaxLevel>, interner: &ThreadedRodeo) -> String {
        match self {
            HighTerminator::Return(expr) => {
                if let Some(expr) = expr {
                    format!("return {};", expr.format_with_context(syntax, interner))
                } else {
                    "return;".to_string()
                }
            },
            HighTerminator::Break => "break;".to_string(),
            HighTerminator::Continue => "continue;".to_string(),
            HighTerminator::None => "".to_string(),
        }
    }
}

/// Implement PrettyPrint for raw type references
impl PrettyPrint for RawTypeRef {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        let mut code = format_path(&self.path, interner);
        
        if !self.generics.is_empty() {
            code.push('<');
            let generic_strs: Vec<String> = self.generics.iter()
                .map(|g| g.format(interner))
                .collect();
            code.push_str(&generic_strs.join(", "));
            code.push('>');
        }
        
        code
    }
}

/// Implement PrettyPrint for raw function references
impl PrettyPrint for RawFunctionRef {
    fn format(&self, interner: &ThreadedRodeo) -> String {
        let mut code = format_path(&self.path, interner);
        
        if !self.generics.is_empty() {
            code.push('<');
            let generic_strs: Vec<String> = self.generics.iter()
                .map(|g| g.format(interner))
                .collect();
            code.push_str(&generic_strs.join(", "));
            code.push('>');
        }
        
        code
    }
}

/// Helper function to resolve a FunctionRef to its actual name with enhanced resolution
pub fn format_function_ref_with_context(
    func_ref: &FunctionRef, 
    syntax: &Syntax<HighSyntaxLevel>,
    interner: &ThreadedRodeo
) -> String {
    if let Some(func_def) = syntax.functions.get(func_ref.reference) {
        let mut name = interner.resolve(&func_def.name).to_string();
        if !func_ref.generics.is_empty() {
            name.push('<');
            // Use the function's own generics for resolving generic type arguments
            let generic_strs: Vec<String> = func_ref.generics.iter()
                .map(|g| format_generic_type_ref_with_function_context(g, syntax, interner, &func_def.generics))
                .collect();
            name.push_str(&generic_strs.join(", "));
            name.push('>');
        }
        name
    } else {
        format!("func_{}", func_ref.reference)
    }
}