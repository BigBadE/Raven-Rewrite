//! CST → HIR lowering with name resolution

use crate::{ScopeId, ScopeTree, SymbolId, SymbolKind, SymbolTable};
use rv_hir::{
    AssociatedType, AssociatedTypeImpl, Body, DefId, EnumDef, Expr, ExprId, ExternalFunction,
    FieldDef, Function, FunctionId, GenericParam, ImplBlock, ImplId, Item, LiteralKind, LocalId,
    ModuleDef, ModuleId, Parameter, Pattern, PatternId, SelfParam, Stmt, StmtId, StructDef,
    TraitBound, TraitDef, TraitId, TraitMethod, Type, TypeDefId, TypeId, UseItem, VariantDef,
    VariantFields, Visibility, WhereClause,
};
use rv_intern::{Interner, Symbol as InternedString};
use rv_macro::{
    BuiltinMacroKind, MacroDef, MacroExpansionContext, MacroKind,
};
use rv_span::{FileId, FileSpan};
use rv_syntax::{SyntaxKind, SyntaxNode};
use std::collections::HashMap;

/// Context for lowering CST to HIR
pub struct LoweringContext {
    /// String interner
    pub interner: Interner,
    /// Scope tree
    pub scope_tree: ScopeTree,
    /// Symbol table
    pub symbols: SymbolTable,
    /// HIR functions
    pub functions: HashMap<FunctionId, Function>,
    /// External functions
    pub external_functions: HashMap<FunctionId, ExternalFunction>,
    /// Next function ID
    next_function_id: u32,
    /// HIR structs
    pub structs: HashMap<TypeDefId, StructDef>,
    /// Next type def ID
    next_type_id: u32,
    /// HIR enums
    pub enums: HashMap<TypeDefId, EnumDef>,
    /// HIR traits
    pub traits: HashMap<TraitId, TraitDef>,
    /// Next trait ID
    next_trait_id: u32,
    /// HIR impl blocks
    pub impl_blocks: HashMap<ImplId, ImplBlock>,
    /// Next impl block ID
    next_impl_id: u32,
    /// HIR modules
    pub modules: HashMap<ModuleId, ModuleDef>,
    /// Next module ID
    next_module_id: u32,
    /// Map from symbol IDs to `DefIds`
    pub symbol_defs: HashMap<SymbolId, DefId>,
    /// File ID for creating spans
    file_id: FileId,
    /// Type arena
    pub types: rv_arena::Arena<rv_hir::Type>,
    /// Next local ID for pattern bindings
    next_local_id: u32,
    /// Current impl block's self type (for resolving `self` parameters)
    current_impl_self_ty: Option<TypeId>,
    /// Macro expansion context
    pub macro_context: MacroExpansionContext,
}

impl LoweringContext {
    /// Create a new lowering context
    pub fn new() -> Self {
        let interner = Interner::new();
        let mut macro_context = MacroExpansionContext::new(interner.clone());

        // Register builtin macros
        Self::register_builtin_macros(&mut macro_context, &interner);

        Self {
            interner,
            scope_tree: ScopeTree::new(),
            symbols: SymbolTable::new(),
            functions: HashMap::new(),
            external_functions: HashMap::new(),
            next_function_id: 0,
            structs: HashMap::new(),
            next_type_id: 0,
            enums: HashMap::new(),
            traits: HashMap::new(),
            next_trait_id: 0,
            impl_blocks: HashMap::new(),
            next_impl_id: 0,
            modules: HashMap::new(),
            next_module_id: 0,
            symbol_defs: HashMap::new(),
            file_id: FileId(0),
            types: rv_arena::Arena::new(),
            next_local_id: 0,
            current_impl_self_ty: None,
            macro_context,
        }
    }

    /// Register builtin macros
    fn register_builtin_macros(macro_context: &mut MacroExpansionContext, interner: &Interner) {
        let builtins = [
            ("println", BuiltinMacroKind::Println),
            ("vec", BuiltinMacroKind::Vec),
            ("assert", BuiltinMacroKind::Assert),
            ("format", BuiltinMacroKind::Format),
        ];

        for (index, (name, kind)) in builtins.iter().enumerate() {
            macro_context.register_macro(MacroDef {
                id: rv_macro::ast::MacroId(index as u32),
                name: interner.intern(name),
                kind: MacroKind::Builtin { expander: *kind },
                span: FileSpan::new(FileId(0), rv_span::Span::new(0, 0)),
            });
        }
    }

    /// Create file span from syntax node
    fn file_span(&self, node: &SyntaxNode) -> FileSpan {
        FileSpan::new(self.file_id, node.span)
    }

    /// Intern a string
    pub fn intern(&mut self, string: &str) -> InternedString {
        self.interner.intern(string)
    }

    /// Allocate a new function ID
    fn alloc_function_id(&mut self) -> FunctionId {
        let id = FunctionId(self.next_function_id);
        self.next_function_id += 1;
        id
    }

    /// Allocate a new type definition ID
    fn alloc_type_id(&mut self) -> TypeDefId {
        let id = TypeDefId(self.next_type_id);
        self.next_type_id += 1;
        id
    }

    /// Allocate a new impl block ID
    fn alloc_impl_id(&mut self) -> ImplId {
        let id = ImplId(self.next_impl_id);
        self.next_impl_id += 1;
        id
    }

    /// Allocate a new trait ID
    fn alloc_trait_id(&mut self) -> TraitId {
        let id = TraitId(self.next_trait_id);
        self.next_trait_id += 1;
        id
    }

    /// Allocate a new module ID
    fn alloc_module_id(&mut self) -> ModuleId {
        let id = ModuleId(self.next_module_id);
        self.next_module_id += 1;
        id
    }
}

impl Default for LoweringContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Lower a source file to HIR
pub fn lower_source_file(root: &SyntaxNode) -> LoweringContext {
    let mut ctx = LoweringContext::new();

    // Create root scope
    let root_scope = ctx.scope_tree.create_root(root.span);

    // Process all top-level items
    lower_items(&mut ctx, root_scope, &root.children);

    ctx
}

/// Lower multiple items
fn lower_items(ctx: &mut LoweringContext, current_scope: ScopeId, children: &[SyntaxNode]) {
    for child in children {
        match child.kind {
            SyntaxKind::Function => lower_function(ctx, current_scope, child),
            SyntaxKind::Struct => lower_struct(ctx, current_scope, child),
            SyntaxKind::Enum => lower_enum(ctx, current_scope, child),
            SyntaxKind::Impl => lower_impl(ctx, current_scope, child),
            SyntaxKind::Trait => lower_trait(ctx, current_scope, child),
            SyntaxKind::Unknown(ref s) if s == "extern_block" || s == "foreign_mod_item" => {
                lower_extern_block(ctx, current_scope, child);
            }
            SyntaxKind::Unknown(ref s) if s == "mod_item" => {
                lower_module(ctx, current_scope, child);
            }
            SyntaxKind::Unknown(ref s) if s == "use_declaration" => {
                lower_use(ctx, child);
            }
            _ => {}
        }
    }
}

/// Lower a function definition
fn lower_function(ctx: &mut LoweringContext, current_scope: ScopeId, node: &SyntaxNode) {
    // Extract function name from children
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| child.text.clone())
        .unwrap_or_default();

    if name.is_empty() {
        return;
    }

    let name_interned = ctx.intern(&name);
    let file_span = ctx.file_span(node);

    // Add symbol to current scope
    let symbol_id = ctx.symbols.add(
        name_interned,
        SymbolKind::Function,
        node.span,
        current_scope,
    );
    ctx.scope_tree.add_symbol(current_scope, name.clone(), symbol_id);

    // Create function ID and store in symbol
    let function_id = ctx.alloc_function_id();
    let def_id = DefId::Function(function_id);
    ctx.symbols.set_def_id(symbol_id, def_id);
    ctx.symbol_defs.insert(symbol_id, def_id);

    // Parse generic parameters
    let mut generics = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generics = parse_generic_params(ctx, child);
            break;
        }
    }

    // Parse parameters
    let mut parameters = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::Parameters {
            parameters = parse_parameters(ctx, child);
            break;
        }
    }

    // Parse return type (Type node after "->")
    let mut return_type = None;
    let mut found_arrow = false;
    for child in &node.children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "->" {
                found_arrow = true;
                continue;
            }
        }
        if found_arrow && child.kind == SyntaxKind::Type {
            return_type = Some(lower_type_node(ctx, child));
            break;
        }
    }

    // Create function scope for body
    let fn_scope = ctx.scope_tree.create_child(current_scope, node.span);

    // Add parameters to the function scope
    for (param_idx, param) in parameters.iter().enumerate() {
        let param_name_str = ctx.interner.resolve(&param.name).to_string();
        let param_symbol = ctx.symbols.add(
            param.name,
            SymbolKind::Local,
            param.span.span,
            fn_scope,
        );
        ctx.scope_tree.add_symbol(fn_scope, param_name_str.clone(), param_symbol);

        // Create a LocalId for the parameter
        let local_id = rv_hir::LocalId(param_idx as u32);
        let def_id = DefId::Local(local_id);
        ctx.symbols.set_def_id(param_symbol, def_id);
        ctx.symbol_defs.insert(param_symbol, def_id);
    }

    // Lower function body
    let mut body = Body::new();

    // Find the block node
    for child in &node.children {
        if child.kind == SyntaxKind::Block {
            let block_expr = lower_block(ctx, fn_scope, child, &mut body);
            body.root_expr = block_expr;
            break;
        }
    }

    // Create HIR function (without resolution yet)
    let function_temp = Function {
        id: function_id,
        name: name_interned,
        span: file_span,
        generics: generics.clone(),
        parameters: parameters.clone(),
        return_type,
        body,
        is_external: false,
    };

    // Run name resolution on the body
    let resolution_result = rv_resolve::NameResolver::resolve(
        &function_temp.body,
        &function_temp,
        &ctx.interner,
    );

    // Fill in def field for Variable expressions using resolution results
    let mut body_with_resolution = function_temp.body;
    for (expr_id, def_id) in &resolution_result.resolutions {
        if let rv_hir::Expr::Variable { def, .. } = &mut body_with_resolution.exprs[*expr_id] {
            *def = Some(*def_id);
        }
    }

    // Store resolution results in body
    body_with_resolution.resolution = Some(rv_hir::BodyResolution {
        expr_resolutions: resolution_result.resolutions,
        pattern_locals: resolution_result.pattern_locals,
    });

    // Create final function with resolution
    let function = Function {
        id: function_id,
        name: name_interned,
        span: file_span,
        generics,
        parameters,
        return_type: function_temp.return_type,
        body: body_with_resolution,
        is_external: false,
    };

    if ctx.interner.resolve(&name_interned) == "get_value" || ctx.interner.resolve(&name_interned) == "increment" {
    }

    ctx.functions.insert(function_id, function);
}

/// Lower a block expression
fn lower_block(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);
    let block_scope = ctx.scope_tree.create_child(current_scope, node.span);

    let mut statements = vec![];
    let mut trailing_expr = None;

    for child in &node.children {
        match &child.kind {
            SyntaxKind::Let => {
                let stmt_id = lower_let_stmt(ctx, block_scope, child, body);
                statements.push(stmt_id);
            }
            SyntaxKind::Return => {
                let stmt_id = lower_return_stmt(ctx, block_scope, child, body);
                statements.push(stmt_id);
            }
            SyntaxKind::Unknown(name) if name == "expression_statement" => {
                // tree-sitter wraps expressions in expression_statement nodes
                // Extract the actual expression from the first child
                if let Some(expr_child) = child.children.first() {
                    if is_expr_node(expr_child) {
                        let expr_id = lower_expr(ctx, block_scope, expr_child, body);
                        trailing_expr = Some(expr_id);
                    }
                }
            }
            _ => {
                // Try to lower as expression
                if is_expr_node(child) {
                    let expr_id = lower_expr(ctx, block_scope, child, body);
                    trailing_expr = Some(expr_id);
                }
            }
        }
    }

    body.exprs.alloc(Expr::Block {
        statements,
        expr: trailing_expr,
        span: file_span,
    })
}

/// Check if a node represents an expression
fn is_expr_node(node: &SyntaxNode) -> bool {
    matches!(
        node.kind,
        SyntaxKind::Literal
            | SyntaxKind::BinaryOp
            | SyntaxKind::Call
            | SyntaxKind::Block
            | SyntaxKind::If
            | SyntaxKind::Match
            | SyntaxKind::Identifier
    ) || matches!(&node.kind, SyntaxKind::Unknown(name) if name == "field_expression" || name == "struct_expression" || name == "self" || name == "closure_expression")
}

/// Lower an expression
fn lower_expr(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    match node.kind {
        SyntaxKind::Literal => {
            let kind = parse_literal(&node.text);
            body.exprs.alloc(Expr::Literal {
                kind,
                span: file_span,
            })
        }
        SyntaxKind::Identifier => {
            let name = node.text.clone();
            let name_sym = ctx.intern(&name);

            // Try to resolve the name
            let def = ctx.scope_tree.resolve(current_scope, &name);

            body.exprs.alloc(Expr::Variable {
                name: name_sym,
                def: def.and_then(|sym_id| ctx.symbol_defs.get(&sym_id).copied()),
                span: file_span,
            })
        }
        SyntaxKind::BinaryOp => lower_binary_op(ctx, current_scope, node, body),
        SyntaxKind::Block => lower_block(ctx, current_scope, node, body),
        SyntaxKind::If => lower_if_expr(ctx, current_scope, node, body),
        SyntaxKind::Match => lower_match_expr(ctx, current_scope, node, body),
        SyntaxKind::Call => lower_call(ctx, current_scope, node, body),
        SyntaxKind::Unknown(ref name) => match name.as_str() {
            "field_expression" => {
                lower_field_access(ctx, current_scope, node, body)
            }
            "struct_expression" => {
                lower_struct_construct(ctx, current_scope, node, body)
            }
            "closure_expression" => {
                lower_closure(ctx, current_scope, node, body)
            }
            "self" => {
                // `self` is a reference to the first parameter
                let name_sym = ctx.intern("self");
                let def = ctx.scope_tree.resolve(current_scope, "self");

                body.exprs.alloc(Expr::Variable {
                    name: name_sym,
                    def: def.and_then(|sym_id| ctx.symbol_defs.get(&sym_id).copied()),
                    span: file_span,
                })
            }
            _ => body.exprs.alloc(Expr::Literal {
                kind: LiteralKind::Unit,
                span: file_span,
            }),
        },
        _ => {
            // Unknown expression, create unit
            body.exprs.alloc(Expr::Literal {
                kind: LiteralKind::Unit,
                span: file_span,
            })
        }
    }
}

/// Lower function call expression
fn lower_call(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    // Check if this is a method call (callee is a field_expression)
    let mut is_method_call = false;
    let mut receiver = None;
    let mut method_name = None;

    for child in &node.children {
        if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "field_expression") {
            is_method_call = true;

            // Extract receiver and method name from field expression
            for field_child in &child.children {
                if is_expr_node(field_child) && receiver.is_none() {
                    receiver = Some(lower_expr(ctx, current_scope, field_child, body));
                } else if field_child.kind == SyntaxKind::Identifier ||
                          matches!(&field_child.kind, SyntaxKind::Unknown(ref s) if s == "field_identifier") {
                    method_name = Some(ctx.intern(&field_child.text));
                }
            }
            break;
        }
    }

    // Extract arguments
    let mut args = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::Arguments {
            for arg_child in &child.children {
                if is_expr_node(arg_child) {
                    args.push(lower_expr(ctx, current_scope, arg_child, body));
                }
            }
        }
    }

    if is_method_call {
        // This is a method call: receiver.method(args)
        if let (Some(recv), Some(method)) = (receiver, method_name) {
            return body.exprs.alloc(Expr::MethodCall {
                receiver: recv,
                method,
                args,
                span: file_span,
            });
        }
    }

    // Regular function call
    let mut callee = None;
    for child in &node.children {
        if child.kind == SyntaxKind::Identifier && callee.is_none() {
            callee = Some(lower_expr(ctx, current_scope, child, body));
            break;
        }
    }

    if let Some(callee_expr) = callee {
        body.exprs.alloc(Expr::Call {
            callee: callee_expr,
            args,
            span: file_span,
        })
    } else {
        // No callee found, create unit
        body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Unit,
            span: file_span,
        })
    }
}

/// Lower field access expression (e.g., obj.field)
fn lower_field_access(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);
    let mut base = None;
    let mut field_name = None;

    for child in &node.children {
        if is_expr_node(child) && base.is_none() {
            base = Some(lower_expr(ctx, current_scope, child, body));
        } else if child.kind == SyntaxKind::Identifier || matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "field_identifier") {
            field_name = Some(ctx.intern(&child.text));
        }
    }

    if let (Some(base_expr), Some(field)) = (base, field_name) {
        body.exprs.alloc(Expr::Field {
            base: base_expr,
            field,
            span: file_span,
        })
    } else {
        body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Unit,
            span: file_span,
        })
    }
}

/// Lower struct construction expression
fn lower_struct_construct(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);
    let mut struct_name = None;
    let mut fields = vec![];

    for child in &node.children {
        // Check for struct name - can be Identifier or Type
        if (child.kind == SyntaxKind::Identifier || child.kind == SyntaxKind::Type) && struct_name.is_none() {
            struct_name = Some(ctx.intern(&child.text));
        } else if let SyntaxKind::Unknown(name) = &child.kind {
            if name == "field_initializer_list" {
                for field_init in &child.children {
                    if let SyntaxKind::Unknown(init_name) = &field_init.kind {
                        if init_name == "field_initializer" {
                            if let Some((field_name, field_expr)) =
                                parse_field_initializer(ctx, current_scope, field_init, body)
                            {
                                fields.push((field_name, field_expr));
                            }
                        }
                    }
                }
            }
        }
    }


    if let Some(name) = struct_name {
        let def = ctx.scope_tree.resolve(current_scope, &ctx.interner.resolve(&name));
        body.exprs.alloc(Expr::StructConstruct {
            struct_name: name,
            def: def.and_then(|sym_id| {
                ctx.symbol_defs.get(&sym_id).and_then(|def_id| match def_id {
                    DefId::Type(type_id) => Some(*type_id),
                    _ => None,
                })
            }),
            fields,
            span: file_span,
        })
    } else {
        body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Unit,
            span: file_span,
        })
    }
}

/// Parse a field initializer (field: value)
fn parse_field_initializer(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> Option<(InternedString, ExprId)> {
    let mut field_name = None;
    let mut field_value = None;

    for child in &node.children {
        // Field name can be field_identifier
        if (child.kind == SyntaxKind::Identifier || matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "field_identifier")) && field_name.is_none() {
            field_name = Some(ctx.intern(&child.text));
        } else if is_expr_node(child) {
            field_value = Some(lower_expr(ctx, current_scope, child, body));
        }
    }


    if let (Some(name), Some(value)) = (field_name, field_value) {
        Some((name, value))
    } else {
        None
    }
}

/// Parse a literal from text
fn parse_literal(text: &str) -> LiteralKind {
    // Try to parse as integer
    if let Ok(value) = text.parse::<i64>() {
        return LiteralKind::Integer(value);
    }

    // Try to parse as float
    if let Ok(value) = text.parse::<f64>() {
        return LiteralKind::Float(value);
    }

    // Try to parse as boolean
    if text == "true" {
        return LiteralKind::Bool(true);
    }
    if text == "false" {
        return LiteralKind::Bool(false);
    }

    // Try to parse as string (strip quotes)
    if text.starts_with('"') && text.ends_with('"') && text.len() >= 2 {
        return LiteralKind::String(text[1..text.len() - 1].to_string());
    }

    // Default to unit
    LiteralKind::Unit
}

/// Lower a binary operation
fn lower_binary_op(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    // Find left operand, operator, and right operand in children
    let mut left_expr = None;
    let mut operator = None;
    let mut right_expr = None;

    for child in &node.children {
        if is_expression(&child.kind) && left_expr.is_none() {
            left_expr = Some(lower_expr(ctx, current_scope, child, body));
        } else if child.text.len() <= 2 && operator.is_none() {
            // Operators are typically 1-2 characters
            operator = Some(parse_binary_operator(&child.text));
        } else if is_expression(&child.kind) && left_expr.is_some() {
            right_expr = Some(lower_expr(ctx, current_scope, child, body));
        }
    }

    if let (Some(left), Some(op), Some(right)) = (left_expr, operator, right_expr) {
        body.exprs.alloc(Expr::BinaryOp {
            op,
            left,
            right,
            span: file_span,
        })
    } else {
        // Fallback to unit if parsing fails
        body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Unit,
            span: file_span,
        })
    }
}

/// Parse a binary operator from text
fn parse_binary_operator(text: &str) -> rv_hir::BinaryOp {
    use rv_hir::BinaryOp;

    match text {
        "+" => BinaryOp::Add,
        "-" => BinaryOp::Sub,
        "*" => BinaryOp::Mul,
        "/" => BinaryOp::Div,
        "%" => BinaryOp::Mod,
        "==" => BinaryOp::Eq,
        "!=" => BinaryOp::Ne,
        "<" => BinaryOp::Lt,
        "<=" => BinaryOp::Le,
        ">" => BinaryOp::Gt,
        ">=" => BinaryOp::Ge,
        "&&" => BinaryOp::And,
        "||" => BinaryOp::Or,
        "&" => BinaryOp::BitAnd,
        "|" => BinaryOp::BitOr,
        "^" => BinaryOp::BitXor,
        "<<" => BinaryOp::Shl,
        ">>" => BinaryOp::Shr,
        _ => BinaryOp::Add, // Default fallback
    }
}

/// Lower an if expression
fn lower_if_expr(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    let mut condition = None;
    let mut then_branch = None;
    let mut else_branch = None;

    // Parse children to find condition, then block, and optional else block
    let mut found_condition = false;
    let mut found_then = false;

    for child in &node.children {
        if !found_condition && is_expression(&child.kind) {
            condition = Some(lower_expr(ctx, current_scope, child, body));
            found_condition = true;
        } else if found_condition && !found_then && child.kind == SyntaxKind::Block {
            then_branch = Some(lower_expr(ctx, current_scope, child, body));
            found_then = true;
        } else if found_then {
            // Handle else clause which may be wrapped in else_clause node
            match &child.kind {
                SyntaxKind::Block => {
                    else_branch = Some(lower_expr(ctx, current_scope, child, body));
                }
                SyntaxKind::Unknown(name) if name == "else_clause" => {
                    // Extract the block from the else_clause wrapper
                    if let Some(block_child) = child.children.iter().find(|c| c.kind == SyntaxKind::Block) {
                        else_branch = Some(lower_expr(ctx, current_scope, block_child, body));
                    }
                }
                _ => {}
            }
        }
    }

    if let (Some(cond), Some(then_expr)) = (condition, then_branch) {
        body.exprs.alloc(Expr::If {
            condition: cond,
            then_branch: then_expr,
            else_branch,
            span: file_span,
        })
    } else {
        // Fallback
        body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Unit,
            span: file_span,
        })
    }
}

/// Lower a match expression
fn lower_match_expr(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    let mut scrutinee = None;
    let mut arms = Vec::new();

    // First child should be the scrutinee expression
    let mut found_scrutinee = false;

    for child in &node.children {
        if !found_scrutinee && is_expression(&child.kind) {
            scrutinee = Some(lower_expr(ctx, current_scope, child, body));
            found_scrutinee = true;
        } else if found_scrutinee {
            // Check for match_arm or match_block
            if let SyntaxKind::Unknown(ref name) = child.kind {
                if name == "match_arm" {
                    if let Some(arm) = lower_match_arm(ctx, current_scope, child, body) {
                        arms.push(arm);
                    }
                } else if name == "match_block" {
                    // Process all arms within match_block
                    for arm_child in &child.children {
                        if let SyntaxKind::Unknown(ref arm_name) = arm_child.kind {
                            if arm_name == "match_arm" {
                                if let Some(arm) = lower_match_arm(ctx, current_scope, arm_child, body) {
                                    arms.push(arm);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    if let Some(scrutinee_expr) = scrutinee {
        body.exprs.alloc(Expr::Match {
            scrutinee: scrutinee_expr,
            arms,
            span: file_span,
        })
    } else {
        // Fallback to unit
        body.exprs.alloc(Expr::Literal {
            kind: LiteralKind::Unit,
            span: file_span,
        })
    }
}

/// Lower a match arm
fn lower_match_arm(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> Option<rv_hir::MatchArm> {
    let mut pattern = None;
    let guard = None;
    let mut arm_body = None;

    for child in &node.children {
        if pattern.is_none() {
            // First element should be the pattern
            if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                pattern = Some(pat);
            }
        } else if is_expression(&child.kind) {
            // Expression after pattern is the body
            arm_body = Some(lower_expr(ctx, current_scope, child, body));
        }
    }

    if let (Some(pat), Some(body_expr)) = (pattern, arm_body) {
        Some(rv_hir::MatchArm {
            pattern: pat,
            guard,
            body: body_expr,
        })
    } else {
        None
    }
}

/// Lower a pattern
fn lower_pattern(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> Option<PatternId> {
    let file_span = ctx.file_span(node);

    let pattern = match &node.kind {
        // match_pattern is a wrapper node - need to look at children
        SyntaxKind::Unknown(ref name) if name == "match_pattern" => {
            // Look for the actual pattern inside
            for child in &node.children {

                match &child.kind {
                    SyntaxKind::Literal => {
                        let kind = parse_literal(&child.text);
                        return Some(body.patterns.alloc(Pattern::Literal { kind, span: file_span }));
                    }
                    SyntaxKind::Identifier => {
                        let name = child.text.clone();
                        if name == "_" {
                            return Some(body.patterns.alloc(Pattern::Wildcard { span: file_span }));
                        } else {
                            // It's a binding pattern - just store the name
                            let name_sym = ctx.intern(&name);

                            return Some(body.patterns.alloc(Pattern::Binding {
                                name: name_sym,
                                mutable: false,
                                sub_pattern: None,
                                span: file_span,
                            }));
                        }
                    }
                    SyntaxKind::Unknown(ref child_name) if child_name == "_" => {
                        // Wildcard pattern
                        return Some(body.patterns.alloc(Pattern::Wildcard { span: file_span }));
                    }
                    _ => continue,
                }
            }
            // Fallback to wildcard if no pattern found
            Pattern::Wildcard { span: file_span }
        }
        SyntaxKind::Identifier => {
            let name = node.text.clone();

            // Check if this is a wildcard pattern
            if name == "_" {
                Pattern::Wildcard { span: file_span }
            } else {
                // It's a binding pattern - just store the name
                let name_sym = ctx.intern(&name);

                Pattern::Binding {
                    name: name_sym,
                    mutable: false,
                    sub_pattern: None,
                    span: file_span,
                }
            }
        }
        SyntaxKind::Literal => {
            // Parse the literal value
            let kind = parse_literal(&node.text);
            Pattern::Literal { kind, span: file_span }
        }
        SyntaxKind::Unknown(ref name) if name == "tuple_pattern" => {
            // Lower tuple pattern elements
            let mut patterns = Vec::new();
            for child in &node.children {
                // Skip punctuation like '(', ')', ','
                if matches!(child.kind, SyntaxKind::Identifier | SyntaxKind::Literal | SyntaxKind::Unknown(_)) {
                    if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                        patterns.push(pat);
                    }
                }
            }
            Pattern::Tuple { patterns, span: file_span }
        }
        SyntaxKind::Unknown(ref name) if name == "struct_pattern" => {
            // Parse struct pattern: Point { x, y }
            let mut type_name = None;
            let mut field_patterns = Vec::new();

            for child in &node.children {
                if let SyntaxKind::Unknown(ref kind) = child.kind {
                    if kind == "type_identifier" {
                        type_name = Some(child.text.clone());
                    } else if kind == "field_pattern" {
                        // Extract field name from shorthand_field_identifier
                        for field_child in &child.children {
                            if let SyntaxKind::Unknown(ref fkind) = field_child.kind {
                                if fkind == "shorthand_field_identifier" {
                                    let field_name = ctx.intern(&field_child.text);
                                    // Create a binding pattern for the field
                                    let binding_pat = body.patterns.alloc(Pattern::Binding {
                                        name: field_name,
                                        mutable: false,
                                        sub_pattern: None,
                                        span: ctx.file_span(field_child),
                                    });
                                    field_patterns.push((field_name, binding_pat));
                                }
                            }
                        }
                    }
                }
            }

            // Create a type reference for the struct
            if let Some(type_name_str) = type_name {
                let type_sym = ctx.intern(&type_name_str);

                // Look up the struct definition
                let def_id = ctx.structs.iter()
                    .find(|(_, s)| s.name == type_sym)
                    .map(|(id, _)| *id);

                // Create a Named type
                let ty_id = ctx.types.alloc(Type::Named {
                    name: type_sym,
                    def: def_id,
                    args: Vec::new(),
                    span: file_span,
                });

                Pattern::Struct {
                    ty: ty_id,
                    fields: field_patterns,
                    span: file_span,
                }
            } else {
                Pattern::Wildcard { span: file_span }
            }
        }
        SyntaxKind::Unknown(ref name) if name == "tuple_struct_pattern" => {
            // Parse enum/tuple struct pattern: Some(x) or Option::Some(x)
            let mut enum_name = None;
            let mut variant_name = None;
            let mut sub_patterns = Vec::new();

            for child in &node.children {
                match &child.kind {
                    SyntaxKind::Identifier => {
                        // This could be the enum name, variant, or both combined
                        let text = child.text.clone();
                        if text.contains("::") {
                            // Qualified path like Option::Some
                            let parts: Vec<&str> = text.split("::").collect();
                            if parts.len() == 2 {
                                enum_name = Some(parts[0].to_string());
                                variant_name = Some(parts[1].to_string());
                            }
                        } else {
                            // Simple variant name, enum is inferred
                            variant_name = Some(text);
                        }
                    }
                    SyntaxKind::Unknown(ref kind) if kind == "scoped_identifier" => {
                        // Handle Option::Some style
                        for scope_child in &child.children {
                            if let SyntaxKind::Identifier = scope_child.kind {
                                if enum_name.is_none() {
                                    enum_name = Some(scope_child.text.clone());
                                } else {
                                    variant_name = Some(scope_child.text.clone());
                                }
                            }
                        }
                    }
                    _ => {
                        // Try to parse sub-patterns (inside parentheses)
                        if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                            sub_patterns.push(pat);
                        }
                    }
                }
            }

            let variant_sym = variant_name.map(|v| ctx.intern(&v)).unwrap_or_else(|| ctx.intern("_"));
            let enum_sym = enum_name.map(|e| ctx.intern(&e)).unwrap_or_else(|| ctx.intern("_"));

            // Look up the enum definition
            let def_id = ctx.enums.iter()
                .find(|(_, e)| e.name == enum_sym)
                .map(|(id, _)| *id);

            Pattern::Enum {
                enum_name: enum_sym,
                variant: variant_sym,
                def: def_id,
                sub_patterns,
                span: file_span,
            }
        }
        SyntaxKind::Unknown(ref name) if name == "or_pattern" => {
            // Parse or-pattern: pat1 | pat2 | pat3
            let mut patterns = Vec::new();
            for child in &node.children {
                // Skip the '|' separators
                if matches!(child.kind, SyntaxKind::Unknown(_)) || matches!(child.kind, SyntaxKind::Identifier | SyntaxKind::Literal) {
                    if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                        patterns.push(pat);
                    }
                }
            }
            Pattern::Or { patterns, span: file_span }
        }
        SyntaxKind::Unknown(ref name) if name == "range_pattern" => {
            // Parse range pattern: start..end or start..=end
            let mut start = None;
            let mut end = None;
            let mut inclusive = false;

            for child in &node.children {
                if let SyntaxKind::Literal = child.kind {
                    let lit = parse_literal(&child.text);
                    if start.is_none() {
                        start = Some(lit);
                    } else {
                        end = Some(lit);
                    }
                } else if let SyntaxKind::Unknown(ref op) = child.kind {
                    if op == "..=" {
                        inclusive = true;
                    }
                }
            }

            if let (Some(start_lit), Some(end_lit)) = (start, end) {
                Pattern::Range {
                    start: start_lit,
                    end: end_lit,
                    inclusive,
                    span: file_span,
                }
            } else {
                Pattern::Wildcard { span: file_span }
            }
        }
        SyntaxKind::Unknown(ref name) if name == "as_pattern" => {
            // Parse @ pattern: binding @ sub_pattern
            // tree-sitter produces: (as_pattern pattern: <pattern> alias: <identifier>)
            // where pattern is the sub-pattern and alias is the binding name
            let mut binding_name = None;
            let mut sub_pattern_node = None;

            for child in &node.children {
                if child.kind == SyntaxKind::Identifier {
                    // This is the binding name (alias)
                    binding_name = Some(ctx.intern(&child.text));
                } else if matches!(&child.kind, SyntaxKind::Literal | SyntaxKind::Unknown(_)) {
                    // This is the sub-pattern to match against
                    sub_pattern_node = Some(child);
                }
            }

            // Lower the sub-pattern recursively
            let sub_pat_id = sub_pattern_node.and_then(|node| lower_pattern(ctx, current_scope, node, body));

            // Create binding pattern with sub-pattern
            if let Some(name) = binding_name {
                Pattern::Binding {
                    name,
                    mutable: false,
                    sub_pattern: sub_pat_id.map(Box::new),
                    span: file_span,
                }
            } else {
                // Fallback if no binding name found
                Pattern::Wildcard { span: file_span }
            }
        }
        _ => {
            // Unknown pattern type, treat as wildcard
            Pattern::Wildcard { span: file_span }
        }
    };

    Some(body.patterns.alloc(pattern))
}

/// Lower a let statement
fn lower_let_stmt(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> StmtId {
    let file_span = ctx.file_span(node);

    // Extract pattern, initializer, and mutability
    let mut pattern_id = None;
    let mut initializer = None;
    let mut is_mutable = false;

    // Check for 'mut' keyword
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "mut" || s == "mutable_specifier" {
                is_mutable = true;
            }
        }
    }

    for child in &node.children {
        if child.kind == SyntaxKind::Identifier {
            // Simple binding pattern
            let name = child.text.clone();
            let name_sym = ctx.intern(&name);

            // Create symbol for the binding
            let symbol_id = ctx.symbols.add(
                name_sym,
                SymbolKind::Local,
                child.span,
                current_scope,
            );
            ctx.scope_tree.add_symbol(current_scope, name.clone(), symbol_id);

            // Create a local definition for this binding
            let local_id = LocalId(ctx.next_local_id);
            ctx.next_local_id += 1;
            let def_id = DefId::Local(local_id);
            ctx.symbols.set_def_id(symbol_id, def_id);
            ctx.symbol_defs.insert(symbol_id, def_id);

            let pat_file_span = ctx.file_span(child);
            pattern_id = Some(body.patterns.alloc(Pattern::Binding {
                name: name_sym,
                mutable: is_mutable,
                sub_pattern: None,
                span: pat_file_span,
            }));
        } else if is_expr_node(child) {
            initializer = Some(lower_expr(ctx, current_scope, child, body));
        }
    }

    body.stmts.alloc(Stmt::Let {
        pattern: pattern_id.unwrap_or_else(|| {
            body.patterns.alloc(Pattern::Wildcard { span: file_span })
        }),
        ty: None,
        initializer,
        mutable: is_mutable,
        span: file_span,
    })
}

/// Lower a return statement
fn lower_return_stmt(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> StmtId {
    let file_span = ctx.file_span(node);

    let mut value = None;
    for child in &node.children {
        if is_expr_node(child) {
            value = Some(lower_expr(ctx, current_scope, child, body));
            break;
        }
    }

    body.stmts.alloc(Stmt::Return {
        value,
        span: file_span,
    })
}

/// Check if a syntax kind represents an expression
fn is_expression(kind: &SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Literal
            | SyntaxKind::BinaryOp
            | SyntaxKind::Call
            | SyntaxKind::Block
            | SyntaxKind::If
            | SyntaxKind::Match
            | SyntaxKind::Identifier
    )
}

/// Lower a struct definition
fn lower_struct(ctx: &mut LoweringContext, current_scope: ScopeId, node: &SyntaxNode) {
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier || child.kind == SyntaxKind::Type)
        .map(|child| child.text.clone())
        .unwrap_or_default();

    if name.is_empty() {
        return;
    }

    let name_interned = ctx.intern(&name);
    let file_span = ctx.file_span(node);

    let symbol_id = ctx.symbols.add(
        name_interned,
        SymbolKind::Function,
        node.span,
        current_scope,
    );
    ctx.scope_tree
        .add_symbol(current_scope, name.clone(), symbol_id);

    let type_id = ctx.alloc_type_id();
    let def_id = DefId::Type(type_id);
    ctx.symbols.set_def_id(symbol_id, def_id);
    ctx.symbol_defs.insert(symbol_id, def_id);

    // Parse fields - look for field_declaration_list or similar
    let mut fields = vec![];
    for child in &node.children {
        if let SyntaxKind::Unknown(child_name) = &child.kind {
            if child_name == "field_declaration_list" {
                for field_node in &child.children {
                    if let SyntaxKind::Unknown(field_kind) = &field_node.kind {
                        if field_kind == "field_declaration" {
                            if let Some(field) = parse_field(ctx, field_node) {
                                fields.push(field);
                            }
                        }
                    }
                }
            }
        }
    }

    let struct_def = StructDef {
        id: type_id,
        name: name_interned,
        generic_params: vec![],
        fields,
        span: file_span,
    };

    ctx.structs.insert(type_id, struct_def);
}

/// Parse a field declaration
fn parse_field(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<FieldDef> {
    let mut field_name = None;
    let mut field_ty = None;

    for child in &node.children {
        // Field name can be Identifier or field_identifier
        if (child.kind == SyntaxKind::Identifier || matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "field_identifier"))
            && field_name.is_none() {
            field_name = Some(ctx.intern(&child.text));
        } else if child.kind == SyntaxKind::Type {
            // Actually parse the type instead of using a placeholder
            field_ty = Some(lower_type_node(ctx, child));
        }
    }

    if let (Some(name), Some(ty)) = (field_name, field_ty) {
        Some(FieldDef {
            name,
            ty,
            visibility: Visibility::Public,
            span: ctx.file_span(node),
        })
    } else {
        None
    }
}

/// Lower an enum definition
fn lower_enum(ctx: &mut LoweringContext, current_scope: ScopeId, node: &SyntaxNode) {
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| child.text.clone())
        .unwrap_or_default();

    if name.is_empty() {
        return;
    }

    let name_interned = ctx.intern(&name);
    let file_span = ctx.file_span(node);

    let symbol_id = ctx.symbols.add(
        name_interned,
        SymbolKind::Function,
        node.span,
        current_scope,
    );
    ctx.scope_tree
        .add_symbol(current_scope, name.clone(), symbol_id);

    let type_id = ctx.alloc_type_id();
    let def_id = DefId::Type(type_id);
    ctx.symbols.set_def_id(symbol_id, def_id);
    ctx.symbol_defs.insert(symbol_id, def_id);

    // Parse variants
    let mut variants = vec![];
    for child in &node.children {
        if let SyntaxKind::Unknown(name) = &child.kind {
            if name == "enum_variant_list" || name == "enum_variant" {
                for variant_node in &child.children {
                    if let Some(variant) = parse_variant(ctx, variant_node) {
                        variants.push(variant);
                    }
                }
            }
        }
    }

    let enum_def = EnumDef {
        id: type_id,
        name: name_interned,
        generic_params: vec![],
        variants,
        span: file_span,
    };

    ctx.enums.insert(type_id, enum_def);
}

/// Parse an enum variant
fn parse_variant(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<VariantDef> {
    if node.kind != SyntaxKind::Identifier {
        return None;
    }

    let name = ctx.intern(&node.text);
    Some(VariantDef {
        name,
        fields: VariantFields::Unit,
        span: ctx.file_span(node),
    })
}

/// Parse generic parameters from a GenericParams node
fn parse_generic_params(ctx: &mut LoweringContext, node: &SyntaxNode) -> Vec<GenericParam> {
    let mut params = vec![];

    for child in &node.children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "type_parameter" {
                // Extract the type name from the type_parameter node
                for type_child in &child.children {
                    if type_child.kind == SyntaxKind::Type {
                        let name = ctx.intern(&type_child.text);
                        params.push(GenericParam {
                            name,
                            bounds: vec![],
                            span: ctx.file_span(type_child),
                        });
                        break;
                    }
                }
            }
        }
    }

    params
}

/// Parse function parameters from a Parameters node
fn parse_parameters(ctx: &mut LoweringContext, node: &SyntaxNode) -> Vec<Parameter> {
    let mut params = vec![];


    // WORKAROUND: Tree-sitter doesn't always create child nodes for simple "self" parameters
    // Check if the node text contains "self" directly
    if node.text.contains("self") && !node.text.contains(":") {
        // Simple self parameter without type annotation (e.g., "(self)")
        // Use the impl block's self type
        if let Some(self_ty) = ctx.current_impl_self_ty {
            let name_sym = ctx.intern("self");
            params.push(Parameter {
                inferred_ty: None,
                name: name_sym,
                ty: self_ty,
                span: ctx.file_span(node),
            });
            return params; // Early return - we found the self parameter
        }
    }

    for child in &node.children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "self_parameter" {
                // Self parameter (e.g., `self` or `self: Type`)
                let name_sym = ctx.intern("self");

                // Try to find a type annotation for self (self: Type)
                let mut param_type_id = None;
                for param_child in &child.children {
                    if param_child.kind == SyntaxKind::Type {
                        param_type_id = Some(lower_type_node(ctx, param_child));
                    }
                }

                // If no type annotation, use the impl block's self type
                if param_type_id.is_none() {
                    param_type_id = ctx.current_impl_self_ty;
                }

                if let Some(type_id) = param_type_id {
                    params.push(Parameter {
                inferred_ty: None,
                        name: name_sym,
                        ty: type_id,
                        span: ctx.file_span(child),
                    });
                }
            } else if kind == "parameter" {
                // Extract parameter name and type
                // Structure: Identifier, ":", Type
                let mut param_name = None;
                let mut param_type_id = None;

                for param_child in &child.children {
                    match &param_child.kind {
                        SyntaxKind::Identifier => {
                            param_name = Some(ctx.intern(&param_child.text));
                        }
                        SyntaxKind::Unknown(ref s) if s == "self" => {
                            param_name = Some(ctx.intern("self"));
                        }
                        SyntaxKind::Type => {
                            param_type_id = Some(lower_type_node(ctx, param_child));
                        }
                        _ => {}
                    }
                }

                // Handle `self` parameter without type annotation
                if let Some(name) = param_name {
                    if ctx.interner.resolve(&name) == "self" && param_type_id.is_none() {
                        // Use the impl block's self type
                        param_type_id = ctx.current_impl_self_ty;
                    }
                }

                if let (Some(name), Some(type_id)) = (param_name, param_type_id) {
                    params.push(Parameter {
                        name,
                        ty: type_id,
                        inferred_ty: None,
                        span: ctx.file_span(child),
                    });
                }
            }
        }
    }

    params
}

/// Lower a Type syntax node to HIR `TypeId`
fn lower_type_node(ctx: &mut LoweringContext, node: &SyntaxNode) -> TypeId {
    let name = ctx.intern(&node.text);
    let span = ctx.file_span(node);

    // Try to resolve the type name to a TypeDefId
    let def = ctx.structs.iter()
        .find(|(_, s)| s.name == name)
        .map(|(id, _)| *id)
        .or_else(|| {
            ctx.enums.iter()
                .find(|(_, e)| e.name == name)
                .map(|(id, _)| *id)
        });

    // Create a Type and allocate it in the type arena
    let type_node = Type::Named {
        name,
        def,
        args: vec![],
        span,
    };

    ctx.types.alloc(type_node)
}

/// Lower an impl block
fn lower_impl(ctx: &mut LoweringContext, current_scope: ScopeId, node: &SyntaxNode) {
    // Check for "impl Trait for Type" pattern by looking for "for" keyword
    let mut trait_ref = None;
    let mut self_ty_node = None;

    // Search for trait name (identifier before "for") and type after "for"
    let mut found_for = false;
    for child in &node.children {
        if child.kind == SyntaxKind::Identifier && !found_for {
            // This might be a trait name
            let trait_name = ctx.intern(&child.text);
            // Look up trait by name
            for (trait_id, trait_def) in &ctx.traits {
                if trait_def.name == trait_name {
                    trait_ref = Some(*trait_id);
                    break;
                }
            }
        } else if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "for" {
                found_for = true;
            }
        } else if child.kind == SyntaxKind::Type {
            if found_for || trait_ref.is_none() {
                // This is the self type
                self_ty_node = Some(child);
            }
        }
    }

    // Extract the type being implemented for
    let self_ty = self_ty_node
        .map(|child| lower_type_node(ctx, child))
        .unwrap_or_else(|| {
            // Create an Unknown type as fallback
            ctx.types.alloc(Type::Unknown {
                span: ctx.file_span(node),
            })
        });

    let impl_id = ctx.alloc_impl_id();
    let file_span = ctx.file_span(node);

    // Parse generic parameters if present
    let mut generic_params = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generic_params = parse_generic_params(ctx, child)
                .into_iter()
                .map(|p| p.name)
                .collect();
            break;
        }
    }

    // Create a scope for the impl block
    let impl_scope = ctx.scope_tree.create_child(current_scope, node.span);

    // Set the current impl self type for method lowering
    let prev_impl_self_ty = ctx.current_impl_self_ty;
    ctx.current_impl_self_ty = Some(self_ty);

    // Parse methods and associated type implementations in the impl block
    let mut methods = vec![];
    let mut associated_type_impls = vec![];
    for child in &node.children {
        let is_decl_list = if let SyntaxKind::Unknown(ref s) = child.kind {
            s == "declaration_list"
        } else {
            false
        };
        if child.kind == SyntaxKind::Block || is_decl_list {
            // The impl block body contains function definitions and type implementations
            for item in &child.children {
                if item.kind == SyntaxKind::Function {
                    // Get the current number of functions to track the new one
                    let func_count_before = ctx.functions.len();

                    // Lower the method function
                    lower_function(ctx, impl_scope, item);

                    // The newly created function should be the last one added
                    // Find it in the functions map
                    if ctx.functions.len() > func_count_before {
                        // Get the last added function ID by finding the highest ID
                        if let Some((&func_id, _)) = ctx.functions.iter().max_by_key(|(id, _)| id.0) {
                            methods.push(func_id);
                        }
                    }
                } else if let SyntaxKind::Unknown(ref s) = item.kind {
                    // Parse associated type implementation (type Foo = Bar;)
                    if s == "type_item" {
                        if let Some(assoc_impl) = parse_associated_type_impl(ctx, item) {
                            associated_type_impls.push(assoc_impl);
                        }
                    }
                }
            }
        }
    }

    // Restore the previous impl self type
    ctx.current_impl_self_ty = prev_impl_self_ty;

    // Parse where clauses
    let where_clauses = parse_where_clauses(ctx, node);

    // Create and store the impl block
    let impl_block = ImplBlock {
        id: impl_id,
        self_ty,
        trait_ref,
        generic_params,
        methods,
        associated_type_impls,
        where_clauses,
        span: file_span,
    };

    ctx.impl_blocks.insert(impl_id, impl_block);
}

/// Lower a trait definition
fn lower_trait(ctx: &mut LoweringContext, current_scope: ScopeId, node: &SyntaxNode) {
    // Extract trait name
    let trait_name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| ctx.intern(&child.text))
        .unwrap_or_else(|| ctx.intern("_"));

    let trait_id = ctx.alloc_trait_id();
    let file_span = ctx.file_span(node);

    // Parse generic parameters if present
    let mut generic_params = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generic_params = parse_generic_params(ctx, child)
                .into_iter()
                .map(|p| p.name)
                .collect();
            break;
        }
    }

    // Create a scope for the trait
    let trait_scope = ctx.scope_tree.create_child(current_scope, node.span);

    // Parse supertraits (trait Foo: Bar + Baz)
    let mut supertraits = vec![];
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "trait_bounds" {
                // Parse each supertrait
                for bound_child in &child.children {
                    if bound_child.kind == SyntaxKind::Identifier {
                        let trait_name = ctx.intern(&bound_child.text);
                        // Look up the trait by name
                        for (tid, tdef) in &ctx.traits {
                            if tdef.name == trait_name {
                                supertraits.push(TraitBound {
                                    trait_ref: *tid,
                                    args: vec![],
                                });
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    // Parse trait methods and associated types
    let mut methods = vec![];
    let mut associated_types = vec![];
    for child in &node.children {
        let is_decl_list = if let SyntaxKind::Unknown(ref s) = child.kind {
            s == "declaration_list"
        } else {
            false
        };
        if child.kind == SyntaxKind::Block || is_decl_list {
            // The trait block body contains method signatures and associated types
            for item in &child.children {
                if item.kind == SyntaxKind::Function {
                    // Parse method signature
                    if let Some(method) = lower_trait_method(ctx, trait_scope, item) {
                        methods.push(method);
                    }
                } else if let SyntaxKind::Unknown(ref s) = item.kind {
                    if s == "type_item" {
                        // Parse associated type: type Foo;
                        if let Some(assoc_ty) = parse_associated_type(ctx, item) {
                            associated_types.push(assoc_ty);
                        }
                    }
                }
            }
        }
    }

    // Create and store the trait definition
    let trait_def = TraitDef {
        id: trait_id,
        name: trait_name,
        generic_params,
        methods,
        associated_types,
        supertraits,
        span: file_span,
    };

    ctx.traits.insert(trait_id, trait_def);
}

/// Parse an associated type declaration
fn parse_associated_type(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<AssociatedType> {
    // Extract type name
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| ctx.intern(&child.text))?;

    let span = ctx.file_span(node);

    // Parse trait bounds if present (type Foo: Trait1 + Trait2)
    let mut bounds = vec![];
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "trait_bounds" {
                for bound_child in &child.children {
                    if bound_child.kind == SyntaxKind::Identifier {
                        let trait_name = ctx.intern(&bound_child.text);
                        // Look up trait by name
                        for (tid, tdef) in &ctx.traits {
                            if tdef.name == trait_name {
                                bounds.push(TraitBound {
                                    trait_ref: *tid,
                                    args: vec![],
                                });
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    Some(AssociatedType { name, bounds, span })
}

/// Parse an associated type implementation (type Foo = Bar;)
fn parse_associated_type_impl(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<AssociatedTypeImpl> {
    // Extract type name (left side of =)
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| ctx.intern(&child.text))?;

    // Extract concrete type (right side of =)
    let ty = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Type)
        .map(|child| lower_type_node(ctx, child))?;

    let span = ctx.file_span(node);

    Some(AssociatedTypeImpl { name, ty, span })
}

/// Parse where clauses (where T: Trait1 + Trait2, U: Trait3)
fn parse_where_clauses(ctx: &mut LoweringContext, node: &SyntaxNode) -> Vec<WhereClause> {
    let mut where_clauses = vec![];

    // Look for where_clause node
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "where_clause" {
                // Parse each where predicate (T: Trait1 + Trait2)
                for predicate in &child.children {
                    if let SyntaxKind::Unknown(ref pred_kind) = predicate.kind {
                        if pred_kind == "where_predicate" {
                            // Extract the type being constrained
                            let ty_opt = predicate
                                .children
                                .iter()
                                .find(|c| c.kind == SyntaxKind::Type)
                                .map(|c| lower_type_node(ctx, c));

                            if let Some(ty) = ty_opt {
                                // Parse trait bounds
                                let mut bounds = vec![];
                                for bound_node in &predicate.children {
                                    if let SyntaxKind::Unknown(ref bound_kind) = bound_node.kind {
                                        if bound_kind == "trait_bounds" {
                                            for trait_node in &bound_node.children {
                                                if trait_node.kind == SyntaxKind::Identifier {
                                                    let trait_name = ctx.intern(&trait_node.text);
                                                    // Look up trait by name
                                                    for (tid, tdef) in &ctx.traits {
                                                        if tdef.name == trait_name {
                                                            bounds.push(TraitBound {
                                                                trait_ref: *tid,
                                                                args: vec![],
                                                            });
                                                            break;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }

                                where_clauses.push(WhereClause { ty, bounds });
                            }
                        }
                    }
                }
            }
        }
    }

    where_clauses
}

/// Lower a trait method signature
fn lower_trait_method(
    ctx: &mut LoweringContext,
    _scope: ScopeId,
    node: &SyntaxNode,
) -> Option<TraitMethod> {
    // Extract method name
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| ctx.intern(&child.text))?;

    let file_span = ctx.file_span(node);

    // Parse generic parameters
    let mut generics = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generics = parse_generic_params(ctx, child);
            break;
        }
    }

    // Parse self parameter and regular parameters
    let mut self_param = None;
    let mut params = vec![];

    for child in &node.children {
        if child.kind == SyntaxKind::Parameters {
            for param_child in &child.children {
                // Check if this is a self parameter
                if let SyntaxKind::Unknown(ref kind) = param_child.kind {
                    if kind == "self_parameter" {
                        // Parse self parameter text to determine type
                        let param_text = param_child.text.trim();
                        if param_text.contains("&mut") {
                            self_param = Some(SelfParam::MutRef);
                        } else if param_text.contains('&') {
                            self_param = Some(SelfParam::Ref);
                        } else {
                            self_param = Some(SelfParam::Value);
                        }
                    } else if kind == "parameter" {
                        // Regular parameter
                        let param_name = param_child
                            .children
                            .iter()
                            .find(|c| c.kind == SyntaxKind::Identifier)
                            .map(|c| ctx.intern(&c.text))
                            .unwrap_or_else(|| ctx.intern("_"));

                        let param_ty = param_child
                            .children
                            .iter()
                            .find(|c| c.kind == SyntaxKind::Type)
                            .map(|c| lower_type_node(ctx, c))
                            .unwrap_or_else(|| {
                                ctx.types.alloc(Type::Unknown {
                                    span: ctx.file_span(param_child),
                                })
                            });

                        params.push(Parameter {
                            name: param_name,
                            ty: param_ty,
                            inferred_ty: None,
                            span: ctx.file_span(param_child),
                        });
                    }
                } else if param_child.kind == SyntaxKind::Identifier && param_child.text == "self" {
                    // Simple self parameter
                    self_param = Some(SelfParam::Value);
                }
            }
        }
    }

    // Parse return type
    let return_type = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Type)
        .map(|child| lower_type_node(ctx, child));

    Some(TraitMethod {
        name,
        generics,
        params,
        return_type,
        self_param,
        span: file_span,
    })
}

/// Lower an extern block (external function declarations)
fn lower_extern_block(ctx: &mut LoweringContext, _current_scope: ScopeId, node: &SyntaxNode) {
    // Extract ABI string if present (extern "C", extern "Rust", etc.)
    let mut abi = None;
    for child in &node.children {
        // Look for string literal node (tree-sitter uses "string_literal")
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "string_literal" {
                // Extract the ABI string (remove quotes)
                let abi_str = child.text.trim_matches('"');
                abi = Some(abi_str.to_string());
                break;
            }
        }
    }

    // Process function declarations inside the extern block
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "declaration_list" {
                for item in &child.children {
                    if let SyntaxKind::Unknown(ref item_kind) = item.kind {
                        if item_kind == "function_signature_item" || item.kind == SyntaxKind::Function {
                            lower_external_function(ctx, item, abi.clone());
                        }
                    }
                }
            }
        }
    }
}

/// Lower an external function declaration
fn lower_external_function(ctx: &mut LoweringContext, node: &SyntaxNode, abi: Option<String>) {
    // Extract function name
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| ctx.intern(&child.text))
        .unwrap_or_else(|| ctx.intern("_"));

    let func_id = ctx.alloc_function_id();
    let span = ctx.file_span(node);

    // Parse parameters
    let parameters = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Parameters)
        .map(|params_node| parse_parameters(ctx, params_node))
        .unwrap_or_default();

    // Parse return type
    let return_type = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Type)
        .map(|child| lower_type_node(ctx, child));

    // Generate mangled name for Rust ABI or use unmangled for C ABI
    // For C ABI, we store the unmangled name
    // For Rust ABI, we store the mangled name
    let name_str = ctx.interner.resolve(&name);
    let mangled_name = if abi.as_deref() == Some("C") || abi.is_none() {
        // C ABI uses unmangled names - store the original name
        Some(name_str)
    } else {
        // Rust ABI requires name mangling
        Some(mangle_rust_v0(name, &ctx.interner))
    };

    let external_fn = ExternalFunction {
        id: func_id,
        name,
        mangled_name,
        parameters,
        return_type,
        abi,
        span,
    };

    ctx.external_functions.insert(func_id, external_fn);
}

/// Lower a closure expression
fn lower_closure(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    // Parse closure parameters from closure_parameters node: |x, y|
    let mut params = vec![];
    for child in &node.children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "closure_parameters" {
                // Extract parameters from inside the pipes
                for param_child in &child.children {
                    if param_child.kind == SyntaxKind::Identifier {
                        let param_name = ctx.intern(&param_child.text);
                        // Create a TypeId for Unknown type (will be inferred)
                        let param_ty = ctx.types.alloc(Type::Unknown {
                            span: ctx.file_span(param_child),
                        });
                        params.push(Parameter {
                            name: param_name,
                            ty: param_ty,
                            inferred_ty: None,
                            span: ctx.file_span(param_child),
                        });
                    }
                }
            }
        }
    }

    // Parse return type annotation if present (-> Type)
    let mut return_type = None;
    let mut found_arrow = false;
    for child in &node.children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "->" {
                found_arrow = true;
                continue;
            }
        }
        if found_arrow && child.kind == SyntaxKind::Type {
            return_type = Some(lower_type_node(ctx, child));
            break;
        }
    }

    // Create a new scope for the closure body
    let closure_scope = ctx.scope_tree.create_child(current_scope, node.span);

    // Add parameters to closure scope
    for param in &params {
        let param_name_str = ctx.interner.resolve(&param.name).to_string();
        let param_symbol = ctx.symbols.add(
            param.name,
            SymbolKind::Local,
            param.span.span,
            closure_scope,
        );
        ctx.scope_tree.add_symbol(closure_scope, param_name_str, param_symbol);
    }

    // Find and lower the closure body expression
    let body_expr = find_closure_body(ctx, closure_scope, node, body);

    // Analyze captures: find all free variables in the body
    let captures = analyze_captures(ctx, closure_scope, current_scope, body, body_expr);

    body.exprs.alloc(Expr::Closure {
        params,
        return_type,
        body: body_expr,
        captures,
        span: file_span,
    })
}

/// Find the body expression in a closure node
fn find_closure_body(
    ctx: &mut LoweringContext,
    closure_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    // The body can be either a block or a single expression
    for child in &node.children {
        if child.kind == SyntaxKind::Block {
            // Block body: |x| { x + 1 }
            return lower_block(ctx, closure_scope, child, body);
        } else if is_expr_node(child) {
            // Expression body: |x| x + 1
            return lower_expr(ctx, closure_scope, child, body);
        }
    }

    // Fallback to unit if no body found
    let file_span = ctx.file_span(node);
    body.exprs.alloc(Expr::Literal {
        kind: LiteralKind::Unit,
        span: file_span,
    })
}

/// Analyze captures for a closure body
///
/// Returns a vector of variables that are:
/// - Referenced in the closure body
/// - Not defined in the closure's parameter list
/// - Defined in an outer scope (free variables)
fn analyze_captures(
    ctx: &LoweringContext,
    closure_scope: ScopeId,
    parent_scope: ScopeId,
    body: &Body,
    body_expr: ExprId,
) -> Vec<rv_intern::Symbol> {
    let mut captures = std::collections::HashSet::new();
    collect_free_vars(ctx, closure_scope, parent_scope, body, body_expr, &mut captures);
    captures.into_iter().collect()
}

/// Recursively collect free variables from an expression
fn collect_free_vars(
    ctx: &LoweringContext,
    closure_scope: ScopeId,
    parent_scope: ScopeId,
    body: &Body,
    expr_id: ExprId,
    captures: &mut std::collections::HashSet<rv_intern::Symbol>,
) {
    let expr = &body.exprs[expr_id];

    match expr {
        Expr::Variable { name, .. } => {
            // Check if this variable is defined in the closure scope
            let local_def = ctx.scope_tree.resolve(closure_scope, &ctx.interner.resolve(name));
            // Check if this variable is defined in parent scope (captured)
            let parent_def = ctx.scope_tree.resolve(parent_scope, &ctx.interner.resolve(name));

            // Variable is captured if:
            // - Not defined locally in closure
            // - Defined in parent scope
            if local_def.is_none() && parent_def.is_some() {
                captures.insert(*name);
            }
        }
        Expr::BinaryOp { left, right, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *left, captures);
            collect_free_vars(ctx, closure_scope, parent_scope, body, *right, captures);
        }
        Expr::UnaryOp { operand, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *operand, captures);
        }
        Expr::Call { callee, args, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *callee, captures);
            for arg in args {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *arg, captures);
            }
        }
        Expr::Block { statements, expr, .. } => {
            // Collect from statements
            for stmt_id in statements {
                collect_free_vars_stmt(ctx, closure_scope, parent_scope, body, *stmt_id, captures);
            }
            // Collect from trailing expression
            if let Some(trailing) = expr {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *trailing, captures);
            }
        }
        Expr::If { condition, then_branch, else_branch, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *condition, captures);
            collect_free_vars(ctx, closure_scope, parent_scope, body, *then_branch, captures);
            if let Some(else_expr) = else_branch {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *else_expr, captures);
            }
        }
        Expr::Match { scrutinee, arms, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *scrutinee, captures);
            for arm in arms {
                collect_free_vars(ctx, closure_scope, parent_scope, body, arm.body, captures);
            }
        }
        Expr::Field { base, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *base, captures);
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *receiver, captures);
            for arg in args {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *arg, captures);
            }
        }
        Expr::StructConstruct { fields, .. } => {
            for (_, field_expr) in fields {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *field_expr, captures);
            }
        }
        Expr::EnumVariant { fields, .. } => {
            for field_expr in fields {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *field_expr, captures);
            }
        }
        Expr::Closure { body: closure_body, .. } => {
            // Recursively analyze nested closures
            collect_free_vars(ctx, closure_scope, parent_scope, body, *closure_body, captures);
        }
        Expr::Literal { .. } => {
            // Literals don't capture variables
        }
    }
}

/// Collect free variables from a statement
fn collect_free_vars_stmt(
    ctx: &LoweringContext,
    closure_scope: ScopeId,
    parent_scope: ScopeId,
    body: &Body,
    stmt_id: StmtId,
    captures: &mut std::collections::HashSet<rv_intern::Symbol>,
) {
    let stmt = &body.stmts[stmt_id];

    match stmt {
        Stmt::Let { initializer, .. } => {
            if let Some(init_expr) = initializer {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *init_expr, captures);
            }
        }
        Stmt::Expr { expr, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *expr, captures);
        }
        Stmt::Return { value, .. } => {
            if let Some(val_expr) = value {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *val_expr, captures);
            }
        }
    }
}

/// Lower a module declaration
fn lower_module(ctx: &mut LoweringContext, current_scope: ScopeId, node: &SyntaxNode) -> ModuleDef {
    // Extract module name
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| ctx.intern(&child.text))
        .unwrap_or_else(|| ctx.intern("_"));

    let module_id = ctx.alloc_module_id();
    let file_span = ctx.file_span(node);

    // Extract visibility (pub or private)
    let visibility = extract_visibility(node);

    // Create a scope for the module
    let module_scope = ctx.scope_tree.create_child(current_scope, node.span);

    // Add module symbol to parent scope
    let symbol_id = ctx.symbols.add(
        name,
        SymbolKind::Function, // Using Function as a placeholder since we don't have SymbolKind::Module
        node.span,
        current_scope,
    );
    ctx.scope_tree.add_symbol(current_scope, ctx.interner.resolve(&name).to_string(), symbol_id);
    let def_id = DefId::Module(module_id);
    ctx.symbols.set_def_id(symbol_id, def_id);
    ctx.symbol_defs.insert(symbol_id, def_id);

    // Parse module body
    let mut items = Vec::new();
    let mut submodules = Vec::new();

    for child in &node.children {
        let is_block = matches!(child.kind, SyntaxKind::Block);
        let is_decl_list = if let SyntaxKind::Unknown(ref s) = child.kind {
            s == "declaration_list"
        } else {
            false
        };

        if is_block || is_decl_list {
            // Module body contains items
            for item_node in &child.children {
                    match item_node.kind {
                        SyntaxKind::Function => {
                            // Get function count before lowering
                            let func_count_before = ctx.functions.len();
                            lower_function(ctx, module_scope, item_node);
                            // Find the newly added function
                            if ctx.functions.len() > func_count_before {
                                if let Some((&func_id, _)) = ctx.functions.iter().max_by_key(|(id, _)| id.0) {
                                    items.push(Item::Function(func_id));
                                }
                            }
                        }
                        SyntaxKind::Struct => {
                            let struct_count_before = ctx.structs.len();
                            lower_struct(ctx, module_scope, item_node);
                            if ctx.structs.len() > struct_count_before {
                                if let Some((&type_id, _)) = ctx.structs.iter().max_by_key(|(id, _)| id.0) {
                                    items.push(Item::Struct(type_id));
                                }
                            }
                        }
                        SyntaxKind::Enum => {
                            let enum_count_before = ctx.enums.len();
                            lower_enum(ctx, module_scope, item_node);
                            if ctx.enums.len() > enum_count_before {
                                if let Some((&type_id, _)) = ctx.enums.iter().max_by_key(|(id, _)| id.0) {
                                    items.push(Item::Enum(type_id));
                                }
                            }
                        }
                        SyntaxKind::Trait => {
                            let trait_count_before = ctx.traits.len();
                            lower_trait(ctx, module_scope, item_node);
                            if ctx.traits.len() > trait_count_before {
                                if let Some((&trait_id, _)) = ctx.traits.iter().max_by_key(|(id, _)| id.0) {
                                    items.push(Item::Trait(trait_id));
                                }
                            }
                        }
                        SyntaxKind::Impl => {
                            let impl_count_before = ctx.impl_blocks.len();
                            lower_impl(ctx, module_scope, item_node);
                            if ctx.impl_blocks.len() > impl_count_before {
                                if let Some((&impl_id, _)) = ctx.impl_blocks.iter().max_by_key(|(id, _)| id.0) {
                                    items.push(Item::Impl(impl_id));
                                }
                            }
                        }
                        SyntaxKind::Unknown(ref s) if s == "mod_item" => {
                            // Nested module
                            let submodule = lower_module(ctx, module_scope, item_node);
                            submodules.push(submodule.id);
                            items.push(Item::Module(submodule.id));
                        }
                        SyntaxKind::Unknown(ref s) if s == "use_declaration" => {
                            // Use declaration
                            if let Some(use_item) = lower_use(ctx, item_node) {
                                items.push(Item::Use(use_item));
                            }
                        }
                        _ => {}
                    }
                }
        }
    }

    let module_def = ModuleDef {
        id: module_id,
        name,
        items,
        submodules,
        visibility,
        span: file_span,
    };

    ctx.modules.insert(module_id, module_def.clone());
    module_def
}

/// Lower a use declaration (import)
fn lower_use(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<UseItem> {
    let file_span = ctx.file_span(node);
    let visibility = extract_visibility(node);

    // Extract the use path
    let path = extract_use_path(ctx, node)?;

    // Extract optional alias (as Name)
    let alias = extract_use_alias(ctx, node);

    Some(UseItem {
        path,
        alias,
        visibility,
        span: file_span,
    })
}

/// Extract use path from a use declaration node
fn extract_use_path(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<Vec<InternedString>> {
    // Look for the argument/path in the use declaration
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            // tree-sitter represents paths as scoped_identifier or identifier
            if s == "scoped_identifier" || s == "scoped_use_list" {
                let mut path = Vec::new();
                extract_path_segments(ctx, child, &mut path);
                if !path.is_empty() {
                    return Some(path);
                }
            }
        } else if child.kind == SyntaxKind::Identifier {
            // Simple single-segment path
            return Some(vec![ctx.intern(&child.text)]);
        }
    }
    None
}

/// Extract path segments recursively from a scoped identifier
fn extract_path_segments(ctx: &mut LoweringContext, node: &SyntaxNode, path: &mut Vec<InternedString>) {
    match &node.kind {
        SyntaxKind::Identifier => {
            path.push(ctx.intern(&node.text));
        }
        SyntaxKind::Unknown(ref s) if s == "scoped_identifier" => {
            // Process path (left side) first
            for child in &node.children {
                if let SyntaxKind::Unknown(ref child_s) = child.kind {
                    if child_s == "scoped_identifier" || child_s == "identifier" {
                        extract_path_segments(ctx, child, path);
                    }
                } else if child.kind == SyntaxKind::Identifier {
                    // This could be either the path or the name part
                    path.push(ctx.intern(&child.text));
                }
            }
        }
        _ => {
            // Recurse into children
            for child in &node.children {
                extract_path_segments(ctx, child, path);
            }
        }
    }
}

/// Extract alias from use declaration (as Name)
fn extract_use_alias(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<InternedString> {
    // Look for "as" keyword followed by identifier
    let mut found_as = false;
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "as" {
                found_as = true;
                continue;
            }
        }
        if found_as && child.kind == SyntaxKind::Identifier {
            return Some(ctx.intern(&child.text));
        }
    }
    None
}

/// Extract visibility from a syntax node
fn extract_visibility(node: &SyntaxNode) -> Visibility {
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "pub" || s == "visibility_modifier" {
                return Visibility::Public;
            }
        }
    }
    Visibility::Private
}

/// Rust v0 name mangling (simplified version)
/// Full spec: https://rust-lang.github.io/rfcs/2603-rust-symbol-name-mangling-v0.html
fn mangle_rust_v0(name: InternedString, interner: &Interner) -> String {
    let name_str = interner.resolve(&name);
    // Simplified mangling: _RNvC<crate><name>
    // For now, just use a basic mangling scheme
    format!("_RNv{}{}", name_str.len(), name_str)
}
