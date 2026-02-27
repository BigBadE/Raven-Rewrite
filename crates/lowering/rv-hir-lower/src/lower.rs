//! CST → HIR lowering with name resolution

use crate::{ScopeId, ScopeTree, SymbolId, SymbolKind, SymbolTable};
use rv_hir::{
    ArraySize, AssociatedType, AssociatedTypeImpl, Attribute, AttributeArgs, AttributeToken, Body,
    ConstId, ConstItem, DefId, EnumDef, Expr, ExprId, ExternalFunction, FieldDef, Function,
    FunctionId, GenericParam, GenericParamKind, ImplBlock, ImplId, Item, LangItem, LangItemRegistry,
    LiteralKind, LocalId, ModuleDef, ModuleId, Parameter, Pattern, PatternId, SelfParam, StaticId,
    StaticItem, Stmt, StmtId, StructDef, StructKind, TraitBound, TraitDef, TraitId, TraitMethod,
    Type, TypeAlias, TypeAliasId, TypeDefId, TypeId, TypeLevelTraitRef, UnaryOp, UseItem,
    VariantDef, VariantFields, Visibility, WhereClause,
};
use rv_intern::{Interner, Symbol as InternedString};
use rv_macro::{
    BuiltinMacroKind, Delimiter, MacroDef, MacroExpansionContext, MacroKind, Token, TokenStream,
};
use rv_span::{FileId, FileSpan};
use rv_syntax::{SyntaxKind, SyntaxNode};
use std::collections::HashMap;

/// Severity level for lowering diagnostics
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    /// Informational — construct recognized but intentionally deferred
    Info,
    /// Construct is recognized but not yet fully supported
    Warning,
    /// Construct should have been handled — indicates a gap in the compiler
    Error,
}

/// A diagnostic produced during lowering
#[derive(Debug, Clone)]
pub struct LoweringDiagnostic {
    /// Severity
    pub severity: DiagnosticSeverity,
    /// Human-readable message
    pub message: String,
    /// Source location
    pub span: FileSpan,
}

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
    /// Mapping from module IDs to their scope IDs (for module-qualified path resolution)
    pub module_scopes: HashMap<ModuleId, ScopeId>,
    /// Next module ID
    next_module_id: u32,
    /// HIR const items
    pub const_items: HashMap<ConstId, ConstItem>,
    /// Next const ID
    next_const_id: u32,
    /// HIR static items
    pub static_items: HashMap<StaticId, StaticItem>,
    /// Next static ID
    next_static_id: u32,
    /// HIR type aliases
    pub type_aliases: HashMap<TypeAliasId, TypeAlias>,
    /// Next type alias ID
    next_type_alias_id: u32,
    /// Map from symbol IDs to `DefIds`
    pub symbol_defs: HashMap<SymbolId, DefId>,
    /// File ID for creating spans
    file_id: FileId,
    /// Type arena
    pub types: la_arena::Arena<rv_hir::Type>,
    /// Next local ID for pattern bindings
    next_local_id: u32,
    /// Current impl block's self type (for resolving `self` parameters)
    current_impl_self_ty: Option<TypeId>,
    /// Current trait being lowered (for resolving `Self::Item` in trait definitions)
    current_trait_id: Option<TraitId>,
    /// Current function's generic parameter names (for resolving T -> Type::Generic)
    current_generic_params: Vec<InternedString>,
    /// Current function ID (for creating function-scoped DefId::Local)
    current_function_id: Option<FunctionId>,
    /// Macro expansion context
    pub macro_context: MacroExpansionContext,
    /// Next lifetime ID counter
    next_lifetime_id: u32,
    /// Diagnostics collected during lowering
    pub diagnostics: Vec<LoweringDiagnostic>,
    /// Lang item registry (populated after all items are lowered)
    pub lang_items: LangItemRegistry,
    /// FunctionIds of default trait method bodies (typed with Self, must be
    /// compiled on-demand per concrete type, not in the main compilation loop)
    pub default_method_bodies: std::collections::HashSet<FunctionId>,
    /// Enabled unstable features from `#![feature(...)]` attributes
    pub features: rv_hir::FeatureSet,
    /// Use declarations (imports) in this module
    pub use_items: Vec<UseItem>,
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
            module_scopes: HashMap::new(),
            next_module_id: 0,
            const_items: HashMap::new(),
            next_const_id: 0,
            static_items: HashMap::new(),
            next_static_id: 0,
            type_aliases: HashMap::new(),
            next_type_alias_id: 0,
            symbol_defs: HashMap::new(),
            file_id: FileId(0),
            types: la_arena::Arena::new(),
            next_local_id: 0,
            current_impl_self_ty: None,
            current_trait_id: None,
            current_generic_params: Vec::new(),
            current_function_id: None,
            macro_context,
            next_lifetime_id: 0,
            diagnostics: Vec::new(),
            default_method_bodies: std::collections::HashSet::new(),
            lang_items: LangItemRegistry::default(),
            features: rv_hir::FeatureSet::new(),
            use_items: Vec::new(),
        }
    }

    /// Report a diagnostic about an unhandled construct
    fn report_unhandled(&mut self, severity: DiagnosticSeverity, message: String, span: FileSpan) {
        self.diagnostics.push(LoweringDiagnostic {
            severity,
            message,
            span,
        });
    }

    /// Validate unsafe trait / unsafe impl consistency.
    ///
    /// Rules:
    /// 1. Implementing an unsafe trait requires `unsafe impl`.
    /// 2. `unsafe impl` on a non-unsafe trait is an error.
    fn validate_unsafe_traits(&mut self) {
        for impl_block in self.impl_blocks.values() {
            let Some(trait_id) = impl_block.trait_ref else {
                continue;
            };
            let Some(trait_def) = self.traits.get(&trait_id) else {
                continue;
            };

            if trait_def.is_unsafe && !impl_block.is_unsafe {
                let trait_name = self.interner.resolve(&trait_def.name).to_string();
                self.diagnostics.push(LoweringDiagnostic {
                    severity: DiagnosticSeverity::Error,
                    message: format!(
                        "implementing the unsafe trait `{}` requires `unsafe impl`",
                        trait_name
                    ),
                    span: impl_block.span,
                });
            }

            if impl_block.is_unsafe && !trait_def.is_unsafe {
                let trait_name = self.interner.resolve(&trait_def.name).to_string();
                self.diagnostics.push(LoweringDiagnostic {
                    severity: DiagnosticSeverity::Error,
                    message: format!(
                        "`unsafe impl` is not needed for non-unsafe trait `{}`",
                        trait_name
                    ),
                    span: impl_block.span,
                });
            }
        }
    }

    /// Scan all items for `#[lang = "..."]` attributes and populate the lang item registry.
    fn collect_lang_items(&mut self) {
        let lang_name = self.interner.intern("lang");

        // Scan traits
        let trait_entries: Vec<_> = self
            .traits
            .iter()
            .map(|(id, def)| (*id, def.attributes.clone()))
            .collect();
        for (trait_id, attrs) in trait_entries {
            if let Some(lang) = Self::extract_lang_item(&attrs, lang_name) {
                self.lang_items.register_trait(lang, trait_id);
            }
        }

        // Scan functions
        let fn_entries: Vec<_> = self
            .functions
            .iter()
            .map(|(id, def)| (*id, def.attributes.clone()))
            .collect();
        for (func_id, attrs) in fn_entries {
            if let Some(lang) = Self::extract_lang_item(&attrs, lang_name) {
                self.lang_items.register_fn(lang, func_id);
            }
        }

        // Scan structs
        let struct_entries: Vec<_> = self
            .structs
            .iter()
            .map(|(id, def)| (*id, def.attributes.clone()))
            .collect();
        for (type_def_id, attrs) in struct_entries {
            if let Some(lang) = Self::extract_lang_item(&attrs, lang_name) {
                self.lang_items.register_type(lang, type_def_id);
            }
        }
    }

    /// Extract a `LangItem` from a list of attributes, if a `#[lang = "..."]` attribute is present.
    fn extract_lang_item(attrs: &[Attribute], lang_name: rv_intern::Symbol) -> Option<LangItem> {
        for attr in attrs {
            if attr.name == lang_name {
                if let AttributeArgs::NameValue(_, ref value) = attr.args {
                    return LangItem::from_str(value);
                }
            }
        }
        None
    }

    /// Allocate a fresh lifetime ID
    fn alloc_lifetime_id(&mut self) -> rv_span::LifetimeId {
        let id = rv_span::LifetimeId(self.next_lifetime_id);
        self.next_lifetime_id += 1;
        id
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

    /// Get the next function ID that would be allocated.
    ///
    /// Used by multi-file compilation to set the starting offset
    /// for subsequent modules so FunctionIds are globally unique.
    #[must_use]
    pub fn next_function_id(&self) -> u32 {
        self.next_function_id
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

    /// Allocate a new const item ID
    fn alloc_const_id(&mut self) -> ConstId {
        let id = ConstId(self.next_const_id);
        self.next_const_id += 1;
        id
    }

    /// Allocate a new static item ID
    fn alloc_static_id(&mut self) -> StaticId {
        let id = StaticId(self.next_static_id);
        self.next_static_id += 1;
        id
    }

    /// Allocate a new type alias ID
    fn alloc_type_alias_id(&mut self) -> TypeAliasId {
        let id = TypeAliasId(self.next_type_alias_id);
        self.next_type_alias_id += 1;
        id
    }
}

impl Default for LoweringContext {
    fn default() -> Self {
        Self::new()
    }
}

impl LoweringContext {
    /// Create a LoweringContext from HirFileData fields.
    /// Used when multi-file compilation produces HirFileData that needs to be
    /// consumed by APIs expecting LoweringContext (monomorphization, LIR lowering).
    pub fn from_hir_fields(
        functions: HashMap<FunctionId, Function>,
        structs: HashMap<TypeDefId, StructDef>,
        enums: HashMap<TypeDefId, EnumDef>,
        traits: HashMap<TraitId, TraitDef>,
        impl_blocks: HashMap<ImplId, ImplBlock>,
        types: la_arena::Arena<rv_hir::Type>,
        interner: Interner,
    ) -> Self {
        let mut ctx = Self::new();
        ctx.functions = functions;
        ctx.structs = structs;
        ctx.enums = enums;
        ctx.traits = traits;
        ctx.impl_blocks = impl_blocks;
        ctx.types = types;
        ctx.interner = interner;
        ctx
    }
}

/// Instantiate blanket impl methods for all concrete types that satisfy the bounds.
///
/// For each blanket impl (e.g., `impl<T: Describable> Summary for T`), finds all
/// concrete types that implement the required trait bounds, clones the blanket
/// methods with the generic parameter replaced by the concrete type, and creates
/// a new concrete impl block.
fn instantiate_blanket_impls(ctx: &mut LoweringContext) {
    // Collect blanket impls and their data
    let blanket_impls: Vec<_> = ctx
        .impl_blocks
        .iter()
        .filter(|(_, ib)| ib.is_blanket && ib.trait_ref.is_some())
        .map(|(id, ib)| (*id, ib.clone()))
        .collect();

    if blanket_impls.is_empty() {
        return;
    }

    // Collect all concrete impl blocks that implement traits, keyed by TypeDefId.
    // We use TypeDefId (not TypeId) because each occurrence of a type name gets a
    // different TypeId in the arena, but they share the same TypeDefId.
    let concrete_trait_impls: Vec<_> = ctx
        .impl_blocks
        .iter()
        .filter(|(_, ib)| !ib.is_blanket && ib.trait_ref.is_some())
        .filter_map(|(_, ib)| {
            let def_id = match &ctx.types[ib.self_ty] {
                Type::Named { def: Some(d), .. } => Some(*d),
                _ => None,
            };
            def_id.map(|d| (d, ib.self_ty, ib.trait_ref.unwrap()))
        })
        .collect();

    for (_blanket_id, blanket_impl) in &blanket_impls {
        let blanket_trait_id = blanket_impl.trait_ref.unwrap();

        // Get the generic parameter name (e.g., "T")
        let generic_param_name = match blanket_impl.generic_params.first() {
            Some(gp) => gp.name,
            None => continue,
        };

        // Get the required trait bounds from the generic parameter
        let required_bounds: Vec<TraitId> = blanket_impl
            .generic_params
            .first()
            .map(|gp| gp.bounds.iter().map(|b| b.trait_ref).collect())
            .unwrap_or_default();

        // Find all concrete types that satisfy all required bounds
        // Use a set to avoid processing the same type multiple times
        let mut seen_types = std::collections::HashSet::new();
        for &(def_id, concrete_self_ty, _) in &concrete_trait_impls {
            if !seen_types.insert(def_id) {
                continue;
            }

            // Check if this concrete type implements all required trait bounds
            let satisfies_all = required_bounds.iter().all(|required_trait| {
                concrete_trait_impls
                    .iter()
                    .any(|(d, _, tid)| *d == def_id && *tid == *required_trait)
            });

            if !satisfies_all {
                continue;
            }

            // Check that this concrete type doesn't already have an impl for the blanket trait
            let already_has_impl = concrete_trait_impls
                .iter()
                .any(|(d, _, tid)| *d == def_id && *tid == blanket_trait_id);

            if already_has_impl {
                continue;
            }

            // Create concrete copies of the blanket impl's methods
            let mut new_methods = Vec::new();
            for &func_id in &blanket_impl.methods {
                if let Some(template_fn) = ctx.functions.get(&func_id).cloned() {
                    let new_fn_id = ctx.alloc_function_id();
                    let mut concrete_fn = template_fn;
                    concrete_fn.id = new_fn_id;
                    // Clear generic params so it's treated as a concrete function
                    concrete_fn.generics.clear();

                    // Replace generic parameter type references in parameters
                    for param in &mut concrete_fn.parameters {
                        let param_ty = &ctx.types[param.ty];
                        match param_ty {
                            Type::Reference {
                                inner,
                                mutable,
                                lifetime,
                                span,
                            } => {
                                let inner_ty = &ctx.types[**inner];
                                let should_replace = match inner_ty {
                                    Type::Named {
                                        name, def: None, ..
                                    } => *name == generic_param_name,
                                    Type::Generic { name, .. } => *name == generic_param_name,
                                    _ => false,
                                };
                                if should_replace {
                                    let new_ref = ctx.types.alloc(Type::Reference {
                                        inner: Box::new(concrete_self_ty),
                                        mutable: *mutable,
                                        lifetime: *lifetime,
                                        span: *span,
                                    });
                                    param.ty = new_ref;
                                }
                            }
                            Type::Named {
                                name, def: None, ..
                            } if *name == generic_param_name => {
                                param.ty = concrete_self_ty;
                            }
                            Type::Generic { name, .. } if *name == generic_param_name => {
                                param.ty = concrete_self_ty;
                            }
                            _ => {}
                        }
                    }

                    ctx.functions.insert(new_fn_id, concrete_fn);
                    new_methods.push(new_fn_id);
                }
            }

            // Create a new concrete impl block
            let new_impl_id = ctx.alloc_impl_id();
            let new_impl_block = ImplBlock {
                id: new_impl_id,
                self_ty: concrete_self_ty,
                trait_ref: Some(blanket_trait_id),
                generic_params: vec![],
                methods: new_methods,
                associated_type_impls: blanket_impl.associated_type_impls.clone(),
                where_clauses: vec![],
                is_unsafe: blanket_impl.is_unsafe,
                is_blanket: false,
                is_synthesized: true,
                is_negative: false,
                attributes: vec![],
                span: blanket_impl.span,
            };
            ctx.impl_blocks.insert(new_impl_id, new_impl_block);
        }
    }
}

/// Lower a source file to HIR
pub fn lower_source_file(root: &SyntaxNode) -> LoweringContext {
    lower_source_file_with_id_offset(root, 0)
}

/// Lower a source file with a starting function ID offset.
///
/// This is used for multi-file projects where each module needs globally
/// unique FunctionIds to avoid collisions during compilation.
pub fn lower_source_file_with_id_offset(
    root: &SyntaxNode,
    function_id_offset: u32,
) -> LoweringContext {
    let mut ctx = LoweringContext::new();
    ctx.next_function_id = function_id_offset;

    // Collect #![feature(...)] attributes first
    collect_feature_flags(&mut ctx, &root.children);

    // Create root scope
    let root_scope = ctx.scope_tree.create_root(root.span);

    // Process all top-level items
    lower_items(&mut ctx, root_scope, &root.children);

    // Instantiate blanket impl methods for concrete types that satisfy bounds
    instantiate_blanket_impls(&mut ctx);

    // Collect lang items from #[lang = "..."] attributes
    ctx.collect_lang_items();

    // Validate unsafe trait/impl consistency
    ctx.validate_unsafe_traits();

    ctx
}

/// Collect `#![feature(...)]` attributes and enable corresponding features.
fn collect_feature_flags(ctx: &mut LoweringContext, children: &[SyntaxNode]) {
    for child in children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "inner_attribute_item" {
                // Check if this is a feature attribute
                if let Some(attr_node) = child
                    .children
                    .iter()
                    .find(|c| matches!(&c.kind, SyntaxKind::Unknown(ref s) if s == "attribute"))
                {
                    // Get attribute name
                    let name = attr_node
                        .children
                        .iter()
                        .find(|c| c.kind == SyntaxKind::Identifier)
                        .map(|c| c.text.as_str());

                    if name == Some("feature") {
                        // Parse the feature list from token_tree
                        if let Some(tt) = attr_node
                            .children
                            .iter()
                            .find(|c| matches!(&c.kind, SyntaxKind::Unknown(ref s) if s == "token_tree"))
                        {
                            collect_features_from_token_tree(ctx, tt);
                        }
                    }
                }
            }
        }
    }
}

/// Extract feature names from a token_tree and enable them.
fn collect_features_from_token_tree(ctx: &mut LoweringContext, tt: &SyntaxNode) {
    for child in &tt.children {
        match &child.kind {
            SyntaxKind::Identifier => {
                let feature = rv_hir::Feature::from_name(&child.text, &ctx.interner);
                ctx.features.enable(feature);
            }
            SyntaxKind::Unknown(ref s) if s == "token_tree" => {
                // Nested token tree (shouldn't happen in feature attrs, but handle gracefully)
                collect_features_from_token_tree(ctx, child);
            }
            _ => {
                // Skip punctuation like commas, parens, etc.
            }
        }
    }
}

/// Parse a single attribute from an `attribute_item` or `inner_attribute_item` tree-sitter node.
///
/// Tree-sitter structure for `#[inline]`: attribute_item > attribute > identifier("inline")
/// Tree-sitter structure for `#[repr(C)]`: attribute_item > attribute > identifier("repr") + token_tree(...)
/// Tree-sitter structure for `#[path = "foo.rs"]`: attribute_item > attribute > identifier("path") + "=" + string_literal
fn lower_attribute(ctx: &mut LoweringContext, node: &SyntaxNode, is_inner: bool) -> Attribute {
    let span = ctx.file_span(node);

    // The attribute_item node wraps an "attribute" child, or may directly contain the content.
    // Navigate to the inner attribute content.
    let attr_node = node
        .children
        .iter()
        .find(|c| matches!(&c.kind, SyntaxKind::Unknown(ref s) if s == "attribute"))
        .unwrap_or(node);

    // First identifier child is the attribute name
    let name = attr_node
        .children
        .iter()
        .find(|c| c.kind == SyntaxKind::Identifier)
        .map(|c| ctx.intern(&c.text))
        .unwrap_or_else(|| {
            // Some attributes may use a path (e.g., rustc_const_stable) — use first text-like child
            ctx.intern(&attr_node.text)
        });

    // Determine arguments
    let args = parse_attribute_args(ctx, attr_node);

    Attribute {
        name,
        args,
        is_inner,
        span,
    }
}

/// Parse attribute arguments from an attribute node.
fn parse_attribute_args(ctx: &mut LoweringContext, node: &SyntaxNode) -> AttributeArgs {
    // Look for "=" (name-value style) or token_tree (delimited style)
    let mut has_eq = false;
    let mut value_str = None;
    let mut token_tree_node = None;

    for child in &node.children {
        if child.text == "=" {
            has_eq = true;
        } else if has_eq && child.kind == SyntaxKind::Literal {
            // Strip quotes from string literal
            let text = child.text.trim_matches('"').to_string();
            value_str = Some(text);
        } else if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "token_tree") {
            token_tree_node = Some(child);
        }
    }

    if has_eq {
        if let Some(val) = value_str {
            let val_name = ctx.intern(
                &node
                    .children
                    .iter()
                    .find(|c| c.kind == SyntaxKind::Identifier)
                    .map(|c| c.text.clone())
                    .unwrap_or_default(),
            );
            let _ = val_name; // name is already on the Attribute itself
            return AttributeArgs::NameValue(ctx.intern(&val), val);
        }
    }

    if let Some(tt) = token_tree_node {
        let tokens = lower_token_tree(ctx, tt);
        return AttributeArgs::Delimited(tokens);
    }

    AttributeArgs::Empty
}

/// Lower a token_tree node into a flat list of AttributeTokens.
fn lower_token_tree(ctx: &mut LoweringContext, node: &SyntaxNode) -> Vec<AttributeToken> {
    let mut tokens = Vec::new();
    for child in &node.children {
        match &child.kind {
            SyntaxKind::Identifier => {
                tokens.push(AttributeToken::Ident(ctx.intern(&child.text)));
            }
            SyntaxKind::Type => {
                // type_identifier shows up as SyntaxKind::Type in our mapping
                tokens.push(AttributeToken::Ident(ctx.intern(&child.text)));
            }
            SyntaxKind::Literal => {
                if child.text.starts_with('"') {
                    tokens.push(AttributeToken::StringLit(
                        child.text.trim_matches('"').to_string(),
                    ));
                } else if let Ok(n) = child.text.parse::<i64>() {
                    tokens.push(AttributeToken::IntLit(n));
                } else {
                    tokens.push(AttributeToken::StringLit(child.text.clone()));
                }
            }
            SyntaxKind::Unknown(ref s) if s == "token_tree" => {
                // Nested token tree — recurse
                let inner = lower_token_tree(ctx, child);
                tokens.push(AttributeToken::Group(inner));
            }
            _ => {
                // Punctuation or other tokens
                let text = &child.text;
                if text.len() == 1 {
                    if let Some(ch) = text.chars().next() {
                        if !ch.is_alphanumeric() && ch != '_' {
                            tokens.push(AttributeToken::Punct(ch));
                            continue;
                        }
                    }
                }
                // Multi-char punctuation or unknown — store as ident
                if !text.is_empty() && text != "(" && text != ")" && text != "[" && text != "]" {
                    tokens.push(AttributeToken::Ident(ctx.intern(text)));
                }
            }
        }
    }
    tokens
}

/// Collect attributes from sibling nodes that precede an item.
/// In tree-sitter, attributes are sibling nodes preceding the item they annotate.
/// This function collects all `attribute_item` nodes from the children list
/// that appear before the given item index.
fn collect_preceding_attributes(
    ctx: &mut LoweringContext,
    children: &[SyntaxNode],
    item_index: usize,
) -> Vec<Attribute> {
    let mut attrs = Vec::new();
    // Walk backwards from item_index - 1 to collect consecutive attribute_item nodes
    if item_index == 0 {
        return attrs;
    }
    let mut i = item_index - 1;
    loop {
        let child = &children[i];
        match &child.kind {
            SyntaxKind::Unknown(ref s) if s == "attribute_item" => {
                attrs.push(lower_attribute(ctx, child, false));
            }
            SyntaxKind::Unknown(ref s) if s == "inner_attribute_item" => {
                attrs.push(lower_attribute(ctx, child, true));
            }
            _ => break,
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }
    // Reverse since we collected from bottom to top
    attrs.reverse();
    attrs
}

/// Check if a SyntaxNode with Unknown kind represents a type-like construct.
/// tree-sitter-rust represents many type forms as named node kinds that our
/// language adapter maps to SyntaxKind::Unknown("..."). This helper identifies
/// those so we can treat them as types in impl blocks, function signatures, etc.
fn is_type_like_unknown(node: &SyntaxNode) -> bool {
    if let SyntaxKind::Unknown(ref s) = node.kind {
        matches!(
            s.as_str(),
            "scoped_type_identifier"
                | "generic_type"
                | "pointer_type"
                | "reference_type"
                | "array_type"
                | "tuple_type"
                | "never_type"
                | "function_type"
                | "bounded_type"
                | "primitive_type"
                | "dynamic_type"
                | "abstract_type"
                | "macro_invocation"
        )
    } else {
        false
    }
}

fn parse_visibility(node: &SyntaxNode) -> Visibility {
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "visibility_modifier" {
                return Visibility::Public;
            }
        }
    }
    Visibility::Private
}

/// Check if a function_item node has specific modifiers (unsafe, const, async, etc.)
fn parse_function_modifiers(node: &SyntaxNode) -> (bool, bool) {
    let mut is_unsafe = false;
    let mut is_const = false;
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "function_modifiers" {
                for modifier in &child.children {
                    match modifier.text.as_str() {
                        "unsafe" => is_unsafe = true,
                        "const" => is_const = true,
                        _ => {}
                    }
                }
            }
        }
        // tree-sitter may also emit bare "unsafe" or "const" keywords as direct children
        if child.text == "unsafe" && child.kind != SyntaxKind::Identifier {
            is_unsafe = true;
        }
        if child.text == "const" && child.kind != SyntaxKind::Identifier {
            is_const = true;
        }
    }
    (is_unsafe, is_const)
}

/// Lower multiple items
fn lower_items(ctx: &mut LoweringContext, current_scope: ScopeId, children: &[SyntaxNode]) {
    // Pre-pass: register all top-level names (functions, structs, enums, traits)
    // so that forward references resolve correctly regardless of source order.
    pre_register_items(ctx, current_scope, children);

    // Main pass: lower all item bodies (use index for attribute collection)
    for (idx, child) in children.iter().enumerate() {
        match child.kind {
            SyntaxKind::Function => {
                let attrs = collect_preceding_attributes(ctx, children, idx);
                lower_function_with_attrs(ctx, current_scope, child, attrs);
            }
            SyntaxKind::Struct => {
                let attrs = collect_preceding_attributes(ctx, children, idx);
                lower_struct_with_attrs(ctx, current_scope, child, attrs);
            }
            SyntaxKind::Enum => {
                let attrs = collect_preceding_attributes(ctx, children, idx);
                lower_enum_with_attrs(ctx, current_scope, child, attrs);
            }
            SyntaxKind::Impl => {
                let attrs = collect_preceding_attributes(ctx, children, idx);
                lower_impl_with_attrs(ctx, current_scope, child, attrs);
            }
            SyntaxKind::Trait => {
                let attrs = collect_preceding_attributes(ctx, children, idx);
                lower_trait_with_attrs(ctx, current_scope, child, attrs);
            }
            SyntaxKind::Unknown(ref s) if s == "extern_block" || s == "foreign_mod_item" => {
                lower_extern_block(ctx, current_scope, child);
            }
            SyntaxKind::Unknown(ref s) if s == "mod_item" => {
                lower_module(ctx, current_scope, child);
            }
            SyntaxKind::Unknown(ref s) if s == "use_declaration" => {
                if let Some(use_item) = lower_use(ctx, child) {
                    ctx.use_items.push(use_item);
                }
            }
            SyntaxKind::Unknown(ref s) if s == "const_item" => {
                let attrs = collect_preceding_attributes(ctx, children, idx);
                lower_const_item(ctx, current_scope, child, attrs);
            }
            SyntaxKind::Unknown(ref s) if s == "static_item" => {
                let attrs = collect_preceding_attributes(ctx, children, idx);
                lower_static_item(ctx, current_scope, child, attrs);
            }
            SyntaxKind::Unknown(ref s) if s == "type_item" => {
                let attrs = collect_preceding_attributes(ctx, children, idx);
                lower_type_alias(ctx, child, attrs);
            }
            SyntaxKind::MacroDefinition => {
                lower_macro_definition(ctx, child);
            }
            SyntaxKind::MacroInvocation => {
                lower_macro_invocation_item(ctx, current_scope, child);
            }
            // Skip attribute items (collected by their following items)
            SyntaxKind::Unknown(ref s) if s == "attribute_item" || s == "inner_attribute_item" => {}
            // Skip punctuation and whitespace nodes
            SyntaxKind::Unknown(ref s)
                if s == "line_comment" || s == "block_comment" || s == ";" => {}
            _ => {
                // Report unhandled item types
                let kind_name = match &child.kind {
                    SyntaxKind::Unknown(s) => s.clone(),
                    other => format!("{other:?}"),
                };
                ctx.report_unhandled(
                    DiagnosticSeverity::Warning,
                    format!("unhandled item kind: {kind_name}"),
                    ctx.file_span(child),
                );
            }
        }
    }
}

/// Pre-register all top-level item names in the scope tree.
/// This allows forward references: a function defined later in the file can be
/// called by an earlier function.
fn pre_register_items(ctx: &mut LoweringContext, current_scope: ScopeId, children: &[SyntaxNode]) {
    for child in children {
        let (kind, syntax_kind) = match child.kind {
            SyntaxKind::Function => ("function", &child.kind),
            SyntaxKind::Struct => ("struct", &child.kind),
            SyntaxKind::Enum => ("enum", &child.kind),
            SyntaxKind::Trait => ("trait", &child.kind),
            _ => continue,
        };

        // Extract the item name from its children
        let name = child
            .children
            .iter()
            .find(|c| c.kind == SyntaxKind::Identifier || c.kind == SyntaxKind::Type)
            .map(|c| c.text.clone());

        let name = match name {
            Some(n) if !n.is_empty() => n,
            _ => continue,
        };

        // Skip if already registered (e.g. from a previous pre-pass)
        if ctx.scope_tree.resolve(current_scope, &name).is_some() {
            continue;
        }

        let name_interned = ctx.intern(&name);

        let symbol_id = ctx.symbols.add(
            name_interned,
            SymbolKind::Function,
            child.span,
            current_scope,
        );
        ctx.scope_tree
            .add_symbol(current_scope, name.clone(), symbol_id);

        // Allocate appropriate ID and create DefId
        let def_id = match syntax_kind {
            SyntaxKind::Function => {
                let function_id = ctx.alloc_function_id();
                DefId::Function(function_id)
            }
            SyntaxKind::Struct | SyntaxKind::Enum => {
                let type_id = ctx.alloc_type_id();
                DefId::Type(type_id)
            }
            SyntaxKind::Trait => {
                let trait_id = ctx.alloc_trait_id();
                DefId::Trait(trait_id)
            }
            other => panic!(
                "ICE: Unexpected syntax kind {:?} in pre_register_items DefId allocation. \
                 Only Function, Struct, Enum, and Trait should reach this point.",
                other
            ),
        };

        ctx.symbols.set_def_id(symbol_id, def_id);
        ctx.symbol_defs.insert(symbol_id, def_id);

        let _ = kind; // used for documentation clarity
    }
}

/// Lower a function definition
/// Wrapper for lower_items calling convention
fn lower_function_with_attrs(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    lower_function(ctx, current_scope, node, attrs);
}

fn lower_function(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    // Extract function name from children
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| child.text.clone())
        .unwrap_or_else(|| {
            panic!(
                "ICE: Function declaration at {:?} has no identifier. \
                 Parser should ensure all function_item nodes contain an identifier.",
                ctx.file_span(node)
            )
        });

    if name.is_empty() {
        panic!(
            "ICE: Function declaration at {:?} has empty identifier. \
             Parser should ensure function identifiers are non-empty.",
            ctx.file_span(node)
        )
    }

    let name_interned = ctx.intern(&name);
    let file_span = ctx.file_span(node);

    // Parse function modifiers (unsafe, const)
    let (is_unsafe, is_const) = parse_function_modifiers(node);

    // Reuse the pre-registered symbol if available, otherwise register now
    // Handle name shadowing: if existing symbol is not a function (e.g., module),
    // create a new function symbol instead of panicking
    let (symbol_id, function_id) =
        if let Some(existing_sym) = ctx.scope_tree.resolve(current_scope, &name) {
            let def_id = ctx.symbol_defs.get(&existing_sym).copied();
            match def_id {
                Some(DefId::Function(fid)) => (existing_sym, fid),
                _ => {
                    // The existing symbol is not a function (e.g., module with same name).
                    // Create a new function symbol which will shadow it in this scope.
                    let symbol_id = ctx.symbols.add(
                        name_interned,
                        SymbolKind::Function,
                        node.span,
                        current_scope,
                    );
                    // Note: We still add to scope tree - it will shadow the previous symbol
                    ctx.scope_tree
                        .add_symbol(current_scope, name.clone(), symbol_id);
                    let function_id = ctx.alloc_function_id();
                    let def_id = DefId::Function(function_id);
                    ctx.symbols.set_def_id(symbol_id, def_id);
                    ctx.symbol_defs.insert(symbol_id, def_id);
                    (symbol_id, function_id)
                }
            }
        } else {
            let symbol_id = ctx.symbols.add(
                name_interned,
                SymbolKind::Function,
                node.span,
                current_scope,
            );
            ctx.scope_tree
                .add_symbol(current_scope, name.clone(), symbol_id);
            let function_id = ctx.alloc_function_id();
            let def_id = DefId::Function(function_id);
            ctx.symbols.set_def_id(symbol_id, def_id);
            ctx.symbol_defs.insert(symbol_id, def_id);
            (symbol_id, function_id)
        };

    let _ = symbol_id; // used above for lookup

    // Set current function ID for DefId::Local creation
    ctx.current_function_id = Some(function_id);

    // Parse generic and lifetime parameters
    let mut generics = vec![];
    let mut lifetime_params = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generics = parse_generic_params(ctx, child);
            lifetime_params = parse_lifetime_params(ctx, child);
            break;
        }
    }

    // ARCHITECTURE: Set current generic params for lower_type_node to recognize generic references
    ctx.current_generic_params = generics.iter().map(|g| g.name).collect();

    // Parse parameters
    let mut parameters = vec![];
    let mut self_param_parsed = None;
    for child in &node.children {
        if child.kind == SyntaxKind::Parameters {
            let (params, sp) = parse_parameters(ctx, child);
            parameters = params;
            self_param_parsed = sp;
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

    // Apply lifetime elision rules to fill in elided reference lifetimes
    apply_lifetime_elision(
        ctx,
        &parameters,
        return_type,
        self_param_parsed,
        &mut lifetime_params,
    );

    // Clear current generic params after parsing parameters and return type
    ctx.current_generic_params.clear();

    // Create function scope for body
    let fn_scope = ctx.scope_tree.create_child(current_scope, node.span);

    // Add parameters to the function scope
    for (param_idx, param) in parameters.iter().enumerate() {
        let param_name_str = ctx.interner.resolve(&param.name).to_string();
        let param_symbol =
            ctx.symbols
                .add(param.name, SymbolKind::Local, param.span.span, fn_scope);
        ctx.scope_tree
            .add_symbol(fn_scope, param_name_str.clone(), param_symbol);

        // Create a LocalId for the parameter
        let local_id = rv_hir::LocalId(param_idx as u32);
        let def_id = DefId::Local {
            func: function_id,
            local: local_id,
        };
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

    // Extract visibility
    let visibility = extract_visibility(node);

    // Create HIR function (without resolution yet)
    let function_temp = Function {
        id: function_id,
        name: name_interned,
        visibility,
        span: file_span,
        generics: generics.clone(),
        lifetime_params: lifetime_params.clone(),
        parameters: parameters.clone(),
        return_type,
        body,
        is_external: false,
        is_unsafe,
        is_const,
        attributes: attrs.clone(),
        self_param: self_param_parsed,
    };

    // ARCHITECTURE: Build global functions map for name resolution
    // This allows function calls to resolve to DefId::Function
    let mut global_functions = std::collections::HashMap::default();
    for (&func_id, func) in &ctx.functions {
        global_functions.insert(func.name, rv_hir::DefId::Function(func_id));
    }
    // Also include the current function being lowered
    global_functions.insert(name_interned, rv_hir::DefId::Function(function_id));

    // Run name resolution on the body
    let resolution_result = rv_resolve::NameResolver::resolve(
        &function_temp.body,
        &function_temp,
        &ctx.interner,
        global_functions,
    );

    // Report name resolution errors as diagnostics rather than panicking.
    // Many resolution failures are expected when lowering code that uses features
    // not yet supported (e.g., `self` parameters, module paths, etc.)
    if !resolution_result.errors.is_empty() {
        let func_name = ctx.interner.resolve(&name_interned);
        ctx.report_unhandled(
            DiagnosticSeverity::Error,
            format!(
                "name resolution failed for function '{}': {} errors",
                func_name,
                resolution_result.errors.len()
            ),
            file_span,
        );
    }

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
        visibility,
        span: file_span,
        generics,
        lifetime_params,
        parameters,
        return_type: function_temp.return_type,
        body: body_with_resolution,
        is_external: false,
        is_unsafe,
        is_const,
        attributes: attrs,
        self_param: self_param_parsed,
    };

    if ctx.interner.resolve(&name_interned) == "get_value"
        || ctx.interner.resolve(&name_interned) == "increment"
    {}

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
                // tree-sitter wraps both semicolon-terminated statements AND
                // trailing return expressions in expression_statement nodes.
                // Distinguish them: if the node contains a ";" child, it's a
                // statement. Otherwise, it's a trailing/return expression.
                let has_semicolon = child
                    .children
                    .iter()
                    .any(|c| matches!(&c.kind, SyntaxKind::Unknown(s) if s == ";"));

                if has_semicolon {
                    // Semicolon-terminated: this is a statement (side effect).
                    // Flush any previous trailing expression to statements first.
                    if let Some(prev_expr) = trailing_expr.take() {
                        let stmt_id = body.stmts.alloc(rv_hir::Stmt::Expr {
                            expr: prev_expr,
                            span: ctx.file_span(child),
                        });
                        statements.push(stmt_id);
                    }

                    if let Some(expr_child) = child.children.first() {
                        if is_expr_node(expr_child) {
                            let expr_id = lower_expr(ctx, block_scope, expr_child, body);
                            let stmt_id = body.stmts.alloc(rv_hir::Stmt::Expr {
                                expr: expr_id,
                                span: ctx.file_span(child),
                            });
                            statements.push(stmt_id);
                        }
                    }
                } else {
                    // No semicolon: this is a trailing/return expression.
                    // Flush any previous trailing expression to statements first.
                    if let Some(prev_expr) = trailing_expr.take() {
                        let stmt_id = body.stmts.alloc(rv_hir::Stmt::Expr {
                            expr: prev_expr,
                            span: ctx.file_span(child),
                        });
                        statements.push(stmt_id);
                    }

                    if let Some(expr_child) = child.children.first() {
                        if is_expr_node(expr_child) {
                            let expr_id = lower_expr(ctx, block_scope, expr_child, body);
                            trailing_expr = Some(expr_id);
                        }
                    }
                }
            }
            _ => {
                // Try to lower as expression (potential trailing expression)
                if is_expr_node(child) {
                    // Flush any previous trailing expression to statements
                    if let Some(prev_expr) = trailing_expr.take() {
                        let stmt_id = body.stmts.alloc(rv_hir::Stmt::Expr {
                            expr: prev_expr,
                            span: ctx.file_span(child),
                        });
                        statements.push(stmt_id);
                    }
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
            | SyntaxKind::While
            | SyntaxKind::For
            | SyntaxKind::Identifier
            | SyntaxKind::MacroInvocation
    ) || matches!(&node.kind, SyntaxKind::Unknown(name) if
        name == "field_expression"
        || name == "struct_expression"
        || name == "self"
        || name == "closure_expression"
        || name == "reference_expression"
        || name == "assignment_expression"
        || name == "compound_assignment_expr"
        || name == "loop_expression"
        || name == "break_expression"
        || name == "continue_expression"
        || name == "array_expression"
        || name == "tuple_expression"
        || name == "parenthesized_expression"
        || name == "index_expression"
        || name == "type_cast_expression"
        || name == "unary_expression"
        || name == "scoped_identifier"
        || name == "macro_invocation"
        || name == "range_expression"
        || name == "try_expression"
        || name == "unsafe_block"
    )
}

/// Check if a node represents a pattern (for use in let statements, match arms, etc.)
fn is_pattern_node(node: &SyntaxNode) -> bool {
    // Identifier can be a pattern (binding) - but we handle it separately in let statements
    if node.kind == SyntaxKind::Identifier {
        return true;
    }
    // All pattern types from tree-sitter-rust
    matches!(&node.kind, SyntaxKind::Unknown(name) if
        name == "tuple_pattern"
        || name == "struct_pattern"
        || name == "tuple_struct_pattern"
        || name == "or_pattern"
        || name == "range_pattern"
        || name == "as_pattern"
        || name == "ref_pattern"
        || name == "mut_pattern"
        || name == "slice_pattern"
        || name == "remaining_field_pattern"
        || name == "reference_pattern"
        || name == "captured_pattern"
        || name == "match_pattern"
        || name == "_"
    )
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
        SyntaxKind::While => lower_while_expr(ctx, current_scope, node, body),
        SyntaxKind::For => lower_for_expr(ctx, current_scope, node, body),
        SyntaxKind::Call => lower_call(ctx, current_scope, node, body),
        SyntaxKind::MacroInvocation => lower_macro_invocation_expr(ctx, current_scope, node, body),
        SyntaxKind::Unknown(ref name) => match name.as_str() {
            "field_expression" => lower_field_access(ctx, current_scope, node, body),
            "struct_expression" => lower_struct_construct(ctx, current_scope, node, body),
            "closure_expression" => lower_closure(ctx, current_scope, node, body),
            "scoped_identifier" => {
                // Scoped identifier used as expression (e.g., Status::Active).
                // Check if this is a unit enum variant construction.
                if let Some(enum_expr) = try_lower_unit_enum_variant(ctx, current_scope, node, body)
                {
                    enum_expr
                } else {
                    // Not an enum variant — treat as a path-qualified variable reference.
                    ctx.report_unhandled(
                        DiagnosticSeverity::Warning,
                        format!("unresolved scoped identifier: {}", node.text),
                        file_span,
                    );
                    body.exprs.alloc(Expr::Literal {
                        kind: LiteralKind::Unit,
                        span: file_span,
                    })
                }
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
            "reference_expression" => {
                // Reference expression: &expr or &mut expr
                let is_mut = node.children.iter().any(|child| child.text == "mut");
                let operand_node = node
                    .children
                    .iter()
                    .find(|child| is_expr_node(child))
                    .expect("reference_expression must have an operand");
                let operand = lower_expr(ctx, current_scope, operand_node, body);
                body.exprs.alloc(Expr::UnaryOp {
                    op: if is_mut {
                        UnaryOp::RefMut
                    } else {
                        UnaryOp::Ref
                    },
                    operand,
                    span: file_span,
                })
            }
            "unary_expression" => {
                // Unary expression: -expr, !expr, *expr
                let mut op = None;
                let mut operand_node = None;
                for child in &node.children {
                    if child.text == "-" && op.is_none() {
                        op = Some(UnaryOp::Neg);
                    } else if child.text == "!" && op.is_none() {
                        op = Some(UnaryOp::Not);
                    } else if child.text == "*" && op.is_none() {
                        op = Some(UnaryOp::Deref);
                    } else if is_expr_node(child) {
                        operand_node = Some(child);
                    }
                }
                // Handle malformed unary expressions (e.g., from parse error recovery)
                // In this case, create an error placeholder expression
                let operand = if let Some(node) = operand_node {
                    lower_expr(ctx, current_scope, node, body)
                } else {
                    // Create an error literal as placeholder for malformed expression
                    body.exprs.alloc(Expr::Literal {
                        kind: LiteralKind::Integer(0, None),
                        span: file_span,
                    })
                };
                body.exprs.alloc(Expr::UnaryOp {
                    op: op.unwrap_or(UnaryOp::Not),
                    operand,
                    span: file_span,
                })
            }
            "assignment_expression" => lower_assignment(ctx, current_scope, node, body),
            "compound_assignment_expr" => lower_compound_assignment(ctx, current_scope, node, body),
            "loop_expression" => lower_loop_expr(ctx, current_scope, node, body),
            "break_expression" => {
                let mut value = None;
                let mut label = None;
                for child in &node.children {
                    if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "label") {
                        // Parse the label
                        let text = child.text.trim_start_matches('\'');
                        if !text.is_empty() {
                            label = Some(ctx.intern(text));
                        }
                    } else if is_expr_node(child) {
                        value = Some(lower_expr(ctx, current_scope, child, body));
                    }
                }
                body.exprs.alloc(Expr::Break {
                    value,
                    label,
                    span: file_span,
                })
            }
            "continue_expression" => {
                let mut label = None;
                for child in &node.children {
                    if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "label") {
                        // Parse the label
                        let text = child.text.trim_start_matches('\'');
                        if !text.is_empty() {
                            label = Some(ctx.intern(text));
                        }
                    }
                }
                body.exprs.alloc(Expr::Continue {
                    label,
                    span: file_span,
                })
            }
            "array_expression" => {
                let mut elements = Vec::new();
                for child in &node.children {
                    if is_expr_node(child) {
                        elements.push(lower_expr(ctx, current_scope, child, body));
                    }
                }
                body.exprs.alloc(Expr::Array {
                    elements,
                    span: file_span,
                })
            }
            "tuple_expression" => {
                let mut elements = Vec::new();
                for child in &node.children {
                    if is_expr_node(child) {
                        elements.push(lower_expr(ctx, current_scope, child, body));
                    }
                }
                body.exprs.alloc(Expr::Tuple {
                    elements,
                    span: file_span,
                })
            }
            "parenthesized_expression" => {
                // Parenthesized expression: (expr) - just lower the inner expression
                for child in &node.children {
                    if is_expr_node(child) {
                        return lower_expr(ctx, current_scope, child, body);
                    }
                }
                body.exprs.alloc(Expr::Literal {
                    kind: LiteralKind::Unit,
                    span: file_span,
                })
            }
            "index_expression" => {
                let mut base = None;
                let mut index = None;
                for child in &node.children {
                    if is_expr_node(child) {
                        if base.is_none() {
                            base = Some(lower_expr(ctx, current_scope, child, body));
                        } else if index.is_none() {
                            index = Some(lower_expr(ctx, current_scope, child, body));
                        }
                    }
                }
                if let (Some(base_expr), Some(index_expr)) = (base, index) {
                    body.exprs.alloc(Expr::Index {
                        base: base_expr,
                        index: index_expr,
                        span: file_span,
                    })
                } else {
                    body.exprs.alloc(Expr::Literal {
                        kind: LiteralKind::Unit,
                        span: file_span,
                    })
                }
            }
            "type_cast_expression" => {
                let mut expr = None;
                let mut ty = None;
                for child in &node.children {
                    if is_expr_node(child) && expr.is_none() {
                        expr = Some(lower_expr(ctx, current_scope, child, body));
                    } else if (child.kind == SyntaxKind::Type || is_type_like_unknown(child))
                        && ty.is_none()
                    {
                        ty = Some(lower_type_node(ctx, child));
                    }
                }
                if let (Some(cast_expr), Some(cast_ty)) = (expr, ty) {
                    body.exprs.alloc(Expr::Cast {
                        expr: cast_expr,
                        ty: cast_ty,
                        span: file_span,
                    })
                } else {
                    body.exprs.alloc(Expr::Literal {
                        kind: LiteralKind::Unit,
                        span: file_span,
                    })
                }
            }
            "unsafe_block" => {
                // unsafe { ... } — lower the inner block and wrap in UnsafeBlock
                for child in &node.children {
                    if child.kind == SyntaxKind::Block {
                        let inner = lower_block(ctx, current_scope, child, body);
                        return body.exprs.alloc(Expr::UnsafeBlock {
                            body: inner,
                            span: file_span,
                        });
                    }
                }
                body.exprs.alloc(Expr::Literal {
                    kind: LiteralKind::Unit,
                    span: file_span,
                })
            }
            "return_expression" => {
                // return [expr] — handle return expressions that appear as Unknown
                let mut value = None;
                for child in &node.children {
                    if is_expr_node(child) {
                        value = Some(lower_expr(ctx, current_scope, child, body));
                        break;
                    }
                }
                // Allocate a return statement and wrap as unit expression
                let stmt = body.stmts.alloc(Stmt::Return {
                    value,
                    span: file_span,
                });
                // We can't directly return a statement as an expression in the current
                // architecture, so we lower it as a block with the return statement
                body.exprs.alloc(Expr::Block {
                    statements: vec![stmt],
                    expr: None,
                    span: file_span,
                })
            }
            "range_expression" => {
                // Range expression: 1..10, 1..=10, ..10, 1.., ..
                let mut start = None;
                let mut end = None;
                let mut inclusive = false;
                let mut found_operator = false;

                for child in &node.children {
                    if child.text == ".." {
                        found_operator = true;
                        inclusive = false;
                    } else if child.text == "..=" {
                        found_operator = true;
                        inclusive = true;
                    } else if is_expr_node(child) {
                        if !found_operator {
                            start = Some(lower_expr(ctx, current_scope, child, body));
                        } else {
                            end = Some(lower_expr(ctx, current_scope, child, body));
                        }
                    }
                }

                body.exprs.alloc(Expr::Range {
                    start,
                    end,
                    inclusive,
                    span: file_span,
                })
            }
            "try_expression" => {
                // Try expression: expr?
                let mut inner = None;
                for child in &node.children {
                    if is_expr_node(child) {
                        inner = Some(lower_expr(ctx, current_scope, child, body));
                        break;
                    }
                }
                if let Some(expr) = inner {
                    body.exprs.alloc(Expr::Try {
                        expr,
                        span: file_span,
                    })
                } else {
                    body.exprs.alloc(Expr::Error { span: file_span })
                }
            }
            "macro_invocation" => {
                // Macro invocation in expression position (e.g., cfg!(), println!())
                lower_macro_invocation_expr(ctx, current_scope, node, body)
            }
            _ => {
                ctx.report_unhandled(
                    DiagnosticSeverity::Warning,
                    format!("unhandled expression kind: {name}"),
                    file_span,
                );
                body.exprs.alloc(Expr::Literal {
                    kind: LiteralKind::Unit,
                    span: file_span,
                })
            }
        },
        _ => {
            let kind_name = match &node.kind {
                SyntaxKind::Unknown(s) => s.clone(),
                other => format!("{other:?}"),
            };
            ctx.report_unhandled(
                DiagnosticSeverity::Warning,
                format!("unhandled expression node: {kind_name}"),
                file_span,
            );
            body.exprs.alloc(Expr::Literal {
                kind: LiteralKind::Unit,
                span: file_span,
            })
        }
    }
}

/// Lower an assignment expression (target = value)
fn lower_assignment(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    let mut target_node = None;
    let mut value_node = None;

    for child in &node.children {
        if is_expr_node(child) {
            if target_node.is_none() {
                target_node = Some(child);
            } else if value_node.is_none() {
                value_node = Some(child);
            }
        }
    }

    let target = lower_expr(
        ctx,
        current_scope,
        target_node.expect("ICE: assignment_expression must have a target expression"),
        body,
    );
    let value = lower_expr(
        ctx,
        current_scope,
        value_node.expect("ICE: assignment_expression must have a value expression"),
        body,
    );

    body.exprs.alloc(Expr::Assign {
        target,
        value,
        span: file_span,
    })
}

/// Lower a compound assignment expression (target += value, target -= value, etc.)
fn lower_compound_assignment(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    let mut target_node = None;
    let mut value_node = None;
    let mut op_text = None;

    for child in &node.children {
        if is_expr_node(child) {
            if target_node.is_none() {
                target_node = Some(child);
            } else if value_node.is_none() {
                value_node = Some(child);
            }
        } else if child.text.ends_with('=') && op_text.is_none() {
            op_text = Some(child.text.clone());
        }
    }

    let target = lower_expr(
        ctx,
        current_scope,
        target_node.expect("ICE: compound_assignment_expr must have a target expression"),
        body,
    );
    let value = lower_expr(
        ctx,
        current_scope,
        value_node.expect("ICE: compound_assignment_expr must have a value expression"),
        body,
    );

    let op = match op_text.as_deref() {
        Some("+=") => rv_hir::BinaryOp::Add,
        Some("-=") => rv_hir::BinaryOp::Sub,
        Some("*=") => rv_hir::BinaryOp::Mul,
        Some("/=") => rv_hir::BinaryOp::Div,
        Some("%=") => rv_hir::BinaryOp::Mod,
        Some("&=") => rv_hir::BinaryOp::BitAnd,
        Some("|=") => rv_hir::BinaryOp::BitOr,
        Some("^=") => rv_hir::BinaryOp::BitXor,
        Some("<<=") => rv_hir::BinaryOp::Shl,
        Some(">>=") => rv_hir::BinaryOp::Shr,
        other => panic!(
            "ICE: Unknown compound assignment operator '{:?}'. \
             All valid Rust compound assignment operators should be handled.",
            other
        ),
    };

    body.exprs.alloc(Expr::CompoundAssign {
        target,
        op,
        value,
        span: file_span,
    })
}

/// Lower a while loop expression
fn lower_while_expr(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    let mut condition_node = None;
    let mut body_node = None;
    let mut label = None;

    for child in &node.children {
        if child.kind == SyntaxKind::Block {
            body_node = Some(child);
        } else if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "label") {
            // Parse the label
            let text = child.text.trim_start_matches('\'');
            if !text.is_empty() {
                label = Some(ctx.intern(text));
            }
        } else if is_expr_node(child) && condition_node.is_none() {
            condition_node = Some(child);
        }
    }

    let condition = lower_expr(
        ctx,
        current_scope,
        condition_node.expect("ICE: while_expression must have a condition expression"),
        body,
    );
    let body_expr = lower_expr(
        ctx,
        current_scope,
        body_node.expect("ICE: while_expression must have a body block"),
        body,
    );

    body.exprs.alloc(Expr::WhileLoop {
        condition,
        body: body_expr,
        label,
        span: file_span,
    })
}

/// Lower a for expression by desugaring to a while loop.
///
/// `for i in start..end { body }` becomes:
/// ```text
/// {
///     let mut i = start;
///     while i < end {
///         body;
///         i = i + 1;
///     }
/// }
/// ```
fn lower_for_expr(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    // Create a new scope for the for-loop variable
    let for_scope = ctx.scope_tree.create_child(current_scope, node.span);

    // tree-sitter for_expression children:
    //   optional label, "for" keyword, pattern (identifier), "in" keyword, iterable expression, body block
    let mut pattern_name: Option<String> = None;
    let mut iterable_node: Option<&SyntaxNode> = None;
    let mut body_node: Option<&SyntaxNode> = None;
    let mut label: Option<rv_intern::Symbol> = None;

    for child in &node.children {
        if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "label") {
            // Parse the label
            let text = child.text.trim_start_matches('\'');
            if !text.is_empty() {
                label = Some(ctx.intern(text));
            }
        } else if child.kind == SyntaxKind::Identifier && pattern_name.is_none() {
            pattern_name = Some(child.text.clone());
        } else if child.kind == SyntaxKind::Block {
            body_node = Some(child);
        } else if is_expr_node(child) && iterable_node.is_none() && pattern_name.is_some() {
            iterable_node = Some(child);
        } else if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "range_expression")
            && iterable_node.is_none()
        {
            iterable_node = Some(child);
        }
    }
    // Label will be passed to the desugared while loop

    let var_name = pattern_name.unwrap_or_else(|| {
        panic!(
            "ICE: for_expression at {:?} has no loop variable identifier",
            file_span
        )
    });
    let iterable = iterable_node.unwrap_or_else(|| {
        panic!(
            "ICE: for_expression at {:?} has no iterable expression",
            file_span
        )
    });
    let loop_body = body_node
        .unwrap_or_else(|| panic!("ICE: for_expression at {:?} has no body block", file_span));

    // Register the loop variable in the for scope
    let var_sym = ctx.intern(&var_name);
    let symbol_id = ctx
        .symbols
        .add(var_sym, SymbolKind::Local, node.span, for_scope);
    ctx.scope_tree
        .add_symbol(for_scope, var_name.clone(), symbol_id);

    let local_id = LocalId(ctx.next_local_id);
    ctx.next_local_id += 1;
    let function_id = ctx
        .current_function_id
        .expect("lower_for_expr called outside function context");
    let def_id = DefId::Local {
        func: function_id,
        local: local_id,
    };
    ctx.symbols.set_def_id(symbol_id, def_id);
    ctx.symbol_defs.insert(symbol_id, def_id);

    // Parse the range expression to get start and end
    // tree-sitter range_expression has children: start, ".." or "..=", end
    let (start_expr, end_expr) = if matches!(&iterable.kind, SyntaxKind::Unknown(ref s) if s == "range_expression")
    {
        let mut start = None;
        let mut end = None;
        for range_child in &iterable.children {
            if is_expr_node(range_child) || range_child.kind == SyntaxKind::Literal {
                if start.is_none() {
                    start = Some(lower_expr(ctx, for_scope, range_child, body));
                } else {
                    end = Some(lower_expr(ctx, for_scope, range_child, body));
                }
            }
        }
        (
            start.unwrap_or_else(|| {
                body.exprs.alloc(Expr::Literal {
                    kind: LiteralKind::Integer(0, None),
                    span: file_span,
                })
            }),
            end.unwrap_or_else(|| {
                panic!("ICE: range_expression at {:?} has no end value", file_span)
            }),
        )
    } else {
        panic!(
            "ICE: for_expression at {:?} has non-range iterable. \
             Only range expressions (start..end) are currently supported.",
            file_span
        )
    };

    // Build: let mut i = start;
    let init_pattern = body.patterns.alloc(Pattern::Binding {
        name: var_sym,
        mutable: true,
        sub_pattern: None,
        span: file_span,
    });
    let let_stmt = body.stmts.alloc(Stmt::Let {
        pattern: init_pattern,
        ty: None,
        initializer: Some(start_expr),
        mutable: true,
        else_branch: None,
        span: file_span,
    });

    // Build: i < end (condition)
    let var_ref = body.exprs.alloc(Expr::Variable {
        name: var_sym,
        def: Some(def_id),
        span: file_span,
    });
    let condition = body.exprs.alloc(Expr::BinaryOp {
        op: rv_hir::BinaryOp::Lt,
        left: var_ref,
        right: end_expr,
        span: file_span,
    });

    // Build: body; i = i + 1;
    let loop_body_expr = lower_block(ctx, for_scope, loop_body, body);

    // i (for assignment target and increment)
    let var_ref_inc = body.exprs.alloc(Expr::Variable {
        name: var_sym,
        def: Some(def_id),
        span: file_span,
    });
    let one_literal = body.exprs.alloc(Expr::Literal {
        kind: LiteralKind::Integer(1, None),
        span: file_span,
    });
    let increment = body.exprs.alloc(Expr::BinaryOp {
        op: rv_hir::BinaryOp::Add,
        left: var_ref_inc,
        right: one_literal,
        span: file_span,
    });
    let var_ref_target = body.exprs.alloc(Expr::Variable {
        name: var_sym,
        def: Some(def_id),
        span: file_span,
    });
    let assign_increment = body.exprs.alloc(Expr::Assign {
        target: var_ref_target,
        value: increment,
        span: file_span,
    });

    // Build the compound body: { original_body; i = i + 1; }
    let body_stmt = body.stmts.alloc(Stmt::Expr {
        expr: loop_body_expr,
        span: file_span,
    });
    let inc_stmt = body.stmts.alloc(Stmt::Expr {
        expr: assign_increment,
        span: file_span,
    });
    let compound_body = body.exprs.alloc(Expr::Block {
        statements: vec![body_stmt, inc_stmt],
        expr: None,
        span: file_span,
    });

    // Build: while i < end { body; i = i + 1; }
    let while_expr = body.exprs.alloc(Expr::WhileLoop {
        condition,
        body: compound_body,
        label,
        span: file_span,
    });

    // Build the outer block: { let mut i = start; while ... }
    let while_stmt = body.stmts.alloc(Stmt::Expr {
        expr: while_expr,
        span: file_span,
    });

    body.exprs.alloc(Expr::Block {
        statements: vec![let_stmt, while_stmt],
        expr: None,
        span: file_span,
    })
}

/// Parse a loop label from a node (e.g., 'outer)
/// Returns the Symbol for the label name, excluding the leading quote
fn parse_label(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<rv_intern::Symbol> {
    // Look for a child node with kind "label" (tree-sitter type)
    for child in &node.children {
        if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "label") {
            // The label node contains "'" and an identifier
            // Extract the identifier part (text starts with ')
            let text = child.text.trim_start_matches('\'');
            if !text.is_empty() {
                return Some(ctx.intern(text));
            }
        }
    }
    None
}

/// Lower a loop expression (infinite loop)
fn lower_loop_expr(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    let mut loop_body_node = None;
    let label = parse_label(ctx, node);

    for child in &node.children {
        if child.kind == SyntaxKind::Block || is_expr_node(child) {
            loop_body_node = Some(child);
            break;
        }
    }

    let body_expr = lower_expr(
        ctx,
        current_scope,
        loop_body_node.expect("ICE: loop_expression must have a body block"),
        body,
    );

    body.exprs.alloc(Expr::Loop {
        body: body_expr,
        label,
        span: file_span,
    })
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
                } else if field_child.kind == SyntaxKind::Identifier
                    || matches!(&field_child.kind, SyntaxKind::Unknown(ref s) if s == "field_identifier")
                {
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

    // Regular function call or path-qualified call
    let mut callee = None;
    let mut callee_name_text: Option<String> = None;
    let mut path_call_info: Option<(Vec<InternedString>, InternedString)> = None;
    let mut type_args = Vec::new();

    // Parse type arguments (turbofish: `::<T, U>`)
    for child in &node.children {
        if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "type_arguments") {
            type_args = parse_type_arguments(ctx, child);
            break;
        }
    }

    for child in &node.children {
        if child.kind == SyntaxKind::Identifier && callee.is_none() && path_call_info.is_none() {
            // Save the name text before lowering — we may need it
            // to detect tuple struct construction (e.g., Wrapper(42)).
            callee_name_text = Some(child.text.clone());
            callee = Some(lower_expr(ctx, current_scope, child, body));
            break;
        } else if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "scoped_identifier") {
            let mut segments = Vec::new();
            collect_scoped_identifier_parts(child, &mut segments);

            if segments.len() >= 2 {
                let func_name = ctx.intern(&segments.pop().unwrap_or_else(|| {
                    panic!(
                        "ICE: scoped_identifier segments became empty after length check. \
                         collect_scoped_identifier_parts should produce at least 2 segments."
                    )
                }));
                let path: Vec<InternedString> = segments.iter().map(|s| ctx.intern(s)).collect();
                path_call_info = Some((path, func_name));
            } else if segments.len() == 1 {
                callee = Some(lower_expr(ctx, current_scope, child, body));
            }
            break;
        }
    }

    if let Some((path, function)) = path_call_info {
        // Check if this is an enum variant construction (e.g., Option::Some(42)).
        // Resolve the first path segment; if it refers to an enum type and the
        // function segment is a valid variant name, emit Expr::EnumVariant.
        if let Some(enum_variant_expr) =
            try_lower_enum_variant_call(ctx, current_scope, &path, function, &args, file_span, body)
        {
            enum_variant_expr
        } else {
            body.exprs.alloc(Expr::PathCall {
                path,
                function,
                args,
                span: file_span,
            })
        }
    } else if let Some(_callee_expr) = callee {
        // Check if this is a tuple struct construction (e.g., Wrapper(42)).
        // If the callee name matches a known tuple struct, produce
        // Expr::StructConstruct with synthetic field names "0", "1", etc.
        if let Some(ref name_text) = callee_name_text {
            let name_sym = ctx.intern(name_text);
            let tuple_struct_match = ctx
                .structs
                .values()
                .find(|s| s.name == name_sym && s.kind == StructKind::Tuple);
            if let Some(struct_def) = tuple_struct_match {
                let def_id = struct_def.id;
                let struct_name = struct_def.name;
                let fields: Vec<(InternedString, ExprId)> = args
                    .iter()
                    .enumerate()
                    .map(|(i, &arg)| (ctx.intern(&i.to_string()), arg))
                    .collect();
                return body.exprs.alloc(Expr::StructConstruct {
                    struct_name,
                    def: Some(def_id),
                    fields,
                    span: file_span,
                });
            }
        }
        body.exprs.alloc(Expr::Call {
            callee: _callee_expr,
            args,
            type_args,
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

/// Attempt to lower a path-qualified call as an enum variant construction.
///
/// Given `path = ["Option"]` and `variant_name = Some`, checks whether
/// "Option" resolves to an enum type and "Some" is a valid variant.
/// Returns `Some(ExprId)` if it is an enum variant, `None` otherwise
/// (so the caller falls back to `PathCall`).
fn try_lower_enum_variant_call(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    path: &[InternedString],
    variant_name: InternedString,
    args: &[ExprId],
    span: FileSpan,
    body: &mut Body,
) -> Option<ExprId> {
    if path.is_empty() {
        return None;
    }

    // For single-segment paths (e.g., Option::Some), resolve in the current scope.
    // For multi-segment paths (e.g., mymod::Option::Some), walk through module scopes.
    let (enum_name, type_def_id) = if path.len() == 1 {
        let enum_name = path[0];
        let enum_name_str = ctx.interner.resolve(&enum_name);
        let sym_id = ctx.scope_tree.resolve(current_scope, &enum_name_str)?;
        let def_id = ctx.symbol_defs.get(&sym_id)?;
        let tid = match def_id {
            DefId::Type(tid) => *tid,
            _ => return None,
        };
        (enum_name, tid)
    } else {
        // Multi-segment path: walk through modules to reach the enum.
        // path = ["mod1", "mod2", "EnumName"], variant_name = "Variant"
        // Resolve all segments except the last as modules, then resolve the
        // last segment as an enum type.
        let module_segments = &path[..path.len() - 1];
        let enum_name = path[path.len() - 1];

        // Start by resolving the first module segment in the current scope
        let first_name_str = ctx.interner.resolve(&module_segments[0]);
        let first_sym = ctx.scope_tree.resolve(current_scope, &first_name_str)?;
        let first_def = ctx.symbol_defs.get(&first_sym)?;
        let mut current_module_id = match first_def {
            DefId::Module(mid) => *mid,
            _ => return None,
        };

        // Walk through remaining module segments
        for &segment in &module_segments[1..] {
            let segment_str = ctx.interner.resolve(&segment);
            let module_scope = *ctx.module_scopes.get(&current_module_id)?;
            let sym_id = ctx
                .scope_tree
                .resolve_in_scope(module_scope, &segment_str)?;
            let def_id = ctx.symbol_defs.get(&sym_id)?;
            current_module_id = match def_id {
                DefId::Module(mid) => *mid,
                _ => return None,
            };
        }

        // Resolve the enum name within the final module's scope
        let module_scope = *ctx.module_scopes.get(&current_module_id)?;
        let enum_name_str = ctx.interner.resolve(&enum_name);
        let sym_id = ctx
            .scope_tree
            .resolve_in_scope(module_scope, &enum_name_str)?;
        let def_id = ctx.symbol_defs.get(&sym_id)?;
        let tid = match def_id {
            DefId::Type(tid) => *tid,
            _ => return None,
        };
        (enum_name, tid)
    };

    // Check that this TypeDefId actually refers to an enum (not a struct)
    if !ctx.enums.contains_key(&type_def_id) {
        return None;
    }

    Some(body.exprs.alloc(Expr::EnumVariant {
        enum_name,
        variant: variant_name,
        def: Some(type_def_id),
        fields: args.to_vec(),
        span,
    }))
}

/// Lower a scoped identifier expression as a unit enum variant (e.g., `Status::Active`).
///
/// Returns `Some(ExprId)` if the scoped identifier resolves to an enum variant,
/// `None` otherwise.
fn try_lower_unit_enum_variant(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> Option<ExprId> {
    let file_span = ctx.file_span(node);
    let mut segments = Vec::new();
    collect_scoped_identifier_parts(node, &mut segments);

    if segments.len() < 2 {
        return None;
    }

    // Last segment is the variant name, second-to-last is the enum name.
    let variant_name_str = &segments[segments.len() - 1];

    let type_def_id = if segments.len() == 2 {
        // Simple case: EnumName::Variant
        let enum_name_str = &segments[0];
        let sym_id = ctx.scope_tree.resolve(current_scope, enum_name_str)?;
        let def_id = ctx.symbol_defs.get(&sym_id)?;
        match def_id {
            DefId::Type(tid) => *tid,
            _ => return None,
        }
    } else {
        // Multi-segment: mod1::mod2::EnumName::Variant
        // Walk through modules, then resolve the enum in the final module's scope.
        let module_segments = &segments[..segments.len() - 2];
        let enum_name_str = &segments[segments.len() - 2];

        let first_sym = ctx.scope_tree.resolve(current_scope, &module_segments[0])?;
        let first_def = ctx.symbol_defs.get(&first_sym)?;
        let mut current_module_id = match first_def {
            DefId::Module(mid) => *mid,
            _ => return None,
        };

        for segment in &module_segments[1..] {
            let module_scope = *ctx.module_scopes.get(&current_module_id)?;
            let sym_id = ctx.scope_tree.resolve_in_scope(module_scope, segment)?;
            let def_id = ctx.symbol_defs.get(&sym_id)?;
            current_module_id = match def_id {
                DefId::Module(mid) => *mid,
                _ => return None,
            };
        }

        let module_scope = *ctx.module_scopes.get(&current_module_id)?;
        let sym_id = ctx
            .scope_tree
            .resolve_in_scope(module_scope, enum_name_str)?;
        let def_id = ctx.symbol_defs.get(&sym_id)?;
        match def_id {
            DefId::Type(tid) => *tid,
            _ => return None,
        }
    };

    // Check that this TypeDefId actually refers to an enum
    if !ctx.enums.contains_key(&type_def_id) {
        return None;
    }

    let enum_name = ctx.intern(&segments[segments.len() - 2]);
    let variant = ctx.intern(variant_name_str);

    Some(body.exprs.alloc(Expr::EnumVariant {
        enum_name,
        variant,
        def: Some(type_def_id),
        fields: vec![],
        span: file_span,
    }))
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
        if child.kind == SyntaxKind::Identifier
            || matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "field_identifier")
        {
            if base.is_none() {
                // First identifier is the base expression
                base = Some(lower_expr(ctx, current_scope, child, body));
            } else {
                // Second identifier is the field name
                field_name = Some(ctx.intern(&child.text));
            }
        } else if base.is_some()
            && field_name.is_none()
            && child.kind == SyntaxKind::Literal
            && child.text.chars().all(|c| c.is_ascii_digit())
        {
            // Numeric tuple field access (e.g., w.0, w.1).
            // tree-sitter maps integer_literal → SyntaxKind::Literal.
            field_name = Some(ctx.intern(&child.text));
        } else if is_expr_node(child) && base.is_none() {
            base = Some(lower_expr(ctx, current_scope, child, body));
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
        if (child.kind == SyntaxKind::Identifier || child.kind == SyntaxKind::Type)
            && struct_name.is_none()
        {
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
        let def = ctx
            .scope_tree
            .resolve(current_scope, &ctx.interner.resolve(&name));
        body.exprs.alloc(Expr::StructConstruct {
            struct_name: name,
            def: def.and_then(|sym_id| {
                ctx.symbol_defs
                    .get(&sym_id)
                    .and_then(|def_id| match def_id {
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
        if (child.kind == SyntaxKind::Identifier
            || matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "field_identifier"))
            && field_name.is_none()
        {
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

/// Parse an integer type suffix, returning (numeric_part, optional width+signedness).
fn parse_int_suffix(text: &str) -> (&str, Option<(rv_hir::IntWidth, rv_hir::Signedness)>) {
    use rv_hir::{IntWidth, Signedness};
    let suffixes: &[(&str, IntWidth, Signedness)] = &[
        ("i128", IntWidth::I128, Signedness::Signed),
        ("u128", IntWidth::I128, Signedness::Unsigned),
        ("isize", IntWidth::Isize, Signedness::Signed),
        ("usize", IntWidth::Isize, Signedness::Unsigned),
        ("i64", IntWidth::I64, Signedness::Signed),
        ("u64", IntWidth::I64, Signedness::Unsigned),
        ("i32", IntWidth::I32, Signedness::Signed),
        ("u32", IntWidth::I32, Signedness::Unsigned),
        ("i16", IntWidth::I16, Signedness::Signed),
        ("u16", IntWidth::I16, Signedness::Unsigned),
        ("i8", IntWidth::I8, Signedness::Signed),
        ("u8", IntWidth::I8, Signedness::Unsigned),
    ];
    for &(suffix, width, sign) in suffixes {
        if text.ends_with(suffix) {
            return (&text[..text.len() - suffix.len()], Some((width, sign)));
        }
    }
    (text, None)
}

/// Parse a float type suffix, returning (numeric_part, optional width).
fn parse_float_suffix(text: &str) -> (&str, Option<rv_hir::FloatWidth>) {
    use rv_hir::FloatWidth;
    if text.ends_with("f64") {
        (&text[..text.len() - 3], Some(FloatWidth::F64))
    } else if text.ends_with("f32") {
        (&text[..text.len() - 3], Some(FloatWidth::F32))
    } else {
        (text, None)
    }
}

/// Parse a literal from text.
///
/// Supports: integer literals (decimal, hex, octal, binary) with optional type
/// suffixes, float literals with optional suffixes, booleans, character literals,
/// string literals, and underscore separators.
fn parse_literal(text: &str) -> LiteralKind {
    // Boolean literals
    if text == "true" {
        return LiteralKind::Bool(true);
    }
    if text == "false" {
        return LiteralKind::Bool(false);
    }

    // Character literals: 'a', '\n', '\u{1F600}'
    if text.starts_with('\'') && text.ends_with('\'') && text.len() >= 3 {
        let inner = &text[1..text.len() - 1];
        let ch = parse_char_escape(inner);
        return LiteralKind::Char(ch);
    }

    // String literals
    if text.starts_with('"') && text.ends_with('"') && text.len() >= 2 {
        let content = &text[1..text.len() - 1];
        return LiteralKind::String(parse_string_escapes(content));
    }

    // Byte string literals: b"..." -> treat as string for now
    if text.starts_with("b\"") && text.ends_with('"') && text.len() >= 3 {
        let content = &text[2..text.len() - 1];
        return LiteralKind::String(parse_string_escapes(content));
    }

    // Raw byte string literals: br"..." or br#"..."# -> extract the content
    if text.starts_with("br") {
        // Count the # characters after 'br'
        let hash_count = text[2..].chars().take_while(|&c| c == '#').count();
        let prefix_len = 3 + hash_count; // br + #...# + "
        let suffix_len = 1 + hash_count; // " + #...#
        if text.len() >= prefix_len + suffix_len {
            let content = &text[prefix_len..text.len() - suffix_len];
            return LiteralKind::String(content.to_string());
        }
    }

    // Raw string literals: r"..." or r#"..."# -> extract the content
    if text.starts_with('r') && !text.starts_with("return") {
        // Count the # characters
        let hash_count = text[1..].chars().take_while(|&c| c == '#').count();
        let prefix_len = 2 + hash_count; // r + #...# + "
        let suffix_len = 1 + hash_count; // " + #...#
        if text.len() >= prefix_len + suffix_len {
            let content = &text[prefix_len..text.len() - suffix_len];
            return LiteralKind::String(content.to_string());
        }
    }

    // Byte literals: b'x' -> treat as char for now
    if text.starts_with("b'") && text.ends_with('\'') && text.len() >= 4 {
        let inner = &text[2..text.len() - 1];
        let ch = parse_char_escape(inner);
        return LiteralKind::Char(ch);
    }

    // Numeric literals — strip underscore separators
    let cleaned = text.replace('_', "");
    let cleaned = cleaned.as_str();

    // Check for float suffix first (before int suffix, since "f32"/"f64" overlap with nothing)
    let (float_num, float_suffix) = parse_float_suffix(cleaned);
    if float_suffix.is_some()
        || float_num.contains('.')
        || (float_num.contains('e') || float_num.contains('E')) && !float_num.starts_with("0x")
    {
        if let Ok(value) = float_num.parse::<f64>() {
            return LiteralKind::Float(value, float_suffix);
        }
    }

    // Integer literals: hex, octal, binary, decimal with optional type suffix
    let (num_str, int_suffix) = parse_int_suffix(cleaned);

    // Hex: 0xFF
    if num_str.starts_with("0x") || num_str.starts_with("0X") {
        if let Ok(value) = i64::from_str_radix(&num_str[2..], 16) {
            return LiteralKind::Integer(value, int_suffix);
        }
    }
    // Octal: 0o77
    if num_str.starts_with("0o") || num_str.starts_with("0O") {
        if let Ok(value) = i64::from_str_radix(&num_str[2..], 8) {
            return LiteralKind::Integer(value, int_suffix);
        }
    }
    // Binary: 0b1010
    if num_str.starts_with("0b") || num_str.starts_with("0B") {
        if let Ok(value) = i64::from_str_radix(&num_str[2..], 2) {
            return LiteralKind::Integer(value, int_suffix);
        }
    }
    // Decimal integer
    if let Ok(value) = num_str.parse::<i64>() {
        return LiteralKind::Integer(value, int_suffix);
    }
    // Try as float (e.g., bare "3.14" without suffix)
    if let Ok(value) = num_str.parse::<f64>() {
        return LiteralKind::Float(value, None);
    }

    panic!(
        "ICE: Failed to parse literal from tree-sitter node text: {:?}. \
         All tree-sitter literal nodes must be parseable.",
        text
    );
}

/// Parse a character escape sequence.
fn parse_char_escape(s: &str) -> char {
    if s.starts_with('\\') {
        match s.as_bytes().get(1) {
            Some(b'n') => '\n',
            Some(b'r') => '\r',
            Some(b't') => '\t',
            Some(b'\\') => '\\',
            Some(b'\'') => '\'',
            Some(b'"') => '"',
            Some(b'0') => '\0',
            Some(b'x') => {
                // \xNN
                u8::from_str_radix(&s[2..], 16)
                    .map(|b| b as char)
                    .unwrap_or('\u{FFFD}')
            }
            Some(b'u') => {
                // \u{NNNN}
                let hex = s.trim_start_matches("\\u{").trim_end_matches('}');
                u32::from_str_radix(hex, 16)
                    .ok()
                    .and_then(char::from_u32)
                    .unwrap_or('\u{FFFD}')
            }
            _ => s.chars().last().unwrap_or('\u{FFFD}'),
        }
    } else {
        s.chars().next().unwrap_or('\u{FFFD}')
    }
}

/// Parse escape sequences in a string literal.
///
/// Handles: \n, \r, \t, \\, \', \", \0, \xNN, \u{NNNN}
fn parse_string_escapes(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '\\' {
            match chars.next() {
                Some('n') => result.push('\n'),
                Some('r') => result.push('\r'),
                Some('t') => result.push('\t'),
                Some('\\') => result.push('\\'),
                Some('\'') => result.push('\''),
                Some('"') => result.push('"'),
                Some('0') => result.push('\0'),
                Some('x') => {
                    // \xNN - two hex digits
                    let mut hex = String::with_capacity(2);
                    if let Some(d1) = chars.next() {
                        hex.push(d1);
                    }
                    if let Some(d2) = chars.next() {
                        hex.push(d2);
                    }
                    if let Ok(byte) = u8::from_str_radix(&hex, 16) {
                        result.push(byte as char);
                    } else {
                        result.push('\u{FFFD}');
                    }
                }
                Some('u') => {
                    // \u{NNNN} - unicode escape
                    if chars.next() == Some('{') {
                        let mut hex = String::new();
                        while let Some(&c) = chars.peek() {
                            if c == '}' {
                                chars.next();
                                break;
                            }
                            hex.push(chars.next().unwrap_or(' '));
                        }
                        if let Some(cp) = u32::from_str_radix(&hex, 16)
                            .ok()
                            .and_then(char::from_u32)
                        {
                            result.push(cp);
                        } else {
                            result.push('\u{FFFD}');
                        }
                    } else {
                        result.push('\u{FFFD}');
                    }
                }
                Some(other) => {
                    // Unknown escape - keep as-is
                    result.push('\\');
                    result.push(other);
                }
                None => {
                    // Trailing backslash
                    result.push('\\');
                }
            }
        } else {
            result.push(ch);
        }
    }

    result
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
        // Check if this looks like an operator (typically 1-2 char operators like +, -, *, /, ==, etc.)
        if is_binary_operator(&child.text) && operator.is_none() {
            operator = Some(parse_binary_operator(&child.text));
        }
        // Otherwise, if it's not a delimiter/keyword, treat it as an expression
        else if !is_keyword_or_delimiter(&child.kind, &child.text) {
            if left_expr.is_none() {
                left_expr = Some(lower_expr(ctx, current_scope, child, body));
            } else if operator.is_some() && right_expr.is_none() {
                right_expr = Some(lower_expr(ctx, current_scope, child, body));
            }
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
        panic!(
            "ICE: Failed to parse binary expression at {:?}. \
             Parser should produce valid binary_expression nodes with left operand, operator, and right operand. \
             Found: left={:?}, op={:?}, right={:?}",
            file_span, left_expr.is_some(), operator.is_some(), right_expr.is_some()
        )
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
        other => panic!(
            "ICE: Unknown binary operator '{}'. \
             All valid Rust binary operators should be handled.",
            other
        ),
    }
}

/// Lower an if expression (handles both `if <expr>` and `if let <pattern> = <expr>`)
fn lower_if_expr(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    let mut condition = None;
    let mut let_condition: Option<(PatternId, ExprId)> = None;
    let mut then_branch = None;
    let mut else_branch = None;

    // Parse children to find condition, then block, and optional else block
    let mut found_condition = false;
    let mut found_then = false;

    for child in &node.children {
        // Check for `if let` pattern: let_condition node
        if !found_condition {
            if let SyntaxKind::Unknown(ref name) = child.kind {
                if name == "let_condition" {
                    // Parse the let_condition: pattern = value
                    let_condition = lower_let_condition(ctx, current_scope, child, body);
                    found_condition = true;
                    continue;
                }
            }
        }

        if !found_condition && is_expr_node(child) {
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
                    // Extract the block or nested if expression from the else_clause wrapper
                    for else_child in &child.children {
                        if else_child.kind == SyntaxKind::Block {
                            else_branch = Some(lower_expr(ctx, current_scope, else_child, body));
                            break;
                        } else if else_child.kind == SyntaxKind::If {
                            // else if case
                            else_branch = Some(lower_if_expr(ctx, current_scope, else_child, body));
                            break;
                        } else if let SyntaxKind::Unknown(ref name) = else_child.kind {
                            if name == "if_expression" {
                                else_branch =
                                    Some(lower_if_expr(ctx, current_scope, else_child, body));
                                break;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Return IfLet if we found a let_condition, otherwise return If
    if let Some((pattern, value)) = let_condition {
        if let Some(then_expr) = then_branch {
            return body.exprs.alloc(Expr::IfLet {
                pattern,
                value,
                then_branch: then_expr,
                else_branch,
                span: file_span,
            });
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
        panic!(
            "ICE: Failed to parse if expression at {:?}. \
             Parser should produce valid if_expression nodes with condition and then branch. \
             Found: condition={:?}, let_condition={:?}, then={:?}",
            file_span,
            condition.is_some(),
            let_condition.is_some(),
            then_branch.is_some()
        )
    }
}

/// Lower a let_condition node (from `if let` or `while let`)
/// Returns (pattern, value_expr) if successful
fn lower_let_condition(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> Option<(PatternId, ExprId)> {
    // let_condition structure:
    //   let: "let"
    //   <pattern>: tuple_struct_pattern, identifier, etc.
    //   =: "="
    //   <value>: identifier, expression, etc.

    let mut pattern = None;
    let mut value = None;
    let mut found_eq = false;

    for child in &node.children {
        if child.text == "let" {
            continue;
        }
        if child.text == "=" {
            found_eq = true;
            continue;
        }

        if !found_eq {
            // Before '=' - this is the pattern
            if pattern.is_none() {
                pattern = lower_pattern(ctx, current_scope, child, body);
            }
        } else {
            // After '=' - this is the value expression
            if value.is_none() && is_expr_node(child) {
                value = Some(lower_expr(ctx, current_scope, child, body));
            }
        }
    }

    match (pattern, value) {
        (Some(p), Some(v)) => Some((p, v)),
        _ => None,
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
        // Skip the 'match' keyword and braces - anything else before match_block is the scrutinee
        if !found_scrutinee && !is_keyword_or_delimiter(&child.kind, &child.text) {
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
                                if let Some(arm) =
                                    lower_match_arm(ctx, current_scope, arm_child, body)
                                {
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
        panic!(
            "ICE: Failed to parse match expression at {:?}. \
             Parser should produce valid match_expression nodes with scrutinee. \
             Found: scrutinee={:?}",
            file_span,
            scrutinee.is_some()
        )
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

                // ARCHITECTURE: Register all pattern bindings in the scope
                // before lowering the arm body so they can be resolved
                register_pattern_bindings(ctx, current_scope, pat, body, child.span);
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

/// Register all bindings in a pattern into the symbol table
fn register_pattern_bindings(
    ctx: &mut LoweringContext,
    scope: ScopeId,
    pattern_id: PatternId,
    body: &Body,
    span: rv_span::Span,
) {
    let pattern = &body.patterns[pattern_id];

    match pattern {
        Pattern::Binding { name, .. } => {
            // Register this binding
            let name_str = ctx.interner.resolve(name).to_string();
            let symbol_id = ctx.symbols.add(*name, SymbolKind::Local, span, scope);
            ctx.scope_tree.add_symbol(scope, name_str, symbol_id);

            // Create a LocalId and DefId for this binding
            let local_id = LocalId(ctx.next_local_id);
            ctx.next_local_id += 1;
            let function_id = ctx
                .current_function_id
                .expect("register_pattern_bindings called outside function context");
            let def_id = DefId::Local {
                func: function_id,
                local: local_id,
            };
            ctx.symbols.set_def_id(symbol_id, def_id);
            ctx.symbol_defs.insert(symbol_id, def_id);
        }
        Pattern::Tuple { patterns, .. } => {
            // Recursively register bindings in tuple elements
            for &elem_id in patterns {
                register_pattern_bindings(ctx, scope, elem_id, body, span);
            }
        }
        Pattern::Struct { fields, .. } => {
            // Recursively register bindings in struct fields
            for (_, field_pat_id) in fields {
                register_pattern_bindings(ctx, scope, *field_pat_id, body, span);
            }
        }
        Pattern::Enum { sub_patterns, .. } => {
            // Recursively register bindings in enum sub-patterns
            for &sub_pat_id in sub_patterns {
                register_pattern_bindings(ctx, scope, sub_pat_id, body, span);
            }
        }
        Pattern::Or { patterns, .. } => {
            // Register bindings from all alternatives (must be consistent)
            for &pat_id in patterns {
                register_pattern_bindings(ctx, scope, pat_id, body, span);
            }
        }
        Pattern::Range { .. } | Pattern::Wildcard { .. } | Pattern::Literal { .. } => {
            // These patterns don't introduce bindings
        }
        Pattern::Slice {
            prefix,
            rest,
            suffix,
            ..
        } => {
            // Recursively register bindings in slice pattern elements
            for &elem_id in prefix {
                register_pattern_bindings(ctx, scope, elem_id, body, span);
            }
            if let Some(rest_pat_id) = rest {
                register_pattern_bindings(ctx, scope, *rest_pat_id, body, span);
            }
            for &elem_id in suffix {
                register_pattern_bindings(ctx, scope, elem_id, body, span);
            }
        }
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
                        return Some(body.patterns.alloc(Pattern::Literal {
                            kind,
                            span: file_span,
                        }));
                    }
                    SyntaxKind::Identifier => {
                        let name = child.text.clone();
                        if name == "_" {
                            return Some(
                                body.patterns.alloc(Pattern::Wildcard { span: file_span }),
                            );
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
                    SyntaxKind::Unknown(ref child_name) if child_name == "|" => {
                        // Pipe separator in or-pattern - skip it
                        continue;
                    }
                    SyntaxKind::Unknown(ref child_name)
                        if child_name == "char_literal"
                            || child_name == "integer_literal"
                            || child_name == "float_literal"
                            || child_name == "negative_literal" =>
                    {
                        // Literal patterns from tree-sitter (char_literal for b'\t', negative_literal for -1, etc.)
                        let kind = parse_literal(&child.text);
                        return Some(body.patterns.alloc(Pattern::Literal {
                            kind,
                            span: file_span,
                        }));
                    }
                    _ => {
                        // Try to recursively parse complex patterns (tuple_struct_pattern, etc.)
                        if let Some(pat_id) = lower_pattern(ctx, current_scope, child, body) {
                            return Some(pat_id);
                        }
                        continue;
                    }
                }
            }
            // No pattern found in match_pattern
            panic!(
                "ICE: match_pattern node at {:?} contains no valid patterns. \
                 Parser should ensure match_pattern nodes have at least one pattern.",
                file_span
            )
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
            Pattern::Literal {
                kind,
                span: file_span,
            }
        }
        SyntaxKind::Unknown(ref name) if name == "tuple_pattern" => {
            // Lower tuple pattern elements
            let mut patterns = Vec::new();
            for child in &node.children {
                // Skip punctuation like '(', ')', ','
                if !matches!(child.text.as_str(), "(" | ")" | "," | "{" | "}") {
                    if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                        patterns.push(pat);
                    }
                }
            }
            Pattern::Tuple {
                patterns,
                span: file_span,
            }
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
                let def_id = ctx
                    .structs
                    .iter()
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
                        // Skip if we already have a variant name (this is a pattern binding inside parens)
                        if variant_name.is_some() {
                            // This is a pattern binding, handle it as a sub-pattern
                            if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                                sub_patterns.push(pat);
                            }
                            continue;
                        }

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
                    SyntaxKind::Unknown(ref kind) if kind == "type_identifier" => {
                        // tree-sitter uses type_identifier for type names like `Some`
                        if variant_name.is_none() {
                            variant_name = Some(child.text.clone());
                        }
                    }
                    SyntaxKind::Unknown(ref kind)
                        if kind == "scoped_identifier" || kind == "scoped_type_identifier" =>
                    {
                        // Handle Option::Some or path::to::Variant style
                        let mut parts = Vec::new();
                        for scope_child in &child.children {
                            if matches!(scope_child.kind, SyntaxKind::Identifier)
                                || matches!(&scope_child.kind, SyntaxKind::Unknown(ref k) if k == "type_identifier" || k == "identifier")
                            {
                                parts.push(scope_child.text.clone());
                            }
                        }
                        if parts.len() >= 2 {
                            enum_name = Some(parts[parts.len() - 2].clone());
                            variant_name = Some(parts[parts.len() - 1].clone());
                        } else if parts.len() == 1 {
                            variant_name = Some(parts[0].clone());
                        }
                    }
                    SyntaxKind::Unknown(ref kind)
                        if kind == "tuple_pattern" || kind == "field_pattern_list" =>
                    {
                        // ARCHITECTURE: Enum variant arguments are wrapped in container nodes
                        // like tuple_pattern. We need to unwrap and parse the actual patterns inside.
                        for grandchild in &child.children {
                            // Skip punctuation like '(' and ')'
                            if !matches!(grandchild.text.as_str(), "(" | ")" | "," | "{" | "}") {
                                if let Some(pat) =
                                    lower_pattern(ctx, current_scope, grandchild, body)
                                {
                                    sub_patterns.push(pat);
                                }
                            }
                        }
                    }
                    _ => {
                        // Try to parse sub-patterns directly, but skip delimiters
                        if !matches!(
                            child.text.as_str(),
                            "(" | ")" | "," | "{" | "}" | "::" | "|"
                        ) {
                            if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                                sub_patterns.push(pat);
                            }
                        }
                    }
                }
            }

            let variant_sym = match variant_name {
                Some(v) => ctx.intern(&v),
                None => {
                    ctx.report_unhandled(
                        DiagnosticSeverity::Warning,
                        format!(
                            "tuple_struct_pattern at {:?} has no variant name",
                            file_span
                        ),
                        file_span,
                    );
                    return None;
                }
            };

            // Check if this is a tuple struct pattern (e.g., Wrapper(x))
            // rather than an enum variant pattern (e.g., Some(x)).
            // When there's no qualified path (no enum_name), try matching
            // against known tuple structs first.
            let is_tuple_struct = enum_name.is_none()
                && ctx
                    .structs
                    .values()
                    .any(|s| s.name == variant_sym && s.kind == StructKind::Tuple);

            if is_tuple_struct {
                // Look up the struct definition
                let def_id = ctx
                    .structs
                    .iter()
                    .find(|(_, s)| s.name == variant_sym && s.kind == StructKind::Tuple)
                    .map(|(id, _)| *id);

                // Create a Named type for the struct
                let ty_id = ctx.types.alloc(Type::Named {
                    name: variant_sym,
                    def: def_id,
                    args: Vec::new(),
                    span: file_span,
                });

                // Map positional sub-patterns to synthetic field names "0", "1", ...
                let fields: Vec<(InternedString, PatternId)> = sub_patterns
                    .iter()
                    .enumerate()
                    .map(|(i, &pat)| (ctx.intern(&i.to_string()), pat))
                    .collect();

                Pattern::Struct {
                    ty: ty_id,
                    fields,
                    span: file_span,
                }
            } else {
                // When unqualified (e.g., `Some(x)` instead of `Option::Some(x)`),
                // use the variant name as the enum name as well
                let enum_sym = match enum_name {
                    Some(e) => ctx.intern(&e),
                    None => variant_sym,
                };

                // Look up the enum definition
                let def_id = ctx
                    .enums
                    .iter()
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
        }
        SyntaxKind::Unknown(ref name) if name == "or_pattern" => {
            // Parse or-pattern: pat1 | pat2 | pat3
            let mut patterns = Vec::new();
            for child in &node.children {
                // Skip the '|' separators
                if matches!(child.kind, SyntaxKind::Unknown(_))
                    || matches!(child.kind, SyntaxKind::Identifier | SyntaxKind::Literal)
                {
                    if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                        patterns.push(pat);
                    }
                }
            }
            Pattern::Or {
                patterns,
                span: file_span,
            }
        }
        SyntaxKind::Unknown(ref name) if name == "range_pattern" => {
            // Parse range pattern: start..end or start..=end
            let mut start = None;
            let mut end = None;
            let mut inclusive = false;

            for child in &node.children {
                // Handle SyntaxKind::Literal or tree-sitter's integer_literal, char_literal, etc.
                let is_literal = matches!(child.kind, SyntaxKind::Literal)
                    || matches!(&child.kind, SyntaxKind::Unknown(ref s) if
                        s == "integer_literal" || s == "char_literal" || s == "float_literal");

                if is_literal {
                    let lit = parse_literal(&child.text);
                    if start.is_none() {
                        start = Some(lit);
                    } else {
                        end = Some(lit);
                    }
                } else if let SyntaxKind::Unknown(ref op) = child.kind {
                    if op == "..=" {
                        inclusive = true;
                    } else if op == ".." {
                        inclusive = false;
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
            let sub_pat_id =
                sub_pattern_node.and_then(|node| lower_pattern(ctx, current_scope, node, body));

            // Create binding pattern with sub-pattern
            if let Some(name) = binding_name {
                Pattern::Binding {
                    name,
                    mutable: false,
                    sub_pattern: sub_pat_id.map(Box::new),
                    span: file_span,
                }
            } else {
                panic!(
                    "ICE: identifier_pattern node at {:?} has no identifier. \
                     Parser should ensure identifier_pattern nodes contain valid identifiers.",
                    file_span
                )
            }
        }
        SyntaxKind::Unknown(ref name) if name == "_" => {
            // Wildcard pattern from tree-sitter
            Pattern::Wildcard { span: file_span }
        }
        SyntaxKind::Unknown(ref name) if name == "scoped_identifier" => {
            // scoped_identifier is used for enum patterns like Option::Some
            // This should be handled by the enum_variant_pattern code above
            // If we reach here, just treat it as an enum pattern
            // Extract the path components
            let text = &node.text;
            if let Some((enum_name, variant_name)) = text.rsplit_once("::") {
                let enum_sym = ctx.intern(enum_name);
                let variant_sym = ctx.intern(variant_name);

                // Look up the enum definition
                let def = ctx.scope_tree.resolve(current_scope, enum_name);
                let type_def = def.and_then(|sym_id| {
                    ctx.symbol_defs
                        .get(&sym_id)
                        .and_then(|def_id| match def_id {
                            DefId::Type(type_id) => Some(*type_id),
                            _ => None,
                        })
                });

                Pattern::Enum {
                    enum_name: enum_sym,
                    variant: variant_sym,
                    def: type_def,
                    sub_patterns: Vec::new(),
                    span: file_span,
                }
            } else {
                // No :: separator, treat as a simple binding
                Pattern::Binding {
                    name: ctx.intern(text),
                    mutable: false,
                    sub_pattern: None,
                    span: file_span,
                }
            }
        }
        SyntaxKind::Unknown(ref name) if name == "ref_pattern" => {
            // `ref x` pattern - creates a reference binding
            // Find the identifier child
            let mut binding_name = None;
            for child in &node.children {
                if child.kind == SyntaxKind::Identifier {
                    binding_name = Some(ctx.intern(&child.text));
                }
            }
            if let Some(name) = binding_name {
                Pattern::Binding {
                    name,
                    mutable: false,
                    sub_pattern: None,
                    span: file_span,
                }
            } else {
                // ref with a more complex pattern — recurse into children
                for child in &node.children {
                    if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                        return Some(pat);
                    }
                }
                Pattern::Wildcard { span: file_span }
            }
        }
        SyntaxKind::Unknown(ref name) if name == "mut_pattern" => {
            // `mut x` pattern - mutable binding
            let mut binding_name = None;
            for child in &node.children {
                if child.kind == SyntaxKind::Identifier {
                    binding_name = Some(ctx.intern(&child.text));
                }
            }
            if let Some(name) = binding_name {
                Pattern::Binding {
                    name,
                    mutable: true,
                    sub_pattern: None,
                    span: file_span,
                }
            } else {
                Pattern::Wildcard { span: file_span }
            }
        }
        SyntaxKind::Unknown(ref name) if name == "slice_pattern" => {
            // Slice patterns: [a, b, ..], [a, b, rest @ ..], [a, .., z], etc.
            // Structure: prefix patterns, optional rest pattern (..), suffix patterns
            let mut prefix: Vec<PatternId> = Vec::new();
            let mut suffix: Vec<PatternId> = Vec::new();
            let mut rest: Option<PatternId> = None;
            let mut seen_rest = false;

            for child in &node.children {
                // Skip punctuation
                if matches!(&child.kind, SyntaxKind::Unknown(k) if k == "[" || k == "]" || k == ",") {
                    continue;
                }

                // Check for rest pattern (..)
                if matches!(&child.kind, SyntaxKind::Unknown(k) if k == "rest_pattern") {
                    seen_rest = true;
                    // Check if there's a binding (e.g., `rest @ ..`)
                    for grandchild in &child.children {
                        if grandchild.kind == SyntaxKind::Identifier {
                            let name = ctx.intern(&grandchild.text);
                            rest = Some(body.patterns.alloc(Pattern::Binding {
                                name,
                                mutable: false,
                                sub_pattern: None,
                                span: ctx.file_span(grandchild),
                            }));
                            break;
                        }
                    }
                    continue;
                }

                // Try to parse as pattern
                if let Some(pat_id) = lower_pattern(ctx, current_scope, child, body) {
                    if seen_rest {
                        suffix.push(pat_id);
                    } else {
                        prefix.push(pat_id);
                    }
                }
            }

            Pattern::Slice {
                prefix,
                rest,
                suffix,
                span: file_span,
            }
        }
        SyntaxKind::Unknown(ref name) if name == "remaining_field_pattern" => {
            // `..` in struct patterns - treat as wildcard
            Pattern::Wildcard { span: file_span }
        }
        SyntaxKind::Unknown(ref name) if name == "reference_pattern" => {
            // `&x` or `&mut x` pattern - parse inner pattern
            for child in &node.children {
                if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                    return Some(pat);
                }
            }
            Pattern::Wildcard { span: file_span }
        }
        SyntaxKind::Unknown(ref name) if name == "captured_pattern" => {
            // `id @ pattern` — alias pattern; tree-sitter sometimes uses this name
            let mut binding_name = None;
            let mut sub_pattern_id = None;
            for child in &node.children {
                if child.kind == SyntaxKind::Identifier && binding_name.is_none() {
                    binding_name = Some(ctx.intern(&child.text));
                } else if let Some(pat) = lower_pattern(ctx, current_scope, child, body) {
                    sub_pattern_id = Some(pat);
                }
            }
            if let Some(name) = binding_name {
                Pattern::Binding {
                    name,
                    mutable: false,
                    sub_pattern: sub_pattern_id.map(Box::new),
                    span: file_span,
                }
            } else {
                Pattern::Wildcard { span: file_span }
            }
        }
        SyntaxKind::Unknown(ref name) if name == "|" => {
            // Pipe separator - this shouldn't be parsed as a standalone pattern
            // It should be filtered out by parent pattern handlers
            // Return None to skip it
            return None;
        }
        _ => {
            // Report unhandled pattern kinds as diagnostics instead of panicking,
            // so we can see all gaps when parsing large real-world files
            ctx.report_unhandled(
                DiagnosticSeverity::Warning,
                format!("unhandled pattern kind: {:?}", node.kind),
                file_span,
            );
            return None;
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
        if pattern_id.is_none() && child.kind == SyntaxKind::Identifier {
            // Simple binding pattern (first identifier before any type/initializer)
            let name = child.text.clone();
            let name_sym = ctx.intern(&name);

            // Create symbol for the binding
            let symbol_id = ctx
                .symbols
                .add(name_sym, SymbolKind::Local, child.span, current_scope);
            ctx.scope_tree
                .add_symbol(current_scope, name.clone(), symbol_id);

            // Create a local definition for this binding
            let local_id = LocalId(ctx.next_local_id);
            ctx.next_local_id += 1;
            let function_id = ctx
                .current_function_id
                .expect("lower_let_stmt called outside function context");
            let def_id = DefId::Local {
                func: function_id,
                local: local_id,
            };
            ctx.symbols.set_def_id(symbol_id, def_id);
            ctx.symbol_defs.insert(symbol_id, def_id);

            let pat_file_span = ctx.file_span(child);
            pattern_id = Some(body.patterns.alloc(Pattern::Binding {
                name: name_sym,
                mutable: is_mutable,
                sub_pattern: None,
                span: pat_file_span,
            }));
        } else if pattern_id.is_none() && is_pattern_node(child) {
            // Complex pattern (tuple, struct, etc.) - use the pattern lowering function
            pattern_id = lower_pattern(ctx, current_scope, child, body);
        } else if is_expr_node(child) {
            initializer = Some(lower_expr(ctx, current_scope, child, body));
        }
    }

    let pattern_id = pattern_id.unwrap_or_else(|| {
        panic!(
            "ICE: Let statement at {:?} has no pattern. \
             Parser should produce valid let_declaration nodes with patterns.",
            file_span
        )
    });

    body.stmts.alloc(Stmt::Let {
        pattern: pattern_id,
        ty: None,
        initializer,
        mutable: is_mutable,
        else_branch: None,
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
    ) || matches!(kind, SyntaxKind::Unknown(ref s) if s == "self")
}

/// Check if a node is a keyword or delimiter (not an expression)
fn is_keyword_or_delimiter(kind: &SyntaxKind, text: &str) -> bool {
    // Keywords and delimiters that shouldn't be treated as expressions
    matches!(
        text,
        "match" | "{" | "}" | "(" | ")" | "[" | "]" | "," | ";" | ":"
    ) || matches!(
        kind,
        SyntaxKind::Unknown(ref s) if s == "match_block" || s.contains("_list")
    )
}

/// Check if text is a binary operator
fn is_binary_operator(text: &str) -> bool {
    matches!(
        text,
        "+" | "-"
            | "*"
            | "/"
            | "%"
            | "=="
            | "!="
            | "<"
            | ">"
            | "<="
            | ">="
            | "&&"
            | "||"
            | "&"
            | "|"
            | "^"
            | "<<"
            | ">>"
    )
}

/// Lower a struct definition
fn lower_struct_with_attrs(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    lower_struct(ctx, current_scope, node, attrs);
}

fn lower_struct(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier || child.kind == SyntaxKind::Type)
        .map(|child| child.text.clone())
        .unwrap_or_else(|| {
            panic!(
                "ICE: Struct declaration at {:?} has no identifier. \
                 Parser should ensure all struct_item nodes contain an identifier.",
                ctx.file_span(node)
            )
        });

    if name.is_empty() {
        panic!(
            "ICE: Struct declaration at {:?} has empty identifier. \
             Parser should ensure struct identifiers are non-empty.",
            ctx.file_span(node)
        )
    }

    let name_interned = ctx.intern(&name);
    let file_span = ctx.file_span(node);

    // Reuse pre-registered symbol if available, otherwise register now
    let type_id = if let Some(existing_sym) = ctx.scope_tree.resolve(current_scope, &name) {
        let def_id = ctx
            .symbol_defs
            .get(&existing_sym)
            .copied()
            .unwrap_or_else(|| panic!("ICE: Pre-registered struct '{}' has no DefId", name));
        match def_id {
            DefId::Type(tid) => tid,
            _ => panic!("ICE: Pre-registered symbol '{}' is not a type", name),
        }
    } else {
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
        type_id
    };

    // Parse generic parameters
    let mut generic_params = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generic_params = parse_generic_params(ctx, child);
        }
    }

    // Parse fields - look for field_declaration_list (named) or ordered_field_declaration_list (tuple)
    let mut fields = vec![];
    let mut kind = StructKind::Unit;
    for child in &node.children {
        if let SyntaxKind::Unknown(child_name) = &child.kind {
            if child_name == "field_declaration_list" {
                kind = StructKind::Named;
                for field_node in &child.children {
                    if let SyntaxKind::Unknown(field_kind) = &field_node.kind {
                        if field_kind == "field_declaration" {
                            if let Some(field) = parse_field(ctx, field_node) {
                                fields.push(field);
                            }
                        }
                    }
                }
            } else if child_name == "ordered_field_declaration_list" {
                // Tuple struct: `struct Wrapper(i64, i64)`
                kind = StructKind::Tuple;
                let mut field_idx = 0u32;
                for field_node in &child.children {
                    // Each child that is a type node is a positional field
                    if field_node.kind == SyntaxKind::Type || is_type_like_unknown(field_node) {
                        let field_ty = lower_type_node(ctx, field_node);
                        let field_span = ctx.file_span(field_node);
                        let synthetic_name = ctx.intern(&field_idx.to_string());
                        fields.push(FieldDef {
                            name: synthetic_name,
                            ty: field_ty,
                            visibility: Visibility::Public,
                            span: field_span,
                        });
                        field_idx += 1;
                    }
                }
            }
        }
    }

    let visibility = extract_visibility(node);
    let struct_def = StructDef {
        id: type_id,
        name: name_interned,
        visibility,
        generic_params,
        fields,
        kind,
        attributes: attrs,
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
        if (child.kind == SyntaxKind::Identifier
            || matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "field_identifier"))
            && field_name.is_none()
        {
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
fn lower_enum_with_attrs(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    lower_enum(ctx, current_scope, node, attrs);
}

fn lower_enum(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier || child.kind == SyntaxKind::Type)
        .map(|child| child.text.clone())
        .unwrap_or_else(|| {
            panic!(
                "ICE: Enum declaration at {:?} has no identifier. \
                 Parser should ensure all enum_item nodes contain an identifier.",
                ctx.file_span(node)
            )
        });

    if name.is_empty() {
        panic!(
            "ICE: Enum declaration at {:?} has empty identifier. \
             Parser should ensure enum identifiers are non-empty.",
            ctx.file_span(node)
        )
    }

    let name_interned = ctx.intern(&name);
    let file_span = ctx.file_span(node);

    // Reuse pre-registered symbol if available, otherwise register now
    let type_id = if let Some(existing_sym) = ctx.scope_tree.resolve(current_scope, &name) {
        let def_id = ctx
            .symbol_defs
            .get(&existing_sym)
            .copied()
            .unwrap_or_else(|| panic!("ICE: Pre-registered enum '{}' has no DefId", name));
        match def_id {
            DefId::Type(tid) => tid,
            _ => panic!("ICE: Pre-registered symbol '{}' is not a type", name),
        }
    } else {
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
        type_id
    };

    // Parse generic parameters
    let mut generic_params = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generic_params = parse_generic_params(ctx, child);
        }
    }

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

    let visibility = extract_visibility(node);
    let enum_def = EnumDef {
        id: type_id,
        name: name_interned,
        visibility,
        generic_params,
        variants,
        attributes: attrs,
        span: file_span,
    };

    ctx.enums.insert(type_id, enum_def);
}

/// Parse an enum variant
///
/// Tree-sitter produces `enum_variant` nodes with children:
/// - Unit variant: `[identifier]`
/// - Tuple variant: `[identifier, ordered_field_declaration_list]`
/// - Struct variant: `[identifier, field_declaration_list]`
fn parse_variant(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<VariantDef> {
    // Handle bare identifier children (unit variants listed directly)
    if node.kind == SyntaxKind::Identifier {
        let name = ctx.intern(&node.text);
        return Some(VariantDef {
            name,
            fields: VariantFields::Unit,
            span: ctx.file_span(node),
        });
    }

    // Handle enum_variant wrapper nodes
    if !matches!(&node.kind, SyntaxKind::Unknown(ref s) if s == "enum_variant") {
        return None;
    }

    // Extract variant name from identifier child
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| ctx.intern(&child.text))?;

    // Determine variant kind by looking for field lists
    let mut fields = VariantFields::Unit;

    for child in &node.children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            match kind.as_str() {
                "ordered_field_declaration_list" => {
                    // Tuple variant: extract types from children
                    let mut type_ids = Vec::new();
                    for type_child in &child.children {
                        if type_child.kind == SyntaxKind::Type {
                            type_ids.push(lower_type_node(ctx, type_child));
                        }
                    }
                    fields = VariantFields::Tuple(type_ids);
                }
                "field_declaration_list" => {
                    // Struct variant: extract field declarations
                    let mut field_defs = Vec::new();
                    for field_node in &child.children {
                        if let SyntaxKind::Unknown(ref field_kind) = field_node.kind {
                            if field_kind == "field_declaration" {
                                if let Some(field) = parse_field(ctx, field_node) {
                                    field_defs.push(field);
                                }
                            }
                        }
                    }
                    fields = VariantFields::Struct(field_defs);
                }
                _ => {}
            }
        }
    }

    Some(VariantDef {
        name,
        fields,
        span: ctx.file_span(node),
    })
}

/// Parse generic parameters from a GenericParams node
fn parse_generic_params(ctx: &mut LoweringContext, node: &SyntaxNode) -> Vec<GenericParam> {
    let mut params = vec![];

    for child in &node.children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "type_parameter" {
                let mut name = None;
                let mut span = None;
                let mut bounds = vec![];

                let mut maybe_unsized = false;
                let mut default_type = None;
                let mut found_eq = false;

                for type_child in &child.children {
                    // Detect `= DefaultType` syntax (e.g., `<Rhs = Self>`)
                    if type_child.text == "=" {
                        found_eq = true;
                        continue;
                    }
                    if found_eq
                        && (type_child.kind == SyntaxKind::Type || is_type_like_unknown(type_child))
                    {
                        default_type = Some(lower_type_node(ctx, type_child));
                        found_eq = false;
                        continue;
                    }

                    // Extract the type name (first Type child)
                    if type_child.kind == SyntaxKind::Type && name.is_none() {
                        name = Some(ctx.intern(&type_child.text));
                        span = Some(ctx.file_span(type_child));
                    }
                    // Extract trait bounds (e.g., <T: Clone + Debug>)
                    // tree-sitter-rust places trait_bounds as a child of type_parameter
                    if let SyntaxKind::Unknown(ref child_kind) = type_child.kind {
                        if child_kind == "trait_bounds" {
                            parse_trait_bounds_node(ctx, type_child, &mut bounds);
                        }
                        // Detect ?Sized (removed_trait_bound node)
                        if child_kind == "removed_trait_bound" {
                            // Check if this removes the Sized bound
                            for inner in &type_child.children {
                                if inner.kind == SyntaxKind::Type && inner.text == "Sized" {
                                    maybe_unsized = true;
                                }
                            }
                        }
                    }
                }

                if let (Some(name), Some(span)) = (name, span) {
                    params.push(GenericParam {
                        name,
                        kind: GenericParamKind::Type,
                        bounds,
                        maybe_unsized,
                        default_type,
                        span,
                    });
                }
            } else if kind == "const_parameter" {
                // Parse const generic parameter: `const N: usize`
                let mut name = None;
                let mut ty = None;
                let mut span = None;
                let mut found_colon = false;

                for const_child in &child.children {
                    // Skip the `const` keyword
                    if const_child.text == "const" {
                        continue;
                    }
                    if const_child.text == ":" {
                        found_colon = true;
                        continue;
                    }
                    // The identifier after `const`
                    if !found_colon && name.is_none() {
                        if const_child.kind == SyntaxKind::Identifier
                            || const_child.kind == SyntaxKind::Type
                            || matches!(&const_child.kind, SyntaxKind::Unknown(k) if k == "identifier")
                        {
                            name = Some(ctx.intern(&const_child.text));
                            span = Some(ctx.file_span(const_child));
                        }
                    }
                    // The type after `:`
                    if found_colon && ty.is_none() {
                        ty = Some(lower_type_node(ctx, const_child));
                    }
                }

                if let (Some(name), Some(ty), Some(span)) = (name, ty, span) {
                    params.push(GenericParam {
                        name,
                        kind: GenericParamKind::Const { ty },
                        bounds: vec![],
                        maybe_unsized: false,
                        default_type: None,
                        span,
                    });
                }
            }
        }
    }

    params
}

/// Parse type arguments from a type_arguments node (turbofish: `::<T, U>`)
///
/// Example: `foo::<i32, String>()`
/// The type_arguments node contains the types inside `< >`.
fn parse_type_arguments(ctx: &mut LoweringContext, node: &SyntaxNode) -> Vec<TypeId> {
    let mut type_args = vec![];

    for child in &node.children {
        // Look for type nodes
        if child.kind == SyntaxKind::Type || is_type_like_unknown(child) {
            type_args.push(lower_type_node(ctx, child));
        }
    }

    type_args
}

/// Parse lifetime parameters from a GenericParams node (e.g., `<'a, 'b: 'a, T>`)
///
/// In tree-sitter-rust, lifetime parameters appear as children of `type_parameters`
/// with node kind `"lifetime"`. The text includes the `'` prefix (e.g., `'a`).
fn parse_lifetime_params(
    ctx: &mut LoweringContext,
    node: &SyntaxNode,
) -> Vec<rv_hir::LifetimeParam> {
    let mut params = vec![];

    for child in &node.children {
        if child.kind == SyntaxKind::Lifetime {
            let lifetime_id = ctx.alloc_lifetime_id();
            let name = ctx.intern(&child.text);
            params.push(rv_hir::LifetimeParam {
                id: lifetime_id,
                name,
                bounds: vec![],
                span: ctx.file_span(child),
            });
        }
        // Also check for constrained_type_parameter nodes that contain lifetime bounds
        // e.g., `'a: 'b` in tree-sitter-rust
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "constrained_type_parameter" || kind == "lifetime" {
                // Check if this is a lifetime with bounds
                let mut lt_name = None;
                let mut bounds = vec![];
                for sub in &child.children {
                    if sub.kind == SyntaxKind::Lifetime {
                        if lt_name.is_none() {
                            lt_name = Some(sub.text.clone());
                        } else {
                            // Subsequent lifetimes are bounds
                            // We'll resolve bound IDs in a later pass
                            let bound_id = ctx.alloc_lifetime_id();
                            bounds.push(bound_id);
                        }
                    }
                }
                if let Some(name_text) = lt_name {
                    let lifetime_id = ctx.alloc_lifetime_id();
                    let name = ctx.intern(&name_text);
                    params.push(rv_hir::LifetimeParam {
                        id: lifetime_id,
                        name,
                        bounds,
                        span: ctx.file_span(child),
                    });
                }
            }
        }
    }

    params
}

/// Apply Rust's lifetime elision rules to a function signature.
///
/// The three rules:
/// 1. Each elided lifetime in a parameter gets a distinct fresh lifetime.
/// 2. If there is exactly one input lifetime, it is assigned to all elided output lifetimes.
/// 3. If `&self` or `&mut self` is a parameter, its lifetime is assigned to all elided output lifetimes.
fn apply_lifetime_elision(
    ctx: &mut LoweringContext,
    parameters: &[Parameter],
    return_type: Option<TypeId>,
    self_param: Option<SelfParam>,
    lifetime_params: &mut Vec<rv_hir::LifetimeParam>,
) {
    // Rule 1: Assign distinct fresh lifetimes to all elided reference parameters
    let mut input_lifetimes: Vec<rv_span::LifetimeId> = Vec::new();
    let mut self_lifetime: Option<rv_span::LifetimeId> = None;

    for param in parameters {
        assign_elided_lifetimes_to_type(ctx, param.ty, lifetime_params, &mut input_lifetimes);
    }

    // Track the self parameter's lifetime (Rule 3)
    if self_param.is_some() && !input_lifetimes.is_empty() {
        // The first input lifetime corresponds to &self / &mut self
        self_lifetime = Some(input_lifetimes[0]);
    }

    // Rules 2 & 3: Determine the output lifetime
    let output_lifetime = if self_lifetime.is_some() {
        // Rule 3: &self lifetime wins
        self_lifetime
    } else if input_lifetimes.len() == 1 {
        // Rule 2: Single input lifetime is assigned to output
        Some(input_lifetimes[0])
    } else {
        // Multiple input lifetimes and no &self — output lifetimes cannot be elided
        // (the programmer must annotate them explicitly; we leave them as None)
        None
    };

    // Apply the output lifetime to all elided references in the return type
    if let (Some(ret_ty), Some(lt_id)) = (return_type, output_lifetime) {
        assign_output_lifetime_to_type(ctx, ret_ty, lt_id);
    }
}

/// Recursively find elided references in a type and assign fresh lifetimes.
/// Collects assigned lifetime IDs into `input_lifetimes`.
fn assign_elided_lifetimes_to_type(
    ctx: &mut LoweringContext,
    type_id: TypeId,
    lifetime_params: &mut Vec<rv_hir::LifetimeParam>,
    input_lifetimes: &mut Vec<rv_span::LifetimeId>,
) {
    // We need to read the type first, then potentially mutate it
    let ty = ctx.types[type_id].clone();
    match ty {
        Type::Reference {
            lifetime: None,
            mutable,
            inner,
            span,
        } => {
            // Elided reference — assign a fresh lifetime (Rule 1)
            let lt_id = ctx.alloc_lifetime_id();
            let lt_name = ctx.intern(&format!("'_{}", lt_id.0));
            lifetime_params.push(rv_hir::LifetimeParam {
                id: lt_id,
                name: lt_name,
                bounds: vec![],
                span,
            });
            input_lifetimes.push(lt_id);

            // Update the reference type with the assigned lifetime
            ctx.types[type_id] = Type::Reference {
                lifetime: Some(lt_id),
                mutable,
                inner,
                span,
            };
        }
        Type::Reference {
            lifetime: Some(lt_id),
            ..
        } => {
            // Explicitly annotated lifetime — just record it
            input_lifetimes.push(lt_id);
        }
        _ => {
            // Not a reference type — no lifetime to assign
        }
    }
}

/// Recursively assign a specific lifetime to all elided references in a return type.
fn assign_output_lifetime_to_type(
    ctx: &mut LoweringContext,
    type_id: TypeId,
    lifetime: rv_span::LifetimeId,
) {
    let ty = ctx.types[type_id].clone();
    if let Type::Reference {
        lifetime: None,
        mutable,
        inner,
        span,
    } = ty
    {
        ctx.types[type_id] = Type::Reference {
            lifetime: Some(lifetime),
            mutable,
            inner,
            span,
        };
    }
}

/// Parse function parameters from a Parameters node
fn parse_parameters(
    ctx: &mut LoweringContext,
    node: &SyntaxNode,
) -> (Vec<Parameter>, Option<SelfParam>) {
    let mut params = vec![];
    let mut self_param = None;

    // Tree-sitter may represent simple self parameters (e.g., `(&self)`) directly in the
    // parameters node text rather than creating a separate `self_parameter` child node.
    // Detect this case by checking if the text contains "self" without a type annotation.
    if node.text.contains("self") && !node.text.contains(":") {
        // Simple self parameter without type annotation (e.g., "(self)", "(&self)", "(&mut self)")
        // Use the impl block's self type with appropriate reference wrapping
        if let Some(self_ty) = ctx.current_impl_self_ty {
            let name_sym = ctx.intern("self");
            let param_text = node.text.trim();

            let param_ty = if param_text.contains("&mut") {
                self_param = Some(SelfParam::MutRef);
                // &mut self
                ctx.types.alloc(Type::Reference {
                    inner: Box::new(self_ty),
                    mutable: true,
                    lifetime: None,
                    span: ctx.file_span(node),
                })
            } else if param_text.contains('&') {
                self_param = Some(SelfParam::Ref);
                // &self
                ctx.types.alloc(Type::Reference {
                    inner: Box::new(self_ty),
                    mutable: false,
                    lifetime: None,
                    span: ctx.file_span(node),
                })
            } else {
                self_param = Some(SelfParam::Value);
                // self (by value)
                self_ty
            };

            params.push(Parameter {
                inferred_ty: None,
                name: name_sym,
                ty: param_ty,
                span: ctx.file_span(node),
            });
            return (params, self_param); // Early return - we found the self parameter
        }
    }

    for child in &node.children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "self_parameter" {
                // Self parameter (e.g., `self`, `&self`, `&mut self`, or `self: Type`)
                let name_sym = ctx.intern("self");

                // Try to find a type annotation for self (self: Type)
                let mut param_type_id = None;
                for param_child in &child.children {
                    if param_child.kind == SyntaxKind::Type {
                        param_type_id = Some(lower_type_node(ctx, param_child));
                    }
                }

                // If no type annotation, parse from text and use the impl block's self type
                if param_type_id.is_none() {
                    if let Some(self_ty) = ctx.current_impl_self_ty {
                        let param_text = child.text.trim();
                        if param_text.contains("&mut") {
                            self_param = Some(SelfParam::MutRef);
                            // &mut self
                            param_type_id = Some(ctx.types.alloc(Type::Reference {
                                inner: Box::new(self_ty),
                                mutable: true,
                                lifetime: None,
                                span: ctx.file_span(child),
                            }));
                        } else if param_text.contains('&') {
                            self_param = Some(SelfParam::Ref);
                            // &self
                            param_type_id = Some(ctx.types.alloc(Type::Reference {
                                inner: Box::new(self_ty),
                                mutable: false,
                                lifetime: None,
                                span: ctx.file_span(child),
                            }));
                        } else {
                            self_param = Some(SelfParam::Value);
                            // self (by value)
                            param_type_id = Some(self_ty);
                        }
                    }
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
                // Structure: Identifier, ":", Type (or reference_type)
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
                        _ if is_type_like_unknown(param_child) => {
                            // Handle generic_type, reference_type, pointer_type, etc.
                            param_type_id = Some(lower_type_node(ctx, param_child));
                        }
                        _ => {}
                    }
                }

                // Handle `self` parameter without type annotation
                if let Some(name) = param_name {
                    if ctx.interner.resolve(&name) == "self" && param_type_id.is_none() {
                        // Parse from text and use the impl block's self type
                        if let Some(self_ty) = ctx.current_impl_self_ty {
                            let param_text = child.text.trim();
                            if param_text.contains("&mut") {
                                self_param = Some(SelfParam::MutRef);
                                param_type_id = Some(ctx.types.alloc(Type::Reference {
                                    inner: Box::new(self_ty),
                                    mutable: true,
                                    lifetime: None,
                                    span: ctx.file_span(child),
                                }));
                            } else if param_text.contains('&') {
                                self_param = Some(SelfParam::Ref);
                                param_type_id = Some(ctx.types.alloc(Type::Reference {
                                    inner: Box::new(self_ty),
                                    mutable: false,
                                    lifetime: None,
                                    span: ctx.file_span(child),
                                }));
                            } else {
                                self_param = Some(SelfParam::Value);
                                param_type_id = Some(self_ty);
                            }
                        }
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

    (params, self_param)
}

/// Lower a Type syntax node to HIR `TypeId`
fn lower_type_node(ctx: &mut LoweringContext, node: &SyntaxNode) -> TypeId {
    let span = ctx.file_span(node);

    // Handle type-like nodes represented as Unknown(...) by tree-sitter
    if let SyntaxKind::Unknown(ref s) = node.kind {
        match s.as_str() {
            "reference_type" => {
                // Parse reference type: & or &mut followed by inner type
                let mut mutable = false;
                let mut inner_type_node = None;

                for child in &node.children {
                    if let SyntaxKind::Unknown(ref child_kind) = child.kind {
                        if child_kind == "mut" || child_kind == "mutable_specifier" {
                            mutable = true;
                        }
                    }
                    // The inner type is the Type node or another type-like node
                    if child.kind == SyntaxKind::Type || is_type_like_unknown(child) {
                        inner_type_node = Some(child);
                    }
                }

                if let Some(inner_node) = inner_type_node {
                    let inner_ty = lower_type_node(ctx, inner_node);
                    return ctx.types.alloc(Type::Reference {
                        inner: Box::new(inner_ty),
                        mutable,
                        lifetime: None,
                        span,
                    });
                }
            }
            "generic_type" => {
                // Parse generic type: TypeName<Arg1, Arg2, ...>
                // Children: Type("TypeName"), type_arguments("<Arg1, Arg2>")
                let mut base_name = None;
                let mut type_args = vec![];

                for child in &node.children {
                    if child.kind == SyntaxKind::Type && base_name.is_none() {
                        base_name = Some(&child.text);
                    } else if let SyntaxKind::Unknown(ref ck) = child.kind {
                        if ck == "scoped_type_identifier" && base_name.is_none() {
                            // e.g., cmp::PartialEq<T>
                            base_name = Some(&child.text);
                        } else if ck == "type_arguments" {
                            // Parse type arguments
                            for arg_child in &child.children {
                                if arg_child.kind == SyntaxKind::Type
                                    || is_type_like_unknown(arg_child)
                                {
                                    type_args.push(lower_type_node(ctx, arg_child));
                                }
                            }
                        }
                    }
                }

                if let Some(name_text) = base_name {
                    let name = ctx.intern(name_text);

                    // Check if this is a generic type alias (e.g., `type Pair<A, B> = (A, B);`)
                    if let Some(alias) = ctx.type_aliases.values().find(|a| a.name == name) {
                        if alias.generic_params.is_empty() || type_args.is_empty() {
                            // Non-generic alias or no args provided — return aliased type directly
                            return alias.aliased_type;
                        }
                        // Generic alias with type args — substitute generic params in aliased type
                        let aliased_type = alias.aliased_type;
                        let param_names: Vec<InternedString> =
                            alias.generic_params.iter().map(|p| p.name).collect();
                        return substitute_type_params(ctx, aliased_type, &param_names, &type_args);
                    }

                    let def = ctx
                        .structs
                        .iter()
                        .find(|(_, st)| st.name == name)
                        .map(|(id, _)| *id)
                        .or_else(|| {
                            ctx.enums
                                .iter()
                                .find(|(_, e)| e.name == name)
                                .map(|(id, _)| *id)
                        });
                    return ctx.types.alloc(Type::Named {
                        name,
                        def,
                        args: type_args,
                        span,
                    });
                }
            }
            "scoped_type_identifier" => {
                // Path-qualified type: e.g., cmp::PartialEq, Self::Item
                // Children: Identifier("cmp"), "::", Type("PartialEq")
                let text = &node.text;
                let parts: Vec<&str> = text.split("::").collect();

                if parts.len() == 2 {
                    let base_name = ctx.intern(parts[0]);
                    let assoc_name = ctx.intern(parts[1]);

                    let base_ty = if parts[0] == "Self" {
                        // Resolve Self to the impl block's self type if available
                        if let Some(self_ty) = ctx.current_impl_self_ty {
                            self_ty
                        } else {
                            ctx.types.alloc(Type::Named {
                                name: base_name,
                                def: None,
                                args: vec![],
                                span,
                            })
                        }
                    } else {
                        let def = ctx
                            .structs
                            .iter()
                            .find(|(_, st)| st.name == base_name)
                            .map(|(id, _)| *id)
                            .or_else(|| {
                                ctx.enums
                                    .iter()
                                    .find(|(_, e)| e.name == base_name)
                                    .map(|(id, _)| *id)
                            });
                        ctx.types.alloc(Type::Named {
                            name: base_name,
                            def,
                            args: vec![],
                            span,
                        })
                    };

                    // Resolve trait_ref: for Self::Item, use the current trait context
                    let trait_ref = if parts[0] == "Self" {
                        ctx.current_trait_id
                    } else {
                        None
                    };

                    return ctx.types.alloc(Type::QualifiedPath {
                        base: Box::new(base_ty),
                        assoc_type: assoc_name,
                        trait_ref,
                        span,
                    });
                }
                // For longer paths (a::b::c), use the last segment as the type name
                if let Some(last) = parts.last() {
                    let name = ctx.intern(last);
                    return ctx.types.alloc(Type::Named {
                        name,
                        def: None,
                        args: vec![],
                        span,
                    });
                }
            }
            "pointer_type" => {
                // Raw pointer type: *const T or *mut T
                let mut mutable = false;
                let mut inner_type_node = None;

                for child in &node.children {
                    if let SyntaxKind::Unknown(ref ck) = child.kind {
                        if ck == "mut" || ck == "mutable_specifier" {
                            mutable = true;
                        }
                    }
                    if child.kind == SyntaxKind::Type || is_type_like_unknown(child) {
                        inner_type_node = Some(child);
                    }
                }

                if let Some(inner_node) = inner_type_node {
                    let inner_ty = lower_type_node(ctx, inner_node);
                    return ctx.types.alloc(Type::Pointer {
                        inner: Box::new(inner_ty),
                        mutable,
                        span,
                    });
                }
            }
            "array_type" => {
                // Array type: [T; N]
                // Children: "[", Type, ";", integer_literal or identifier or expression, "]"
                let mut elem_type = None;
                let mut array_size = ArraySize::Infer;
                let mut found_semicolon = false;

                for child in &node.children {
                    // First, look for the element type (before semicolon)
                    if !found_semicolon
                        && (child.kind == SyntaxKind::Type || is_type_like_unknown(child))
                    {
                        elem_type = Some(lower_type_node(ctx, child));
                    }

                    // Track when we've seen the semicolon
                    if child.text == ";" {
                        found_semicolon = true;
                        continue;
                    }

                    // After semicolon, look for the size expression
                    if found_semicolon {
                        // Integer literal: [T; 10]
                        if matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "integer_literal")
                            || matches!(child.kind, SyntaxKind::Literal)
                        {
                            if let Ok(size) = child.text.parse::<usize>() {
                                array_size = ArraySize::Const(size);
                            } else {
                                // If it's not a valid integer, store as expression
                                array_size = ArraySize::Expr(child.text.clone());
                            }
                        }
                        // Identifier: [T; N] where N is a const generic parameter
                        else if matches!(child.kind, SyntaxKind::Identifier) {
                            let name = ctx.intern(&child.text);
                            array_size = ArraySize::ConstParam(name);
                        }
                        // General expression (for generic_const_exprs feature)
                        else if is_expr_node(child) {
                            array_size = ArraySize::Expr(child.text.clone());
                        }
                    }
                }

                if let Some(elem_ty) = elem_type {
                    return ctx.types.alloc(Type::Array {
                        element: Box::new(elem_ty),
                        size: array_size,
                        span,
                    });
                }
            }
            "tuple_type" => {
                // Tuple type: (A, B, C)
                let mut elem_types = vec![];
                for child in &node.children {
                    if child.kind == SyntaxKind::Type || is_type_like_unknown(child) {
                        elem_types.push(lower_type_node(ctx, child));
                    }
                }
                return ctx.types.alloc(Type::Tuple {
                    elements: elem_types,
                    span,
                });
            }
            "never_type" => {
                return ctx.types.alloc(Type::Never { span });
            }
            "function_type" => {
                // fn(A, B) -> C
                // Children: "fn", parameters(...), "->", ReturnType
                let mut param_types = vec![];
                let mut ret_type = None;

                for child in &node.children {
                    if child.kind == SyntaxKind::Parameters {
                        // Parse parameter types from the parameter list
                        for param_child in &child.children {
                            if param_child.kind == SyntaxKind::Type
                                || is_type_like_unknown(param_child)
                            {
                                param_types.push(lower_type_node(ctx, param_child));
                            }
                        }
                    } else if child.kind == SyntaxKind::Type || is_type_like_unknown(child) {
                        // Return type
                        ret_type = Some(lower_type_node(ctx, child));
                    }
                }

                let unit_name = ctx.intern("()");
                let ret = ret_type.unwrap_or_else(|| {
                    ctx.types.alloc(Type::Tuple {
                        elements: vec![],
                        span,
                    })
                });
                let _ = unit_name; // used for documentation clarity

                return ctx.types.alloc(Type::Function {
                    params: param_types,
                    ret: Box::new(ret),
                    span,
                });
            }
            "bounded_type" => {
                // `T + Trait` in a type position. Bare bounded types aren't valid
                // Rust in type position (they belong inside `dyn`/`impl` contexts,
                // which have their own handling). When tree-sitter produces a
                // bounded_type here, extract the primary type and discard the
                // additional trait bounds since they're enforced at the where-clause
                // or generic-bound level, not in the type representation itself.
                for child in &node.children {
                    if child.kind == SyntaxKind::Type || is_type_like_unknown(child) {
                        return lower_type_node(ctx, child);
                    }
                }
            }
            "dynamic_type" => {
                // dyn Trait or dyn Trait + Trait2
                // Children: "dyn", Type("Trait") [or bounded_type for multiple traits]
                let mut bounds = vec![];
                for child in &node.children {
                    if child.kind == SyntaxKind::Type {
                        let name = ctx.intern(&child.text);
                        bounds.push(TypeLevelTraitRef {
                            name,
                            args: vec![],
                            span: ctx.file_span(child),
                        });
                    } else if is_type_like_unknown(child) {
                        if let SyntaxKind::Unknown(ref ck) = child.kind {
                            if ck == "bounded_type" {
                                // Multiple trait bounds: dyn Trait + Send
                                // Parse each bound from the bounded_type children
                                for bound_child in &child.children {
                                    if bound_child.kind == SyntaxKind::Type {
                                        let name = ctx.intern(&bound_child.text);
                                        bounds.push(TypeLevelTraitRef {
                                            name,
                                            args: vec![],
                                            span: ctx.file_span(bound_child),
                                        });
                                    } else if is_type_like_unknown(bound_child) {
                                        // Could be generic_type like Iterator<Item = T>
                                        let name = ctx.intern(&bound_child.text);
                                        bounds.push(TypeLevelTraitRef {
                                            name,
                                            args: vec![],
                                            span: ctx.file_span(bound_child),
                                        });
                                    }
                                }
                            } else {
                                let name = ctx.intern(&child.text);
                                bounds.push(TypeLevelTraitRef {
                                    name,
                                    args: vec![],
                                    span: ctx.file_span(child),
                                });
                            }
                        }
                    }
                }
                return ctx.types.alloc(Type::DynTrait { bounds, span });
            }
            "abstract_type" => {
                // impl Trait or impl Trait + Trait2
                // Children: "impl", Type("Trait") [or bounded_type for multiple traits]
                let mut bounds = vec![];
                for child in &node.children {
                    if child.kind == SyntaxKind::Type {
                        let name = ctx.intern(&child.text);
                        bounds.push(TypeLevelTraitRef {
                            name,
                            args: vec![],
                            span: ctx.file_span(child),
                        });
                    } else if is_type_like_unknown(child) {
                        if let SyntaxKind::Unknown(ref ck) = child.kind {
                            if ck == "bounded_type" {
                                for bound_child in &child.children {
                                    if bound_child.kind == SyntaxKind::Type {
                                        let name = ctx.intern(&bound_child.text);
                                        bounds.push(TypeLevelTraitRef {
                                            name,
                                            args: vec![],
                                            span: ctx.file_span(bound_child),
                                        });
                                    } else if is_type_like_unknown(bound_child) {
                                        let name = ctx.intern(&bound_child.text);
                                        bounds.push(TypeLevelTraitRef {
                                            name,
                                            args: vec![],
                                            span: ctx.file_span(bound_child),
                                        });
                                    }
                                }
                            } else {
                                let name = ctx.intern(&child.text);
                                bounds.push(TypeLevelTraitRef {
                                    name,
                                    args: vec![],
                                    span: ctx.file_span(child),
                                });
                            }
                        }
                    }
                }
                return ctx.types.alloc(Type::ImplTrait { bounds, span });
            }
            "primitive_type" => {
                // Primitive type like i32, u8, bool, etc.
                let name = ctx.intern(&node.text);
                return ctx.types.alloc(Type::Named {
                    name,
                    def: None,
                    args: vec![],
                    span,
                });
            }
            "macro_invocation" => {
                // Macro invocation used as a type — treat as opaque
                let name = ctx.intern(&node.text);
                return ctx.types.alloc(Type::Named {
                    name,
                    def: None,
                    args: vec![],
                    span,
                });
            }
            _ => {}
        }
    }

    // Check if this is a scoped type identifier from text (e.g., Self::Item)
    // This handles cases where the node kind is Type but the text contains "::"
    let text = &node.text;
    if text.contains("::") {
        // This is a qualified path like Self::Item or Foo::Bar
        let parts: Vec<&str> = text.split("::").collect();
        if parts.len() == 2 {
            let base_name = ctx.intern(parts[0]);
            let assoc_name = ctx.intern(parts[1]);

            // Create a base type for Self or the type name
            let base_ty = if parts[0] == "Self" {
                // Resolve Self to the impl block's self type if available
                if let Some(self_ty) = ctx.current_impl_self_ty {
                    self_ty
                } else {
                    ctx.types.alloc(Type::Named {
                        name: base_name,
                        def: None,
                        args: vec![],
                        span,
                    })
                }
            } else {
                // Regular type name - try to resolve it
                let def = ctx
                    .structs
                    .iter()
                    .find(|(_, s)| s.name == base_name)
                    .map(|(id, _)| *id)
                    .or_else(|| {
                        ctx.enums
                            .iter()
                            .find(|(_, e)| e.name == base_name)
                            .map(|(id, _)| *id)
                    });

                ctx.types.alloc(Type::Named {
                    name: base_name,
                    def,
                    args: vec![],
                    span,
                })
            };

            // Resolve trait_ref: for Self::Item, use the current trait context
            let trait_ref = if parts[0] == "Self" {
                ctx.current_trait_id
            } else {
                None
            };

            // Create a QualifiedPath type
            return ctx.types.alloc(Type::QualifiedPath {
                base: Box::new(base_ty),
                assoc_type: assoc_name,
                trait_ref,
                span,
            });
        }
    }

    let name = ctx.intern(text);

    // ARCHITECTURE: Check if this is a generic parameter reference (e.g., T in fn foo<T>(x: T))
    if ctx.current_generic_params.contains(&name) {
        // This is a reference to a generic parameter - create Type::Generic
        let type_node = Type::Generic { name, span };
        return ctx.types.alloc(type_node);
    }

    // Check if this is a type alias (e.g., `type Int = i64;`)
    if let Some(alias) = ctx.type_aliases.values().find(|a| a.name == name) {
        return alias.aliased_type;
    }

    // Try to resolve the type name to a TypeDefId
    let def = ctx
        .structs
        .iter()
        .find(|(_, s)| s.name == name)
        .map(|(id, _)| *id)
        .or_else(|| {
            ctx.enums
                .iter()
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

/// Substitute generic type parameters in a type.
///
/// Walks the type tree rooted at `ty` and replaces any `Type::Generic { name }`
/// whose name appears in `param_names` with the corresponding `TypeId` from `args`.
/// Used for resolving generic type aliases like `type Pair<A, B> = (A, B);`.
fn substitute_type_params(
    ctx: &mut LoweringContext,
    ty: TypeId,
    param_names: &[InternedString],
    args: &[TypeId],
) -> TypeId {
    let hir_type = ctx.types[ty].clone();
    match hir_type {
        Type::Generic { name, .. } => {
            // If this generic name matches one of the alias params, substitute it
            if let Some(idx) = param_names.iter().position(|p| *p == name) {
                if let Some(&replacement) = args.get(idx) {
                    return replacement;
                }
            }
            ty
        }
        Type::Named {
            name,
            def,
            args: inner_args,
            span,
        } => {
            let substituted_args: Vec<TypeId> = inner_args
                .iter()
                .map(|a| substitute_type_params(ctx, *a, param_names, args))
                .collect();
            ctx.types.alloc(Type::Named {
                name,
                def,
                args: substituted_args,
                span,
            })
        }
        Type::Tuple { elements, span } => {
            let substituted: Vec<TypeId> = elements
                .iter()
                .map(|e| substitute_type_params(ctx, *e, param_names, args))
                .collect();
            ctx.types.alloc(Type::Tuple {
                elements: substituted,
                span,
            })
        }
        Type::Reference {
            mutable,
            inner,
            lifetime,
            span,
        } => {
            let substituted_inner = substitute_type_params(ctx, *inner, param_names, args);
            ctx.types.alloc(Type::Reference {
                mutable,
                inner: Box::new(substituted_inner),
                lifetime,
                span,
            })
        }
        Type::Pointer {
            mutable,
            inner,
            span,
        } => {
            let substituted_inner = substitute_type_params(ctx, *inner, param_names, args);
            ctx.types.alloc(Type::Pointer {
                mutable,
                inner: Box::new(substituted_inner),
                span,
            })
        }
        Type::Array {
            element,
            size,
            span,
        } => {
            let substituted_elem = substitute_type_params(ctx, *element, param_names, args);
            ctx.types.alloc(Type::Array {
                element: Box::new(substituted_elem),
                size,
                span,
            })
        }
        Type::Function {
            params: fn_params,
            ret,
            span,
        } => {
            let substituted_params: Vec<TypeId> = fn_params
                .iter()
                .map(|p| substitute_type_params(ctx, *p, param_names, args))
                .collect();
            let substituted_ret = substitute_type_params(ctx, *ret, param_names, args);
            ctx.types.alloc(Type::Function {
                params: substituted_params,
                ret: Box::new(substituted_ret),
                span,
            })
        }
        // Leaf types that don't contain inner types — no substitution needed
        Type::QualifiedPath { .. }
        | Type::Never { .. }
        | Type::DynTrait { .. }
        | Type::ImplTrait { .. }
        | Type::Unknown { .. } => ty,
    }
}

/// Lower an impl block
fn lower_impl_with_attrs(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    lower_impl(ctx, current_scope, node, attrs);
}

fn lower_impl(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    // Parse impl block: either "impl Type { ... }" or "impl Trait for Type { ... }"
    // Strategy: collect type-like nodes and check for "for" keyword to disambiguate.
    //
    // tree-sitter represents types in impl blocks as various node kinds:
    //   - SyntaxKind::Type for simple type identifiers (e.g., `Foo`, `Send`)
    //   - Unknown("scoped_type_identifier") for path-qualified types (e.g., `cmp::PartialEq`)
    //   - Unknown("generic_type") for generic types (e.g., `Option<T>`)
    //   - Unknown("pointer_type") for pointer types (e.g., `*const T`)
    //   - Unknown("reference_type") for reference types (e.g., `&T`)
    //   - Unknown("array_type") for array types (e.g., `[T; N]`)
    //   - Unknown("tuple_type") for tuple types (e.g., `(A, B)`)
    //   - Unknown("never_type") for the never type (`!`)
    //   - Unknown("function_type") for function pointer types
    //   - Unknown("bounded_type") for bounded types (e.g., `T + Trait`)
    let mut trait_ref = None;
    let mut type_nodes: Vec<&SyntaxNode> = Vec::new();
    let mut has_for = false;
    let mut is_negative = false;

    for child in &node.children {
        if child.kind == SyntaxKind::Type || is_type_like_unknown(child) {
            type_nodes.push(child);
        } else if let SyntaxKind::Unknown(ref s) = child.kind {
            match s.as_str() {
                "for" => has_for = true,
                "!" => is_negative = true,
                _ => {}
            }
        }
    }

    // Negative impls (`impl !Trait for Type {}`) opt out of auto traits.
    // Since auto trait propagation isn't implemented, we report them and skip.
    if is_negative {
        ctx.report_unhandled(
            DiagnosticSeverity::Info,
            "negative impl (impl !Trait for Type) — auto traits not yet supported".to_string(),
            ctx.file_span(node),
        );
        return;
    }

    let self_ty_node = if has_for && type_nodes.len() >= 2 {
        // "impl Trait for Type" — first type-like node is trait, second is self type
        let trait_node = type_nodes[0];
        // Extract the trait name: for simple types use text directly,
        // for scoped_type_identifier use the last segment
        let trait_name_text = if let SyntaxKind::Unknown(ref s) = trait_node.kind {
            if s == "scoped_type_identifier" {
                // Extract last segment: e.g., "cmp::PartialEq" -> "PartialEq"
                trait_node
                    .children
                    .iter()
                    .rev()
                    .find(|c| c.kind == SyntaxKind::Type || c.kind == SyntaxKind::Identifier)
                    .map(|c| c.text.as_str())
                    .unwrap_or(&trait_node.text)
            } else {
                &trait_node.text
            }
        } else {
            &trait_node.text
        };
        let trait_name = ctx.intern(trait_name_text);
        for (trait_id, trait_def) in &ctx.traits {
            if trait_def.name == trait_name {
                trait_ref = Some(*trait_id);
                break;
            }
        }
        type_nodes[1]
    } else if !type_nodes.is_empty() {
        // "impl Type" — the single type-like node is the self type
        type_nodes[0]
    } else {
        ctx.report_unhandled(
            DiagnosticSeverity::Warning,
            format!(
                "impl block with no recognizable type nodes (text: {:?})",
                &node.text[..node.text.len().min(80)]
            ),
            ctx.file_span(node),
        );
        return;
    };

    let self_ty = lower_type_node(ctx, self_ty_node);

    let impl_id = ctx.alloc_impl_id();
    let file_span = ctx.file_span(node);

    // Parse generic parameters if present
    let mut generic_params = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generic_params = parse_generic_params(ctx, child);
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
                    lower_function(ctx, impl_scope, item, vec![]);

                    // The newly created function should be the last one added
                    // Find it in the functions map
                    if ctx.functions.len() > func_count_before {
                        // Get the last added function ID by finding the highest ID
                        if let Some((&func_id, _)) = ctx.functions.iter().max_by_key(|(id, _)| id.0)
                        {
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

    // For generic impls (including blanket impls), propagate the impl's generic parameters
    // to each method. This ensures impl methods are treated as generic functions and
    // compiled on-demand via monomorphization. This applies to:
    // - Blanket impls: impl<T> Trait for T
    // - Generic type impls: impl<T> Option<T>
    // - Any impl with generic parameters
    if !generic_params.is_empty() {
        for &func_id in &methods {
            if let Some(func) = ctx.functions.get_mut(&func_id) {
                if func.generics.is_empty() {
                    func.generics = generic_params.clone();
                }
            }
            // Mark as a "template" function that must not be compiled standalone
            ctx.default_method_bodies.insert(func_id);
        }
    }

    // Instantiate default method bodies for this concrete impl
    if let Some(trait_id) = trait_ref {
        if let Some(trait_def) = ctx.traits.get(&trait_id).cloned() {
            let self_name = ctx.intern("Self");
            for trait_method in &trait_def.methods {
                if let Some(default_fn_id) = trait_method.default_body {
                    // Check if this method is already overridden in the impl
                    let already_overridden = methods.iter().any(|&mid| {
                        ctx.functions
                            .get(&mid)
                            .is_some_and(|f| f.name == trait_method.name)
                    });
                    if !already_overridden {
                        // Clone the default body function with Self replaced by the concrete type
                        if let Some(default_fn) = ctx.functions.get(&default_fn_id).cloned() {
                            let new_fn_id = ctx.alloc_function_id();
                            let mut concrete_fn = default_fn;
                            concrete_fn.id = new_fn_id;

                            // Replace Self type references in parameters
                            for param in &mut concrete_fn.parameters {
                                let param_ty = &ctx.types[param.ty];
                                if let Type::Reference {
                                    inner,
                                    mutable,
                                    lifetime,
                                    span,
                                } = param_ty
                                {
                                    let inner_ty = &ctx.types[**inner];
                                    if let Type::Named { name, .. } = inner_ty {
                                        if *name == self_name {
                                            // Replace &Self with &ConcreteType
                                            let new_ref = ctx.types.alloc(Type::Reference {
                                                inner: Box::new(self_ty),
                                                mutable: *mutable,
                                                lifetime: *lifetime,
                                                span: *span,
                                            });
                                            param.ty = new_ref;
                                        }
                                    }
                                } else if let Type::Named { name, .. } = param_ty {
                                    if *name == self_name {
                                        param.ty = self_ty;
                                    }
                                }
                            }

                            ctx.functions.insert(new_fn_id, concrete_fn);
                            methods.push(new_fn_id);
                        }
                    }
                }
            }
        }
    }

    // Parse where clauses
    let where_clauses = parse_where_clauses(ctx, node);

    // Create and store the impl block
    // Check for unsafe impl
    let is_unsafe = node
        .children
        .iter()
        .any(|c| c.text == "unsafe" && c.kind != SyntaxKind::Identifier);

    // Detect blanket impl: self_ty is a generic parameter (e.g., impl<T: Trait> Foo for T)
    let is_blanket = if !generic_params.is_empty() {
        let self_ty_hir = &ctx.types[self_ty];
        match self_ty_hir {
            Type::Named {
                name, def: None, ..
            }
            | Type::Generic { name, .. } => {
                // self_ty is an unresolved name or generic param — check if it matches
                generic_params.iter().any(|gp| gp.name == *name)
            }
            _ => false,
        }
    } else {
        false
    };

    let impl_block = ImplBlock {
        id: impl_id,
        self_ty,
        trait_ref,
        generic_params,
        methods,
        associated_type_impls,
        where_clauses,
        is_unsafe,
        is_blanket,
        is_synthesized: false,
        is_negative: false,
        attributes: attrs,
        span: file_span,
    };

    ctx.impl_blocks.insert(impl_id, impl_block);
}

/// Lower a trait definition
fn lower_trait_with_attrs(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    lower_trait(ctx, current_scope, node, attrs);
}

fn lower_trait(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    // Extract trait name (can be Identifier or Type node)
    let trait_name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier || child.kind == SyntaxKind::Type)
        .map(|child| ctx.intern(&child.text))
        .unwrap_or_else(|| {
            panic!(
                "ICE: Trait declaration at {:?} has no identifier. \
                 Parser should ensure all trait_item nodes contain identifiers.",
                ctx.file_span(node)
            )
        });

    // Reuse pre-registered symbol if available, otherwise allocate now
    let trait_name_str = ctx.interner.resolve(&trait_name).to_string();
    let trait_id =
        if let Some(existing_sym) = ctx.scope_tree.resolve(current_scope, &trait_name_str) {
            let def_id = ctx
                .symbol_defs
                .get(&existing_sym)
                .copied()
                .unwrap_or_else(|| {
                    panic!(
                        "ICE: Pre-registered trait '{}' has no DefId",
                        trait_name_str
                    )
                });
            match def_id {
                DefId::Trait(tid) => tid,
                _ => panic!(
                    "ICE: Pre-registered symbol '{}' is not a trait",
                    trait_name_str
                ),
            }
        } else {
            let symbol_id =
                ctx.symbols
                    .add(trait_name, SymbolKind::Trait, node.span, current_scope);
            ctx.scope_tree
                .add_symbol(current_scope, trait_name_str.clone(), symbol_id);
            let tid = ctx.alloc_trait_id();
            let def_id = DefId::Trait(tid);
            ctx.symbols.set_def_id(symbol_id, def_id);
            ctx.symbol_defs.insert(symbol_id, def_id);
            tid
        };
    let file_span = ctx.file_span(node);

    // Parse generic parameters if present
    let mut generic_params = vec![];
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generic_params = parse_generic_params(ctx, child);
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
                                    for_lifetimes: vec![],
                                });
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    // Set current trait for Self::Item resolution in default method bodies
    let prev_trait_id = ctx.current_trait_id;
    ctx.current_trait_id = Some(trait_id);

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
                // Check for function_signature_item (trait methods) or Function (trait impl methods)
                let is_function_sig = matches!(&item.kind, SyntaxKind::Unknown(ref s) if s == "function_signature_item");

                if item.kind == SyntaxKind::Function || is_function_sig {
                    // Parse method signature
                    if let Some(mut method) = lower_trait_method(ctx, trait_scope, item) {
                        // If this is a full function_item (not function_signature_item),
                        // it has a default body — lower it as a Function entry
                        if item.kind == SyntaxKind::Function {
                            // Set current_impl_self_ty to a Self type so that parse_parameters()
                            // can create a proper `self` parameter for the default method body
                            let self_name = ctx.intern("Self");
                            let self_ty = ctx.types.alloc(Type::Named {
                                name: self_name,
                                args: vec![],
                                def: None,
                                span: ctx.file_span(node),
                            });
                            let prev_impl_self_ty = ctx.current_impl_self_ty;
                            ctx.current_impl_self_ty = Some(self_ty);

                            let func_count_before = ctx.functions.len();
                            lower_function(ctx, trait_scope, item, vec![]);

                            ctx.current_impl_self_ty = prev_impl_self_ty;

                            if ctx.functions.len() > func_count_before {
                                if let Some((&func_id, _)) =
                                    ctx.functions.iter().max_by_key(|(id, _)| id.0)
                                {
                                    method.default_body = Some(func_id);
                                    ctx.default_method_bodies.insert(func_id);
                                }
                            }
                        }
                        methods.push(method);
                    } else {
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

    // Restore previous trait context
    ctx.current_trait_id = prev_trait_id;

    // Check for auto/unsafe trait modifiers
    let is_auto = node
        .children
        .iter()
        .any(|c| c.text == "auto" && c.kind != SyntaxKind::Identifier);
    let is_unsafe = node
        .children
        .iter()
        .any(|c| c.text == "unsafe" && c.kind != SyntaxKind::Identifier);

    // Create and store the trait definition
    let visibility = extract_visibility(node);
    let trait_def = TraitDef {
        id: trait_id,
        name: trait_name,
        visibility,
        generic_params,
        methods,
        associated_types,
        supertraits,
        is_auto,
        is_unsafe,
        attributes: attrs,
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
                                    for_lifetimes: vec![],
                                });
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    // Parse default type if present (type Item = i32;)
    let mut default = None;
    let mut found_eq = false;
    for child in &node.children {
        if child.text == "=" {
            found_eq = true;
            continue;
        }
        if found_eq
            && (child.kind == SyntaxKind::Type
                || matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "generic_type" || s == "scoped_type_identifier" || s == "reference_type" || s == "tuple_type" || s == "array_type"))
        {
            default = Some(lower_type_node(ctx, child));
            break;
        }
    }

    Some(AssociatedType {
        name,
        bounds,
        default,
        span,
    })
}

/// Parse an associated type implementation (type Foo = Bar;)
fn parse_associated_type_impl(
    ctx: &mut LoweringContext,
    node: &SyntaxNode,
) -> Option<AssociatedTypeImpl> {
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
                            // May be SyntaxKind::Type or a type-like Unknown node
                            let ty_opt = predicate
                                .children
                                .iter()
                                .find(|c| c.kind == SyntaxKind::Type || is_type_like_unknown(c))
                                .map(|c| lower_type_node(ctx, c));

                            if let Some(ty) = ty_opt {
                                // Parse trait bounds from trait_bounds node
                                let mut bounds = vec![];
                                for bound_node in &predicate.children {
                                    if let SyntaxKind::Unknown(ref bound_kind) = bound_node.kind {
                                        if bound_kind == "trait_bounds" {
                                            parse_trait_bounds_node(ctx, bound_node, &mut bounds);
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

/// Parse trait bounds from a `trait_bounds` tree-sitter node.
/// Extracts trait names from Type, Identifier, scoped_type_identifier,
/// and generic_type children, resolving them to TraitId where possible.
fn parse_trait_bounds_node(
    ctx: &LoweringContext,
    bounds_node: &SyntaxNode,
    out: &mut Vec<TraitBound>,
) {
    for trait_node in &bounds_node.children {
        // Extract trait name from various node kinds
        let trait_name_str = if trait_node.kind == SyntaxKind::Type
            || trait_node.kind == SyntaxKind::Identifier
        {
            Some(trait_node.text.as_str())
        } else if let SyntaxKind::Unknown(ref ck) = trait_node.kind {
            match ck.as_str() {
                "scoped_type_identifier" => {
                    // e.g., fmt::Debug — use last segment
                    trait_node
                        .children
                        .iter()
                        .rev()
                        .find(|c| c.kind == SyntaxKind::Type || c.kind == SyntaxKind::Identifier)
                        .map(|c| c.text.as_str())
                }
                "generic_type" => {
                    // e.g., Iterator<Item = T> — use base name
                    trait_node
                        .children
                        .iter()
                        .find(|c| c.kind == SyntaxKind::Type)
                        .map(|c| c.text.as_str())
                }
                // Skip punctuation like "+", lifetime bounds like 'a, etc.
                _ => None,
            }
        } else {
            None
        };

        if let Some(name_str) = trait_name_str {
            let trait_name = ctx.interner.intern(name_str);
            // Look up trait by name
            for (tid, tdef) in &ctx.traits {
                if tdef.name == trait_name {
                    out.push(TraitBound {
                        trait_ref: *tid,
                        args: vec![],
                        for_lifetimes: vec![],
                    });
                    break;
                }
            }
        }
    }
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
                        // First try to find an identifier, otherwise check for "_" (ignored parameter)
                        let param_name = param_child
                            .children
                            .iter()
                            .find(|c| c.kind == SyntaxKind::Identifier)
                            .map(|c| ctx.intern(&c.text))
                            .or_else(|| {
                                // Check for "_" pattern (ignored parameter)
                                param_child
                                    .children
                                    .iter()
                                    .find(|c| c.text == "_")
                                    .map(|_| ctx.intern("_"))
                            })
                            .unwrap_or_else(|| {
                                panic!(
                                    "ICE: Parameter at {:?} has no identifier. \
                                     Parser should ensure all parameter nodes contain identifiers.",
                                    ctx.file_span(param_child)
                                )
                            });

                        // Find the type node - could be SyntaxKind::Type or Unknown("reference_type") etc.
                        let param_ty = param_child
                            .children
                            .iter()
                            .find(|c| {
                                c.kind == SyntaxKind::Type ||
                                matches!(c.kind, SyntaxKind::Unknown(ref s) if s.contains("type"))
                            })
                            .map(|c| lower_type_node(ctx, c))
                            .unwrap_or_else(|| {
                                panic!(
                                    "ICE: Parameter at {:?} has no type annotation. \
                                     Parser should ensure all parameter nodes contain type annotations.",
                                    ctx.file_span(param_child)
                                )
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

    // Apply lifetime elision rules to trait method signature
    let mut method_lifetime_params = vec![];
    apply_lifetime_elision(
        ctx,
        &params,
        return_type,
        self_param,
        &mut method_lifetime_params,
    );

    Some(TraitMethod {
        name,
        generics,
        params,
        return_type,
        self_param,
        default_body: None,
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
                        if item_kind == "function_signature_item"
                            || item.kind == SyntaxKind::Function
                        {
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
        .unwrap_or_else(|| {
            panic!(
                "ICE: External function declaration at {:?} has no identifier. \
                 Parser should ensure all function_item nodes in extern blocks contain identifiers.",
                ctx.file_span(node)
            )
        });

    let func_id = ctx.alloc_function_id();
    let span = ctx.file_span(node);

    // Parse parameters - external functions might have no parameter list (just a signature)
    let parameters = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Parameters)
        .map(|params_node| parse_parameters(ctx, params_node).0)
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

    // Parse closure parameters from closure_parameters node: |x, y| or |x: i64, y: i64|
    let mut params = vec![];
    for child in &node.children {
        if let SyntaxKind::Unknown(ref kind) = child.kind {
            if kind == "closure_parameters" {
                for param_child in &child.children {
                    if param_child.kind == SyntaxKind::Identifier {
                        // Untyped parameter: |x|
                        let param_name = ctx.intern(&param_child.text);
                        let param_ty = ctx.types.alloc(Type::Unknown {
                            span: ctx.file_span(param_child),
                        });
                        params.push(Parameter {
                            name: param_name,
                            ty: param_ty,
                            inferred_ty: None,
                            span: ctx.file_span(param_child),
                        });
                    } else if matches!(&param_child.kind, SyntaxKind::Unknown(ref k) if k == "parameter")
                    {
                        // Typed parameter: |x: i64|
                        // The parameter node has an identifier and a type child
                        let mut param_name_opt = None;
                        let mut param_ty_opt = None;
                        for inner in &param_child.children {
                            if inner.kind == SyntaxKind::Identifier && param_name_opt.is_none() {
                                param_name_opt = Some(ctx.intern(&inner.text));
                            } else if inner.kind == SyntaxKind::Type
                                || matches!(&inner.kind, SyntaxKind::Unknown(ref k) if k == "type_identifier")
                            {
                                param_ty_opt = Some(lower_type_node(ctx, inner));
                            }
                        }
                        if let Some(param_name) = param_name_opt {
                            let param_ty = param_ty_opt.unwrap_or_else(|| {
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
        ctx.scope_tree
            .add_symbol(closure_scope, param_name_str, param_symbol);
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
        is_move: false, // TODO: Detect `move` keyword in closure
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

    // No body found in closure
    let file_span = ctx.file_span(node);
    panic!(
        "ICE: Closure at {:?} has no body. \
         Parser should ensure closures have either a block or expression body.",
        file_span
    )
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
    collect_free_vars(
        ctx,
        closure_scope,
        parent_scope,
        body,
        body_expr,
        &mut captures,
    );
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
            let local_def = ctx
                .scope_tree
                .resolve(closure_scope, &ctx.interner.resolve(name));
            // Check if this variable is defined in parent scope (captured)
            let parent_def = ctx
                .scope_tree
                .resolve(parent_scope, &ctx.interner.resolve(name));

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
        Expr::Block {
            statements, expr, ..
        } => {
            // Collect from statements
            for stmt_id in statements {
                collect_free_vars_stmt(ctx, closure_scope, parent_scope, body, *stmt_id, captures);
            }
            // Collect from trailing expression
            if let Some(trailing) = expr {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *trailing, captures);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *condition, captures);
            collect_free_vars(
                ctx,
                closure_scope,
                parent_scope,
                body,
                *then_branch,
                captures,
            );
            if let Some(else_expr) = else_branch {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *else_expr, captures);
            }
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
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
                collect_free_vars(
                    ctx,
                    closure_scope,
                    parent_scope,
                    body,
                    *field_expr,
                    captures,
                );
            }
        }
        Expr::PathCall { args, .. } => {
            for arg in args {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *arg, captures);
            }
        }
        Expr::EnumVariant { fields, .. } => {
            for field_expr in fields {
                collect_free_vars(
                    ctx,
                    closure_scope,
                    parent_scope,
                    body,
                    *field_expr,
                    captures,
                );
            }
        }
        Expr::Closure {
            body: closure_body, ..
        } => {
            // Recursively analyze nested closures
            collect_free_vars(
                ctx,
                closure_scope,
                parent_scope,
                body,
                *closure_body,
                captures,
            );
        }
        Expr::Assign { target, value, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *target, captures);
            collect_free_vars(ctx, closure_scope, parent_scope, body, *value, captures);
        }
        Expr::CompoundAssign { target, value, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *target, captures);
            collect_free_vars(ctx, closure_scope, parent_scope, body, *value, captures);
        }
        Expr::WhileLoop {
            condition,
            body: loop_body,
            ..
        } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *condition, captures);
            collect_free_vars(ctx, closure_scope, parent_scope, body, *loop_body, captures);
        }
        Expr::Loop {
            body: loop_body, ..
        } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *loop_body, captures);
        }
        Expr::Break { value, .. } => {
            if let Some(val) = value {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *val, captures);
            }
        }
        Expr::Continue { .. } => {
            // Nothing to collect
        }
        Expr::Array { elements, .. } => {
            for elem in elements {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *elem, captures);
            }
        }
        Expr::Tuple { elements, .. } => {
            for elem in elements {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *elem, captures);
            }
        }
        Expr::Index { base, index, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *base, captures);
            collect_free_vars(ctx, closure_scope, parent_scope, body, *index, captures);
        }
        Expr::Cast {
            expr: cast_expr, ..
        } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *cast_expr, captures);
        }
        Expr::UnsafeBlock {
            body: inner_body, ..
        } => {
            collect_free_vars(
                ctx,
                closure_scope,
                parent_scope,
                body,
                *inner_body,
                captures,
            );
        }
        Expr::Literal { .. } | Expr::Error { .. } => {
            // Literals and error expressions don't capture variables
        }
        Expr::WhileLet { value, body: while_body, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *value, captures);
            collect_free_vars(ctx, closure_scope, parent_scope, body, *while_body, captures);
        }
        Expr::IfLet { value, then_branch, else_branch, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *value, captures);
            collect_free_vars(ctx, closure_scope, parent_scope, body, *then_branch, captures);
            if let Some(else_expr) = else_branch {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *else_expr, captures);
            }
        }
        Expr::Range { start, end, .. } => {
            if let Some(s) = start {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *s, captures);
            }
            if let Some(e) = end {
                collect_free_vars(ctx, closure_scope, parent_scope, body, *e, captures);
            }
        }
        Expr::Try { expr: inner, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *inner, captures);
        }
        Expr::ForLoop { iterator, body: loop_body, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *iterator, captures);
            collect_free_vars(ctx, closure_scope, parent_scope, body, *loop_body, captures);
        }
        Expr::Box { value, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *value, captures);
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
        Stmt::Box { value, .. } => {
            collect_free_vars(ctx, closure_scope, parent_scope, body, *value, captures);
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
        .unwrap_or_else(|| {
            panic!(
                "ICE: Module declaration at {:?} has no identifier. \
                 Parser should ensure all mod_item nodes contain identifiers.",
                ctx.file_span(node)
            )
        });

    let module_id = ctx.alloc_module_id();
    let file_span = ctx.file_span(node);

    // Extract visibility (pub or private)
    let visibility = extract_visibility(node);

    // Create a scope for the module
    let module_scope = ctx.scope_tree.create_child(current_scope, node.span);

    // Add module symbol to parent scope
    let symbol_id = ctx
        .symbols
        .add(name, SymbolKind::Module, node.span, current_scope);
    ctx.scope_tree.add_symbol(
        current_scope,
        ctx.interner.resolve(&name).to_string(),
        symbol_id,
    );
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
                        lower_function(ctx, module_scope, item_node, vec![]);
                        // Find the newly added function
                        if ctx.functions.len() > func_count_before {
                            if let Some((&func_id, _)) =
                                ctx.functions.iter().max_by_key(|(id, _)| id.0)
                            {
                                items.push(Item::Function(func_id));
                            }
                        }
                    }
                    SyntaxKind::Struct => {
                        let struct_count_before = ctx.structs.len();
                        lower_struct(ctx, module_scope, item_node, vec![]);
                        if ctx.structs.len() > struct_count_before {
                            if let Some((&type_id, _)) =
                                ctx.structs.iter().max_by_key(|(id, _)| id.0)
                            {
                                items.push(Item::Struct(type_id));
                            }
                        }
                    }
                    SyntaxKind::Enum => {
                        let enum_count_before = ctx.enums.len();
                        lower_enum(ctx, module_scope, item_node, vec![]);
                        if ctx.enums.len() > enum_count_before {
                            if let Some((&type_id, _)) = ctx.enums.iter().max_by_key(|(id, _)| id.0)
                            {
                                items.push(Item::Enum(type_id));
                            }
                        }
                    }
                    SyntaxKind::Trait => {
                        let trait_count_before = ctx.traits.len();
                        lower_trait(ctx, module_scope, item_node, vec![]);
                        if ctx.traits.len() > trait_count_before {
                            if let Some((&trait_id, _)) =
                                ctx.traits.iter().max_by_key(|(id, _)| id.0)
                            {
                                items.push(Item::Trait(trait_id));
                            }
                        }
                    }
                    SyntaxKind::Impl => {
                        let impl_count_before = ctx.impl_blocks.len();
                        lower_impl(ctx, module_scope, item_node, vec![]);
                        if ctx.impl_blocks.len() > impl_count_before {
                            if let Some((&impl_id, _)) =
                                ctx.impl_blocks.iter().max_by_key(|(id, _)| id.0)
                            {
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
    ctx.module_scopes.insert(module_id, module_scope);
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
fn extract_path_segments(
    ctx: &mut LoweringContext,
    node: &SyntaxNode,
    path: &mut Vec<InternedString>,
) {
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
        SyntaxKind::Unknown(ref s) if s == "use_wildcard" || s == "*" => {
            // Glob import: use foo::*
            // Add "*" as the last segment to indicate a glob
            path.push(ctx.intern("*"));
        }
        _ => {
            // Check if the node's text is "*" directly (some tree-sitter versions)
            if node.text == "*" {
                path.push(ctx.intern("*"));
            } else {
                // Recurse into children
                for child in &node.children {
                    extract_path_segments(ctx, child, path);
                }
            }
        }
    }
}

/// Collect the path segments from a scoped_identifier node as plain strings.
///
/// For `utils::get_value`, produces `["utils", "get_value"]`.
/// For `math::arithmetic::add`, produces `["math", "arithmetic", "add"]`.
fn collect_scoped_identifier_parts(node: &SyntaxNode, parts: &mut Vec<String>) {
    for child in &node.children {
        match &child.kind {
            SyntaxKind::Identifier => {
                parts.push(child.text.clone());
            }
            SyntaxKind::Unknown(ref s) if s == "scoped_identifier" => {
                collect_scoped_identifier_parts(child, parts);
            }
            _ => {}
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
///
/// Produces `_RNvC5raven{len}{name}` — a valid v0 symbol under a synthetic
/// "raven" crate path. A full implementation would also encode namespaces,
/// generic arguments, and the actual crate disambiguation hash.
///
/// Reference: <https://rust-lang.github.io/rfcs/2603-rust-symbol-name-mangling-v0.html>
fn mangle_rust_v0(name: InternedString, interner: &Interner) -> String {
    let name_str = interner.resolve(&name);
    // _R = Rust v0 prefix, Nv = value namespace, C5raven = crate "raven"
    format!("_RNvC5raven{}{}", name_str.len(), name_str)
}

// ===== Macro System Integration =====

/// Convert a CST SyntaxNode (representing a token_tree) to a macro TokenStream.
///
/// Walks the tree-sitter CST and produces Token values (Ident, Literal, Punct, Group)
/// that the macro expansion engine can work with.
fn cst_to_token_stream(ctx: &mut LoweringContext, node: &SyntaxNode) -> TokenStream {
    let mut stream = TokenStream::new();

    for child in &node.children {
        match &child.kind {
            SyntaxKind::Identifier => {
                let sym = ctx.intern(&child.text);
                stream.push(Token::Ident(sym));
            }
            SyntaxKind::Type => {
                // Type identifiers are treated as identifiers in token streams
                let sym = ctx.intern(&child.text);
                stream.push(Token::Ident(sym));
            }
            SyntaxKind::Literal => {
                if let Some(token) = parse_literal_token(&child.text) {
                    stream.push(Token::Literal(token));
                }
            }
            SyntaxKind::Unknown(ref s) => {
                match s.as_str() {
                    "token_tree" => {
                        // Nested token tree — determine delimiter from the text
                        let delim = if child.text.starts_with('(') {
                            Delimiter::Paren
                        } else if child.text.starts_with('[') {
                            Delimiter::Bracket
                        } else {
                            Delimiter::Brace
                        };
                        let inner = cst_to_token_stream(ctx, child);
                        stream.push(Token::Group {
                            delim,
                            stream: inner,
                        });
                    }
                    "string_literal" | "raw_string_literal" => {
                        // Extract the string content (strip quotes)
                        let text = &child.text;
                        let content =
                            if text.starts_with('"') && text.ends_with('"') && text.len() >= 2 {
                                text[1..text.len() - 1].to_string()
                            } else {
                                text.clone()
                            };
                        stream.push(Token::Literal(rv_macro::LiteralKind::String(content)));
                    }
                    "integer_literal" => {
                        if let Ok(n) = child.text.parse::<i64>() {
                            stream.push(Token::Literal(rv_macro::LiteralKind::Integer(n)));
                        }
                    }
                    "float_literal" => {
                        if let Ok(f) = child.text.parse::<f64>() {
                            stream.push(Token::Literal(rv_macro::LiteralKind::Float(f)));
                        }
                    }
                    "boolean_literal" => {
                        stream.push(Token::Literal(rv_macro::LiteralKind::Bool(
                            child.text == "true",
                        )));
                    }
                    "metavariable" => {
                        // $x becomes an Ident
                        let sym = ctx.intern(&child.text);
                        stream.push(Token::Ident(sym));
                    }
                    _ => {
                        // Single-character punctuation or other tokens
                        let text = child.text.trim();
                        if text.len() == 1 {
                            let ch = text.chars().next().unwrap();
                            // Skip delimiters — they're handled by the Group parent
                            if ch != '('
                                && ch != ')'
                                && ch != '['
                                && ch != ']'
                                && ch != '{'
                                && ch != '}'
                            {
                                stream.push(Token::Punct(ch));
                            }
                        } else if !text.is_empty() {
                            // Multi-character token — emit as individual punctuation
                            for ch in text.chars() {
                                stream.push(Token::Punct(ch));
                            }
                        }
                    }
                }
            }
            _ => {
                // Recurse into other node types
                let inner = cst_to_token_stream(ctx, child);
                stream.extend(inner);
            }
        }
    }

    stream
}

/// Parse a literal string to a macro LiteralKind
fn parse_literal_token(text: &str) -> Option<rv_macro::LiteralKind> {
    if text.starts_with('"') {
        let content = if text.len() >= 2 {
            text[1..text.len() - 1].to_string()
        } else {
            String::new()
        };
        Some(rv_macro::LiteralKind::String(content))
    } else if text == "true" {
        Some(rv_macro::LiteralKind::Bool(true))
    } else if text == "false" {
        Some(rv_macro::LiteralKind::Bool(false))
    } else if text.contains('.') {
        text.parse::<f64>().ok().map(rv_macro::LiteralKind::Float)
    } else {
        text.parse::<i64>().ok().map(rv_macro::LiteralKind::Integer)
    }
}

/// Convert a TokenStream back to source text for re-parsing through tree-sitter.
fn token_stream_to_source(stream: &TokenStream, interner: &Interner) -> String {
    let mut parts = Vec::new();

    for token in stream.iter() {
        match token {
            Token::Ident(sym) => {
                parts.push(interner.resolve(sym).to_string());
            }
            Token::Literal(lit) => match lit {
                rv_macro::LiteralKind::Integer(n) => parts.push(n.to_string()),
                rv_macro::LiteralKind::Float(f) => parts.push(f.to_string()),
                rv_macro::LiteralKind::String(s) => parts.push(format!("\"{}\"", s)),
                rv_macro::LiteralKind::Bool(b) => parts.push(b.to_string()),
            },
            Token::Punct(ch) => {
                parts.push(ch.to_string());
            }
            Token::Group { delim, stream } => {
                let (open, close) = match delim {
                    Delimiter::Paren => ("(", ")"),
                    Delimiter::Bracket => ("[", "]"),
                    Delimiter::Brace => ("{", "}"),
                };
                let inner = token_stream_to_source(stream, interner);
                parts.push(format!("{}{}{}", open, inner, close));
            }
        }
    }

    parts.join(" ")
}

/// Extract the macro name from a MacroInvocation CST node.
///
/// The tree-sitter macro_invocation has a "macro" field containing an identifier.
fn extract_macro_name(node: &SyntaxNode) -> Option<&str> {
    for child in &node.children {
        match &child.kind {
            SyntaxKind::Identifier => {
                // The macro name (e.g., "println" from "println!()")
                return Some(&child.text);
            }
            SyntaxKind::Unknown(ref s) if s == "scoped_identifier" => {
                // Scoped macro (e.g., std::println) — use full text
                return Some(&child.text);
            }
            _ => {}
        }
    }
    None
}

/// Extract the token_tree arguments from a MacroInvocation CST node.
fn extract_macro_args(node: &SyntaxNode) -> Option<&SyntaxNode> {
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "token_tree" {
                return Some(child);
            }
        }
    }
    None
}

/// Lower a macro invocation in expression position.
///
/// Expands the macro and re-parses the result as an expression.
fn lower_macro_invocation_expr(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    body: &mut Body,
) -> ExprId {
    let file_span = ctx.file_span(node);

    let macro_name = match extract_macro_name(node) {
        Some(name) => name.to_string(),
        None => {
            ctx.report_unhandled(
                DiagnosticSeverity::Error,
                "cannot determine macro name from invocation".to_string(),
                file_span,
            );
            return body.exprs.alloc(Expr::Error { span: file_span });
        }
    };

    // Strip trailing '!' if present (tree-sitter may include it in the identifier)
    let macro_name_clean = macro_name.trim_end_matches('!');
    let name_sym = ctx.intern(macro_name_clean);

    // Build the argument token stream from the CST
    let arguments = match extract_macro_args(node) {
        Some(args_node) => cst_to_token_stream(ctx, args_node),
        None => TokenStream::new(),
    };

    // Expand the macro
    let expanded = match ctx
        .macro_context
        .expand_macro(name_sym, arguments, file_span)
    {
        Ok(ts) => ts,
        Err(err) => {
            ctx.report_unhandled(
                DiagnosticSeverity::Error,
                format!(
                    "macro expansion error for '{}': {:?}",
                    macro_name_clean, err
                ),
                file_span,
            );
            return body.exprs.alloc(Expr::Error { span: file_span });
        }
    };

    // Convert expanded tokens back to source and re-parse as an expression
    let source = token_stream_to_source(&expanded, &ctx.interner);

    // Wrap in a function body so tree-sitter can parse it as a complete unit
    let wrapper = format!("fn __macro_expand__() {{ {} }}", source);

    use rv_syntax::Language;
    let language = lang_raven::RavenLanguage::new();
    match language.parse(&wrapper) {
        Ok(tree) => {
            let root = language.lower_node(&tree.root_node(), &wrapper);

            // Navigate to the expression inside: root > function > block > expression
            if let Some(func_node) = root.children.first() {
                for child in &func_node.children {
                    if child.kind == SyntaxKind::Block {
                        // Find the expression inside the block
                        for block_child in &child.children {
                            match &block_child.kind {
                                SyntaxKind::Unknown(_)
                                | SyntaxKind::Call
                                | SyntaxKind::Literal
                                | SyntaxKind::Identifier
                                | SyntaxKind::BinaryOp
                                | SyntaxKind::If
                                | SyntaxKind::Block
                                | SyntaxKind::MacroInvocation => {
                                    return lower_expr(ctx, current_scope, block_child, body);
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }

            // No recognizable expression found in expanded macro result
            ctx.report_unhandled(
                DiagnosticSeverity::Error,
                format!(
                    "macro '{}' expanded but produced no recognizable expression",
                    macro_name_clean
                ),
                file_span,
            );
            body.exprs.alloc(Expr::Error { span: file_span })
        }
        Err(err) => {
            ctx.report_unhandled(
                DiagnosticSeverity::Error,
                format!(
                    "failed to re-parse expanded macro '{}': {:?}",
                    macro_name_clean, err
                ),
                file_span,
            );
            body.exprs.alloc(Expr::Error { span: file_span })
        }
    }
}

/// Lower a macro invocation in item position.
///
/// Expands the macro and re-parses the result as top-level items.
fn lower_macro_invocation_item(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
) {
    let file_span = ctx.file_span(node);

    let macro_name = match extract_macro_name(node) {
        Some(name) => name.to_string(),
        None => return,
    };

    let macro_name_clean = macro_name.trim_end_matches('!');
    let name_sym = ctx.intern(macro_name_clean);

    let arguments = match extract_macro_args(node) {
        Some(args_node) => cst_to_token_stream(ctx, args_node),
        None => TokenStream::new(),
    };

    let expanded = match ctx
        .macro_context
        .expand_macro(name_sym, arguments, file_span)
    {
        Ok(ts) => ts,
        Err(err) => {
            ctx.report_unhandled(
                DiagnosticSeverity::Error,
                format!(
                    "macro expansion error for '{}' in item position: {:?}",
                    macro_name_clean, err
                ),
                file_span,
            );
            return;
        }
    };

    // Convert expanded tokens back to source and re-parse as items
    let source = token_stream_to_source(&expanded, &ctx.interner);

    use rv_syntax::Language;
    let language = lang_raven::RavenLanguage::new();
    match language.parse(&source) {
        Ok(tree) => {
            let root = language.lower_node(&tree.root_node(), &source);
            lower_items(ctx, current_scope, &root.children);
        }
        Err(err) => {
            ctx.report_unhandled(
                DiagnosticSeverity::Error,
                format!(
                    "failed to re-parse expanded macro '{}' as items: {:?}",
                    macro_name_clean, err
                ),
                file_span,
            );
        }
    }
}

/// Lower a macro_rules! definition and register it in the expansion context.
fn lower_macro_definition(ctx: &mut LoweringContext, node: &SyntaxNode) {
    // Extract the macro name
    let name = node
        .children
        .iter()
        .find(|child| child.kind == SyntaxKind::Identifier)
        .map(|child| child.text.clone());

    let macro_name = match name {
        Some(n) => n,
        None => return,
    };

    let name_sym = ctx.intern(&macro_name);

    // Parse macro rules from the CST children
    let mut rules = Vec::new();
    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            if s == "macro_rule" {
                if let Some(rule) = parse_macro_rule(ctx, child) {
                    rules.push(rule);
                }
            }
        }
    }

    // Allocate a unique macro ID
    let macro_id = rv_macro::MacroId(ctx.next_function_id);
    ctx.next_function_id += 1;

    let file_span = ctx.file_span(node);

    ctx.macro_context.register_macro(MacroDef {
        id: macro_id,
        name: name_sym,
        kind: MacroKind::Declarative { rules },
        span: file_span,
    });
}

/// Parse a single macro_rule CST node into a MacroRule.
///
/// A macro_rule has a "left" field (token_tree_pattern) and a "right" field (token_tree).
fn parse_macro_rule(ctx: &mut LoweringContext, node: &SyntaxNode) -> Option<rv_macro::MacroRule> {
    let mut left_node = None;
    let mut right_node = None;

    for child in &node.children {
        if let SyntaxKind::Unknown(ref s) = child.kind {
            match s.as_str() {
                "token_tree_pattern" => left_node = Some(child),
                "token_tree" => right_node = Some(child),
                _ => {}
            }
        }
    }

    let left = left_node?;
    let right = right_node?;

    let matcher = parse_macro_matcher(ctx, left);
    let expander = parse_macro_expander(ctx, right);

    Some(rv_macro::MacroRule { matcher, expander })
}

/// Parse a token_tree_pattern into a MacroMatcher (group form).
fn parse_macro_matcher(ctx: &mut LoweringContext, node: &SyntaxNode) -> rv_macro::MacroMatcher {
    let mut matchers = Vec::new();

    for child in &node.children {
        match &child.kind {
            SyntaxKind::Identifier => {
                let sym = ctx.intern(&child.text);
                matchers.push(rv_macro::MacroMatcher::Token(Token::Ident(sym)));
            }
            SyntaxKind::Literal => {
                if let Some(lit) = parse_literal_token(&child.text) {
                    matchers.push(rv_macro::MacroMatcher::Token(Token::Literal(lit)));
                }
            }
            SyntaxKind::Unknown(ref s) => match s.as_str() {
                "token_binding_pattern" => {
                    // $x:expr pattern
                    let mut var_name = None;
                    let mut frag_kind = None;

                    for inner in &child.children {
                        if let SyntaxKind::Unknown(ref inner_s) = inner.kind {
                            match inner_s.as_str() {
                                "metavariable" => {
                                    // Strip leading $ from metavariable name
                                    let name = inner.text.trim_start_matches('$');
                                    var_name = Some(ctx.intern(name));
                                }
                                "fragment_specifier" => {
                                    frag_kind = Some(match inner.text.as_str() {
                                        "expr" => rv_macro::FragmentKind::Expr,
                                        "ident" => rv_macro::FragmentKind::Ident,
                                        "ty" => rv_macro::FragmentKind::Ty,
                                        "pat" => rv_macro::FragmentKind::Pat,
                                        "stmt" => rv_macro::FragmentKind::Stmt,
                                        "block" => rv_macro::FragmentKind::Block,
                                        "item" => rv_macro::FragmentKind::Item,
                                        "path" => rv_macro::FragmentKind::Path,
                                        "tt" => rv_macro::FragmentKind::Tt,
                                        _ => rv_macro::FragmentKind::Tt,
                                    });
                                }
                                _ => {}
                            }
                        }
                    }

                    if let (Some(name), Some(kind)) = (var_name, frag_kind) {
                        matchers.push(rv_macro::MacroMatcher::MetaVar { name, kind });
                    }
                }
                "token_repetition_pattern" => {
                    // $(...)*  $(...)+  $(...)?
                    let inner_matchers: Vec<_> = child
                        .children
                        .iter()
                        .filter_map(|inner| {
                            if let SyntaxKind::Unknown(ref inner_s) = inner.kind {
                                if inner_s == "token_tree_pattern" {
                                    return Some(parse_macro_matcher(ctx, inner));
                                }
                            }
                            None
                        })
                        .collect();

                    // Determine sequence kind from the last character of the text
                    let seq_kind = if child.text.ends_with('*') {
                        rv_macro::SequenceKind::ZeroOrMore
                    } else if child.text.ends_with('+') {
                        rv_macro::SequenceKind::OneOrMore
                    } else {
                        rv_macro::SequenceKind::Optional
                    };

                    // Detect separator: the character between the closing ')' and the
                    // repeat operator (e.g., the ',' in `$($x:expr),*`).
                    let separator = {
                        let trimmed = child.text.trim();
                        // Strip the trailing repeat operator (*, +, ?)
                        let without_op = &trimmed[..trimmed.len().saturating_sub(1)];
                        // If the last char before the operator is punctuation (not ')'),
                        // it's a separator token.
                        without_op.chars().last().and_then(|ch| {
                            if ch != ')' && ch != ']' && ch != '}' && ch.is_ascii_punctuation() {
                                Some(rv_macro::Token::Punct(ch))
                            } else {
                                None
                            }
                        })
                    };

                    matchers.push(rv_macro::MacroMatcher::Sequence {
                        matchers: inner_matchers,
                        separator,
                        kind: seq_kind,
                    });
                }
                "token_tree_pattern" => {
                    let delim = if child.text.starts_with('(') {
                        Delimiter::Paren
                    } else if child.text.starts_with('[') {
                        Delimiter::Bracket
                    } else {
                        Delimiter::Brace
                    };
                    let inner = parse_macro_matcher(ctx, child);
                    if let rv_macro::MacroMatcher::Group {
                        matchers: inner_ms, ..
                    } = inner
                    {
                        matchers.push(rv_macro::MacroMatcher::Group {
                            delimiter: delim,
                            matchers: inner_ms,
                        });
                    } else {
                        matchers.push(rv_macro::MacroMatcher::Group {
                            delimiter: delim,
                            matchers: vec![inner],
                        });
                    }
                }
                _ => {
                    // Punctuation or other tokens
                    let text = child.text.trim();
                    for ch in text.chars() {
                        if ch != '('
                            && ch != ')'
                            && ch != '['
                            && ch != ']'
                            && ch != '{'
                            && ch != '}'
                        {
                            matchers.push(rv_macro::MacroMatcher::Token(Token::Punct(ch)));
                        }
                    }
                }
            },
            _ => {}
        }
    }

    rv_macro::MacroMatcher::Group {
        delimiter: Delimiter::Paren,
        matchers,
    }
}

/// Parse a token_tree into a MacroExpander (group form).
fn parse_macro_expander(ctx: &mut LoweringContext, node: &SyntaxNode) -> rv_macro::MacroExpander {
    let mut expanders = Vec::new();

    for child in &node.children {
        match &child.kind {
            SyntaxKind::Identifier => {
                let sym = ctx.intern(&child.text);
                expanders.push(rv_macro::MacroExpander::Token(Token::Ident(sym)));
            }
            SyntaxKind::Literal => {
                if let Some(lit) = parse_literal_token(&child.text) {
                    expanders.push(rv_macro::MacroExpander::Token(Token::Literal(lit)));
                }
            }
            SyntaxKind::Unknown(ref s) => match s.as_str() {
                "metavariable" => {
                    let name = child.text.trim_start_matches('$');
                    let sym = ctx.intern(name);
                    expanders.push(rv_macro::MacroExpander::Substitute(sym));
                }
                "token_repetition" => {
                    let inner_expanders: Vec<_> = child
                        .children
                        .iter()
                        .filter_map(|inner| {
                            if let SyntaxKind::Unknown(ref inner_s) = inner.kind {
                                if inner_s == "token_tree" {
                                    return Some(parse_macro_expander(ctx, inner));
                                }
                            }
                            None
                        })
                        .collect();

                    let seq_kind = if child.text.ends_with('*') {
                        rv_macro::SequenceKind::ZeroOrMore
                    } else if child.text.ends_with('+') {
                        rv_macro::SequenceKind::OneOrMore
                    } else {
                        rv_macro::SequenceKind::Optional
                    };

                    // Detect separator from the text (same logic as matcher)
                    let separator = {
                        let trimmed = child.text.trim();
                        let without_op = &trimmed[..trimmed.len().saturating_sub(1)];
                        without_op.chars().last().and_then(|ch| {
                            if ch != ')' && ch != ']' && ch != '}' && ch.is_ascii_punctuation() {
                                Some(rv_macro::Token::Punct(ch))
                            } else {
                                None
                            }
                        })
                    };

                    expanders.push(rv_macro::MacroExpander::Sequence {
                        expanders: inner_expanders,
                        separator,
                        kind: seq_kind,
                    });
                }
                "token_tree" => {
                    let delim = if child.text.starts_with('(') {
                        Delimiter::Paren
                    } else if child.text.starts_with('[') {
                        Delimiter::Bracket
                    } else {
                        Delimiter::Brace
                    };
                    let inner = parse_macro_expander(ctx, child);
                    if let rv_macro::MacroExpander::Group {
                        expanders: inner_es,
                        ..
                    } = inner
                    {
                        expanders.push(rv_macro::MacroExpander::Group {
                            delimiter: delim,
                            expanders: inner_es,
                        });
                    } else {
                        expanders.push(rv_macro::MacroExpander::Group {
                            delimiter: delim,
                            expanders: vec![inner],
                        });
                    }
                }
                _ => {
                    let text = child.text.trim();
                    for ch in text.chars() {
                        if ch != '('
                            && ch != ')'
                            && ch != '['
                            && ch != ']'
                            && ch != '{'
                            && ch != '}'
                        {
                            expanders.push(rv_macro::MacroExpander::Token(Token::Punct(ch)));
                        }
                    }
                }
            },
            _ => {}
        }
    }

    rv_macro::MacroExpander::Group {
        delimiter: Delimiter::Brace,
        expanders,
    }
}

/// Lower a const item: `const NAME: Type = expr;`
fn lower_const_item(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    let file_span = ctx.file_span(node);
    let visibility = parse_visibility(node);

    // Extract name
    let name = node
        .children
        .iter()
        .find(|c| c.kind == SyntaxKind::Identifier)
        .map(|c| ctx.intern(&c.text));

    let name = match name {
        Some(n) => n,
        None => return, // Skip malformed const items
    };

    // Extract type annotation
    let ty = node
        .children
        .iter()
        .find(|c| c.kind == SyntaxKind::Type)
        .map(|c| lower_type_node(ctx, c));

    let ty = match ty {
        Some(t) => t,
        None => ctx.types.alloc(Type::Unknown { span: file_span }),
    };

    // Extract value expression (must come after the `=` sign to avoid
    // picking up the const name identifier as the expression)
    let mut body = Body::new();
    let fn_scope = ctx.scope_tree.create_child(current_scope, node.span);
    let mut past_equals = false;
    for child in &node.children {
        if child.text == "=" {
            past_equals = true;
            continue;
        }
        if past_equals && is_expr_node(child) {
            let expr = lower_expr(ctx, fn_scope, child, &mut body);
            body.root_expr = expr;
            break;
        }
    }

    let const_id = ctx.alloc_const_id();
    let const_item = ConstItem {
        id: const_id,
        name,
        ty,
        body,
        attributes: attrs,
        visibility,
        span: file_span,
    };

    ctx.const_items.insert(const_id, const_item);

    // Register in scope so other items can reference the constant
    let symbol_id = ctx
        .symbols
        .add(name, SymbolKind::Const, node.span, current_scope);
    ctx.scope_tree.add_symbol(
        current_scope,
        ctx.interner.resolve(&name).to_string(),
        symbol_id,
    );

    // Map symbol to DefId::Const so variable references resolve correctly
    let def_id = DefId::Const(const_id);
    ctx.symbol_defs.insert(symbol_id, def_id);
}

/// Lower a static item: `static [mut] NAME: Type = expr;`
fn lower_static_item(
    ctx: &mut LoweringContext,
    current_scope: ScopeId,
    node: &SyntaxNode,
    attrs: Vec<Attribute>,
) {
    let file_span = ctx.file_span(node);
    let visibility = parse_visibility(node);

    // Check for `mut`
    let mutable = node.children.iter().any(|c| {
        matches!(&c.kind, SyntaxKind::Unknown(ref s) if s == "mutable_specifier") || c.text == "mut"
    });

    // Extract name
    let name = node
        .children
        .iter()
        .find(|c| c.kind == SyntaxKind::Identifier)
        .map(|c| ctx.intern(&c.text));

    let name = match name {
        Some(n) => n,
        None => return,
    };

    // Extract type annotation
    let ty = node
        .children
        .iter()
        .find(|c| c.kind == SyntaxKind::Type)
        .map(|c| lower_type_node(ctx, c));

    let ty = match ty {
        Some(t) => t,
        None => ctx.types.alloc(Type::Unknown { span: file_span }),
    };

    // Extract value expression (must come after the `=` sign to avoid
    // picking up the static name identifier as the expression)
    let mut body = Body::new();
    let fn_scope = ctx.scope_tree.create_child(current_scope, node.span);
    let mut past_equals = false;
    for child in &node.children {
        if child.text == "=" {
            past_equals = true;
            continue;
        }
        if past_equals && is_expr_node(child) {
            let expr = lower_expr(ctx, fn_scope, child, &mut body);
            body.root_expr = expr;
            break;
        }
    }

    let static_id = ctx.alloc_static_id();
    let static_item = StaticItem {
        id: static_id,
        name,
        ty,
        body,
        mutable,
        attributes: attrs,
        visibility,
        span: file_span,
    };

    ctx.static_items.insert(static_id, static_item);

    // Register in scope
    let symbol_id = ctx
        .symbols
        .add(name, SymbolKind::Static, node.span, current_scope);
    ctx.scope_tree.add_symbol(
        current_scope,
        ctx.interner.resolve(&name).to_string(),
        symbol_id,
    );

    // Map symbol to DefId::Static so variable references resolve correctly
    let def_id = DefId::Static(static_id);
    ctx.symbol_defs.insert(symbol_id, def_id);
}

/// Lower a type alias: `type Name<T> = AliasedType;`
fn lower_type_alias(ctx: &mut LoweringContext, node: &SyntaxNode, attrs: Vec<Attribute>) {
    let file_span = ctx.file_span(node);
    let visibility = parse_visibility(node);

    // Extract name
    let name = node
        .children
        .iter()
        .find(|c| c.kind == SyntaxKind::Identifier || c.kind == SyntaxKind::Type)
        .map(|c| ctx.intern(&c.text));

    let name = match name {
        Some(n) => n,
        None => return,
    };

    // Extract generic parameters
    let mut generic_params = Vec::new();
    for child in &node.children {
        if child.kind == SyntaxKind::GenericParams {
            generic_params = parse_generic_params(ctx, child);
            break;
        }
    }

    // Find the aliased type — it's the type node after "="
    let mut found_eq = false;
    let mut aliased_type = None;
    for child in &node.children {
        if child.text == "=" {
            found_eq = true;
            continue;
        }
        if found_eq
            && (child.kind == SyntaxKind::Type
                || matches!(&child.kind, SyntaxKind::Unknown(ref s) if s == "generic_type" || s == "scoped_type_identifier" || s == "reference_type" || s == "tuple_type" || s == "array_type" || s == "function_type"))
        {
            aliased_type = Some(lower_type_node(ctx, child));
            break;
        }
    }

    let aliased_type = match aliased_type {
        Some(t) => t,
        None => ctx.types.alloc(Type::Unknown { span: file_span }),
    };

    let type_alias_id = ctx.alloc_type_alias_id();
    let type_alias = TypeAlias {
        id: type_alias_id,
        name,
        generic_params,
        aliased_type,
        attributes: attrs,
        visibility,
        span: file_span,
    };

    ctx.type_aliases.insert(type_alias_id, type_alias);
}
