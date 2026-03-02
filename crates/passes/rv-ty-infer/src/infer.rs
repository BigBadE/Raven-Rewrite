//! Type inference
#![allow(
    clippy::min_ident_chars,
    reason = "Ty and TyId are conventional names in type system implementations"
)]

use crate::bounds::BoundError;
use crate::constraint::{ConstraintSource, Constraints};
use crate::context::TyContext;
use crate::module_context::ModuleTypeContext;
use crate::ty::{TyId, TyKind};
use crate::unify::{UnificationError, Unifier};
use rv_hir::{Body, Expr, ExprId, Function, LiteralKind, Stmt, StmtId};

/// Type inference result
pub struct InferenceResult {
    /// Type context with inferred types
    pub ctx: TyContext,
    /// Errors encountered during inference
    pub errors: Vec<TypeError>,
    /// Lifetime outlives constraints: (sub, sup, source_expr)
    /// sub's lifetime must outlive sup's lifetime
    pub lifetime_constraints: Vec<(rv_span::LifetimeId, rv_span::LifetimeId, Option<ExprId>)>,
}

/// Type error
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    /// Unification error
    Unification {
        /// Unification error
        error: UnificationError,
        /// Expression where error occurred
        expr: Option<ExprId>,
    },
    /// Undefined variable
    UndefinedVariable {
        /// Expression
        expr: ExprId,
    },
    /// Trait bound not satisfied
    BoundError {
        /// The bound error details
        error: BoundError,
        /// Expression where error occurred
        expr: Option<ExprId>,
    },
    /// Calling an unsafe function outside an unsafe context
    UnsafeCallInSafeContext {
        /// Source location of the call
        span: rv_span::FileSpan,
    },
}

/// Type inference engine
pub struct TypeInference<'a> {
    ctx: TyContext,
    errors: Vec<TypeError>,
    /// Stack of scopes, each mapping variable names to their inferred types
    /// Inner scopes shadow outer scopes
    scope_stack: Vec<rustc_hash::FxHashMap<rv_intern::Symbol, TyId>>,
    /// Reference to impl blocks for method resolution
    impl_blocks: Option<&'a std::collections::HashMap<rv_hir::ImplId, rv_hir::ImplBlock>>,
    /// Reference to functions for method resolution
    functions: Option<&'a std::collections::HashMap<rv_hir::FunctionId, rv_hir::Function>>,
    /// Reference to HIR types for type conversion
    hir_types: Option<&'a la_arena::Arena<rv_hir::Type>>,
    /// Reference to struct definitions for type conversion
    structs: Option<&'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>>,
    /// Reference to enum definitions for variant type lookup
    enums: Option<&'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::EnumDef>>,
    /// Reference to trait definitions for dyn Trait resolution
    trait_defs: Option<&'a std::collections::HashMap<rv_hir::TraitId, rv_hir::TraitDef>>,
    /// Reference to const items for type registration
    const_items: Option<&'a std::collections::HashMap<rv_hir::ConstId, rv_hir::ConstItem>>,
    /// Reference to static items for type registration
    static_items: Option<&'a std::collections::HashMap<rv_hir::StaticId, rv_hir::StaticItem>>,

    /// Reference to interner for resolving type names
    interner: Option<&'a rv_intern::Interner>,
    /// Cache for HIR TypeId → TyId conversions to prevent infinite recursion
    type_conversion_cache: rustc_hash::FxHashMap<rv_hir::TypeId, TyId>,
    /// Expected return type for the current function being inferred
    current_function_return_ty: Option<TyId>,
    /// Stack tracking variable mutability (variable name → is_mutable)
    var_mutability: Vec<rustc_hash::FxHashMap<rv_intern::Symbol, bool>>,
    /// Receiver mutability for method calls (ExprId → is_mutable)
    receiver_mutability: rustc_hash::FxHashMap<ExprId, bool>,
    /// Constraint generation mode (generate constraints instead of immediate unification)
    generate_mode: bool,
    /// Constraints collected during constraint generation mode
    constraints: Constraints,
    /// Reference to module context for constraint generation
    module_ctx: Option<&'a mut ModuleTypeContext>,
    /// Map from generic parameter names to type variables (for current function being inferred)
    /// This ensures all occurrences of the same generic parameter T map to the same type variable
    generic_param_map: rustc_hash::FxHashMap<rv_intern::Symbol, TyId>,
    /// True if set_generic_bindings() was called for the current function, indicating
    /// concrete type bindings are pre-set for monomorphization (don't create fresh vars)
    generic_bindings_preset: bool,
    /// Next lifetime ID for fresh lifetime generation during reference type creation
    next_lifetime_id: u32,
    /// Lifetime outlives constraints collected during inference (sub, sup, source_expr)
    /// These are forwarded to the borrow checker's LifetimeContext after inference completes
    lifetime_constraints: Vec<(rv_span::LifetimeId, rv_span::LifetimeId, Option<ExprId>)>,
    /// Tracks nesting depth of unsafe contexts (unsafe blocks, unsafe fn bodies)
    /// When > 0, operations requiring unsafe (raw pointer deref, unsafe fn calls) are allowed
    unsafe_depth: u32,
}

impl<'a> TypeInference<'a> {
    /// Create a new type inference engine
    pub fn new() -> Self {
        Self {
            ctx: TyContext::new(),
            errors: vec![],
            scope_stack: vec![rustc_hash::FxHashMap::default()], // Start with one global scope
            impl_blocks: None,
            functions: None,
            hir_types: None,
            structs: None,
            enums: None,
            trait_defs: None,
            const_items: None,
            static_items: None,
            interner: None,
            type_conversion_cache: rustc_hash::FxHashMap::default(),
            current_function_return_ty: None,
            var_mutability: vec![rustc_hash::FxHashMap::default()],
            receiver_mutability: rustc_hash::FxHashMap::default(),
            generate_mode: false,
            generic_param_map: rustc_hash::FxHashMap::default(),
            generic_bindings_preset: false,
            constraints: Constraints::new(),
            module_ctx: None,
            next_lifetime_id: 0,
            lifetime_constraints: Vec::new(),
            unsafe_depth: 0,
        }
    }

    /// Create a new type inference engine with HIR context for method resolution
    pub fn with_hir_context(
        impl_blocks: &'a std::collections::HashMap<rv_hir::ImplId, rv_hir::ImplBlock>,
        functions: &'a std::collections::HashMap<rv_hir::FunctionId, rv_hir::Function>,
        hir_types: &'a la_arena::Arena<rv_hir::Type>,
        structs: &'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
        enums: &'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::EnumDef>,
        interner: &'a rv_intern::Interner,
    ) -> Self {
        Self::with_hir_context_and_tyctx(
            impl_blocks,
            functions,
            hir_types,
            structs,
            enums,
            interner,
            TyContext::new(),
        )
    }

    /// Create a type inference context with HIR context and a custom TyContext
    /// This is useful for monomorphization where we need to pre-populate the TyContext
    /// with concrete types for generic parameters
    pub fn with_hir_context_and_tyctx(
        impl_blocks: &'a std::collections::HashMap<rv_hir::ImplId, rv_hir::ImplBlock>,
        functions: &'a std::collections::HashMap<rv_hir::FunctionId, rv_hir::Function>,
        hir_types: &'a la_arena::Arena<rv_hir::Type>,
        structs: &'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
        enums: &'a std::collections::HashMap<rv_hir::TypeDefId, rv_hir::EnumDef>,
        interner: &'a rv_intern::Interner,
        ctx: TyContext,
    ) -> Self {
        Self {
            ctx,
            errors: vec![],
            scope_stack: vec![rustc_hash::FxHashMap::default()], // Start with one global scope
            impl_blocks: Some(impl_blocks),
            functions: Some(functions),
            hir_types: Some(hir_types),
            structs: Some(structs),
            enums: Some(enums),
            trait_defs: None,
            const_items: None,
            static_items: None,
            interner: Some(interner),
            type_conversion_cache: rustc_hash::FxHashMap::default(),
            current_function_return_ty: None,
            var_mutability: vec![rustc_hash::FxHashMap::default()],
            receiver_mutability: rustc_hash::FxHashMap::default(),
            generate_mode: false,
            generic_param_map: rustc_hash::FxHashMap::default(),
            generic_bindings_preset: false,
            constraints: Constraints::new(),
            module_ctx: None,
            next_lifetime_id: 0,
            lifetime_constraints: Vec::new(),
            unsafe_depth: 0,
        }
    }

    /// Set trait definitions for dyn Trait resolution
    pub fn set_trait_defs(
        &mut self,
        trait_defs: &'a std::collections::HashMap<rv_hir::TraitId, rv_hir::TraitDef>,
    ) {
        self.trait_defs = Some(trait_defs);
    }

    /// Set const and static item definitions for type registration.
    ///
    /// This registers the declared types of all const and static items in the TyContext
    /// so that when `Expr::Variable { def: DefId::Const(..) }` is encountered during
    /// inference, `ctx.get_def_type()` returns the correct type.
    pub fn set_const_static_items(
        &mut self,
        const_items: &'a std::collections::HashMap<rv_hir::ConstId, rv_hir::ConstItem>,
        static_items: &'a std::collections::HashMap<rv_hir::StaticId, rv_hir::StaticItem>,
    ) {
        self.const_items = Some(const_items);
        self.static_items = Some(static_items);

        // Register types for all const items in the TyContext
        if let (Some(hir_types), Some(structs), Some(interner)) =
            (self.hir_types, self.structs, self.interner)
        {
            for (const_id, const_item) in const_items {
                let ty = self.hir_type_to_ty_id(const_item.ty, hir_types, structs, interner);
                self.ctx.set_def_type(rv_hir::DefId::Const(*const_id), ty);
            }
            for (static_id, static_item) in static_items {
                let ty = self.hir_type_to_ty_id(static_item.ty, hir_types, structs, interner);
                self.ctx.set_def_type(rv_hir::DefId::Static(*static_id), ty);
            }
        }
    }

    /// Enable constraint generation mode
    pub fn enable_constraint_generation(&mut self, module_ctx: &'a mut ModuleTypeContext) {
        self.generate_mode = true;
        self.module_ctx = Some(module_ctx);
    }

    /// Get the collected constraints
    #[must_use]
    pub fn take_constraints(&mut self) -> Constraints {
        std::mem::take(&mut self.constraints)
    }

    /// Get the type context
    #[must_use]
    pub fn context(&self) -> &TyContext {
        &self.ctx
    }

    /// Get a mutable reference to the type context
    #[must_use]
    pub fn context_mut(&mut self) -> &mut TyContext {
        &mut self.ctx
    }

    /// Allocate a fresh lifetime ID for a new reference type
    fn fresh_lifetime(&mut self) -> rv_span::LifetimeId {
        let id = rv_span::LifetimeId(self.next_lifetime_id);
        self.next_lifetime_id += 1;
        id
    }

    /// Add a lifetime outlives constraint: `sub` must outlive `sup`
    fn add_lifetime_outlives(
        &mut self,
        sub: rv_span::LifetimeId,
        sup: rv_span::LifetimeId,
        source_expr: Option<ExprId>,
    ) {
        self.lifetime_constraints.push((sub, sup, source_expr));
    }

    /// Get the lifetime constraints collected during inference
    #[must_use]
    pub fn lifetime_constraints(
        &self,
    ) -> &[(rv_span::LifetimeId, rv_span::LifetimeId, Option<ExprId>)] {
        &self.lifetime_constraints
    }

    /// Extract the lifetime ID from a TyKind::Ref, if present
    fn ref_lifetime(&self, ty_id: TyId) -> Option<rv_span::LifetimeId> {
        match &self.ctx.types.get(ty_id).kind {
            TyKind::Ref { lifetime, .. } => *lifetime,
            _ => None,
        }
    }

    /// Bind a variable name to a concrete type in the global scope
    /// This is used for monomorphization to bind generic type parameters to concrete types
    pub fn bind_type_in_global_scope(&mut self, name: rv_intern::Symbol, ty: TyId) {
        if let Some(global_scope) = self.scope_stack.first_mut() {
            global_scope.insert(name, ty);
        }
    }

    /// Pre-set generic parameter bindings for monomorphization.
    ///
    /// When instantiating a generic function with concrete types (e.g., calling `max<i64>`),
    /// this method should be called BEFORE `infer_function` to bind each generic parameter
    /// to its concrete type. This prevents `infer_function` from creating fresh type variables
    /// that would remain unresolved.
    ///
    /// # Arguments
    /// * `bindings` - A map from generic parameter names to their concrete TyIds
    pub fn set_generic_bindings(
        &mut self,
        bindings: impl IntoIterator<Item = (rv_intern::Symbol, TyId)>,
    ) {
        self.generic_param_map.clear();
        for (name, ty_id) in bindings {
            self.generic_param_map.insert(name, ty_id);
        }
        // Mark that bindings were pre-set so infer_function doesn't overwrite them
        self.generic_bindings_preset = true;
    }

    /// Push a new scope onto the scope stack
    fn push_scope(&mut self) {
        self.scope_stack.push(rustc_hash::FxHashMap::default());
        self.var_mutability.push(rustc_hash::FxHashMap::default());
    }

    /// Pop the current scope from the scope stack
    fn pop_scope(&mut self) {
        if self.scope_stack.len() > 1 {
            self.scope_stack.pop();
            self.var_mutability.pop();
        }
    }

    /// Insert a variable into the current scope
    fn insert_var(&mut self, name: rv_intern::Symbol, ty: TyId) {
        if let Some(current_scope) = self.scope_stack.last_mut() {
            current_scope.insert(name, ty);
        }
    }

    /// Look up a variable by name, searching from innermost to outermost scope
    fn lookup_var(&self, name: rv_intern::Symbol) -> Option<TyId> {
        // Search from innermost scope (last in vec) to outermost (first in vec)
        for scope in self.scope_stack.iter().rev() {
            if let Some(&ty) = scope.get(&name) {
                return Some(ty);
            }
        }
        None
    }

    /// Insert variable mutability into the current scope
    fn insert_var_mutability(&mut self, name: rv_intern::Symbol, is_mutable: bool) {
        if let Some(current_scope) = self.var_mutability.last_mut() {
            current_scope.insert(name, is_mutable);
        }
    }

    /// Check if a local variable is mutable
    fn is_local_mutable(&self, name: rv_intern::Symbol) -> bool {
        // Search from innermost scope to outermost
        for scope in self.var_mutability.iter().rev() {
            if let Some(&is_mut) = scope.get(&name) {
                return is_mut;
            }
        }
        false // Default to immutable if not found
    }

    /// Resolve a call expression's callee to a FunctionId, if possible.
    fn resolve_callee_function(&self, body: &Body, callee: ExprId) -> Option<rv_hir::FunctionId> {
        match &body.exprs[callee] {
            Expr::Variable {
                def: Some(rv_hir::DefId::Function(fid)),
                ..
            } => Some(*fid),
            _ => None,
        }
    }

    /// Recursively check if an expression is mutable
    fn is_expr_mutable(&self, body: &Body, expr_id: ExprId) -> bool {
        let expr = &body.exprs[expr_id];

        match expr {
            Expr::Variable { name, .. } => {
                // Check if the variable was declared mutable
                self.is_local_mutable(*name)
            }
            Expr::Field { base, .. } => {
                // Field access is mutable if base is mutable
                self.is_expr_mutable(body, *base)
            }
            _ => {
                // Other expressions (temporaries, literals) are not mutable
                false
            }
        }
    }

    /// Infer types for pattern bindings and register them in the variable scope.
    ///
    /// For match patterns like `Option::Some(v)`, this extracts the type of `v` from
    /// the scrutinee type and registers it so that `v` can be used in the arm body.
    fn infer_pattern_bindings(&mut self, body: &Body, pattern: &rv_hir::Pattern, scrutinee_ty: TyId) {
        match pattern {
            rv_hir::Pattern::Binding { name, .. } => {
                // Register the binding with the scrutinee type (the whole matched value)
                self.insert_var(*name, scrutinee_ty);
            }
            rv_hir::Pattern::Enum { sub_patterns, def, .. } => {
                // For enum patterns, extract field types from the scrutinee
                // scrutinee_ty should be TyKind::Named { def, args }
                let resolved_ty = self.ctx.follow_var(scrutinee_ty);
                let ty_kind = self.ctx.types.get(resolved_ty).kind.clone();

                if let TyKind::Named { args, def: ty_def, .. } = ty_kind {
                    // Get the enum definition to find field types
                    let enum_def_id = def.or(Some(ty_def));
                    if let (Some(enum_def_id), Some(enums)) = (enum_def_id, self.enums) {
                        if let Some(enum_def) = enums.get(&enum_def_id) {
                            // Find this variant in the enum definition
                            // Note: we need the variant name, which is in the Pattern::Enum
                            // For now, assume sub_patterns correspond to generic args for simple cases
                            // like Option::Some(v) where v gets the type arg
                            for (idx, sub_pat_id) in sub_patterns.iter().enumerate() {
                                let sub_pattern = &body.patterns[*sub_pat_id];
                                // If the sub-pattern is a binding, register it with the appropriate type
                                // For Option<T>, Some(v) means v has type T, which is args[0]
                                let field_ty = if idx < args.len() {
                                    args[idx]
                                } else {
                                    // Fallback to fresh type variable
                                    self.ctx.fresh_ty_var()
                                };
                                self.infer_pattern_bindings(body, sub_pattern, field_ty);
                            }
                            let _ = enum_def; // Suppress unused warning - needed for pattern matching
                        }
                    }
                }
            }
            rv_hir::Pattern::Tuple { patterns, .. } => {
                // For tuple patterns, extract element types
                let resolved_ty = self.ctx.follow_var(scrutinee_ty);
                let ty_kind = self.ctx.types.get(resolved_ty).kind.clone();

                if let TyKind::Tuple { elements } = ty_kind {
                    for (idx, sub_pat_id) in patterns.iter().enumerate() {
                        let sub_pattern = &body.patterns[*sub_pat_id];
                        let elem_ty = if idx < elements.len() {
                            elements[idx]
                        } else {
                            self.ctx.fresh_ty_var()
                        };
                        self.infer_pattern_bindings(body, sub_pattern, elem_ty);
                    }
                }
            }
            rv_hir::Pattern::Struct { fields, .. } => {
                // For struct patterns, extract field types by name
                let resolved_ty = self.ctx.follow_var(scrutinee_ty);
                let ty_kind = self.ctx.types.get(resolved_ty).kind.clone();

                if let TyKind::Struct { fields: struct_fields, .. } = ty_kind {
                    for (field_name, sub_pat_id) in fields {
                        let sub_pattern = &body.patterns[*sub_pat_id];
                        let field_ty = struct_fields
                            .iter()
                            .find(|(name, _)| name == field_name)
                            .map(|(_, ty)| *ty)
                            .unwrap_or_else(|| self.ctx.fresh_ty_var());
                        self.infer_pattern_bindings(body, sub_pattern, field_ty);
                    }
                }
            }
            rv_hir::Pattern::Or { patterns, .. } => {
                // For or-patterns, all alternatives should bind the same variables
                // with the same types, so we just process the first one
                if let Some(first_pat_id) = patterns.first() {
                    let first_pattern = &body.patterns[*first_pat_id];
                    self.infer_pattern_bindings(body, first_pattern, scrutinee_ty);
                }
            }
            rv_hir::Pattern::Slice { prefix, rest, suffix, .. } => {
                // For slice patterns, extract element type from the scrutinee
                let resolved_ty = self.ctx.follow_var(scrutinee_ty);
                let ty_kind = self.ctx.types.get(resolved_ty).kind.clone();

                // Get element type from Array or Slice type
                let elem_ty = match ty_kind {
                    TyKind::Array { element, .. } => *element,
                    TyKind::Slice { element } => *element,
                    _ => self.ctx.fresh_ty_var(),
                };

                // Process prefix patterns
                for sub_pat_id in prefix {
                    let sub_pattern = &body.patterns[*sub_pat_id];
                    self.infer_pattern_bindings(body, sub_pattern, elem_ty);
                }

                // Process rest pattern (if any) - binds to the remaining slice
                if let Some(rest_pat_id) = rest {
                    let rest_pattern = &body.patterns[*rest_pat_id];
                    // Rest binds to a slice of the element type
                    let slice_ty = self.ctx.types.alloc(TyKind::Slice {
                        element: Box::new(elem_ty),
                    });
                    self.infer_pattern_bindings(body, rest_pattern, slice_ty);
                }

                // Process suffix patterns
                for sub_pat_id in suffix {
                    let sub_pattern = &body.patterns[*sub_pat_id];
                    self.infer_pattern_bindings(body, sub_pattern, elem_ty);
                }
            }
            // These patterns don't introduce bindings
            rv_hir::Pattern::Wildcard { .. }
            | rv_hir::Pattern::Literal { .. }
            | rv_hir::Pattern::Range { .. } => {}
        }
    }

    /// Infer types for a function
    pub fn infer_function(&mut self, function: &Function) {
        // Clear type conversion cache between functions to avoid stale type variable references.
        // Types containing generic parameters get cached with function-specific type variables,
        // and those type variables won't be resolved in subsequent functions.
        self.type_conversion_cache.clear();

        // Populate generic parameter map for this function.
        // If set_generic_bindings() was called beforehand (for monomorphization),
        // use those bindings instead of creating fresh type variables.
        // Otherwise, clear and create fresh type variables.
        if self.generic_bindings_preset {
            // Bindings were pre-set by set_generic_bindings(), use them
            // Reset the flag for next function
            self.generic_bindings_preset = false;
        } else {
            // No pre-set bindings, create fresh type variables for each generic param
            self.generic_param_map.clear();
            for generic_param in &function.generics {
                let ty_var = self.ctx.fresh_ty_var();
                self.generic_param_map.insert(generic_param.name, ty_var);
            }
        }

        // Set expected return type
        self.current_function_return_ty = function.return_type.and_then(|return_ty_id| {
            if let (Some(hir_types), Some(structs), Some(interner)) =
                (self.hir_types, self.structs, self.interner)
            {
                Some(self.hir_type_to_ty_id(return_ty_id, hir_types, structs, interner))
            } else {
                None
            }
        });

        // ARCHITECTURE: Initialize parameter types from HIR type annotations
        // NO fallbacks - HIR context is REQUIRED for type inference
        let hir_types = self
            .hir_types
            .expect("HIR types required for type inference");
        let structs = self.structs.expect("Structs required for type inference");
        let interner = self.interner.expect("Interner required for type inference");

        for (param_idx, param) in function.parameters.iter().enumerate() {
            let local_id = rv_hir::LocalId(param_idx as u32);
            let def_id = rv_hir::DefId::Local {
                func: function.id,
                local: local_id,
            };

            // ARCHITECTURE: Check if monomorphization already set a concrete type
            // If def_types already contains a concrete type (not a type variable),
            // use that instead of converting from HIR (which creates type variables for generics)
            let param_ty = if let Some(existing_ty) = self.ctx.get_def_type(def_id) {
                // Check if it's a concrete type (not a type variable)
                match &self.ctx.types.get(existing_ty).kind {
                    TyKind::Var { .. } | TyKind::IntVar { .. } | TyKind::FloatVar { .. } => {
                        // It's an inference variable, convert from HIR
                        self.hir_type_to_ty_id(param.ty, hir_types, structs, interner)
                    }
                    _ => {
                        // It's a concrete type from monomorphization - use it
                        existing_ty
                    }
                }
            } else {
                // No existing type, convert from HIR
                self.hir_type_to_ty_id(param.ty, hir_types, structs, interner)
            };

            // ARCHITECTURE: Store type by DefId (structured ID, not Symbol name)
            self.ctx.set_def_type(def_id, param_ty);

            // Also keep in var map for local variable tracking
            self.insert_var(param.name, param_ty);
        }

        // Unsafe functions have an implicit unsafe context for their entire body
        if function.is_unsafe {
            self.unsafe_depth += 1;
        }

        // Infer body
        self.infer_body(&function.body);

        // Restore unsafe depth after function
        if function.is_unsafe {
            self.unsafe_depth -= 1;
        }

        // Clear expected return type after function
        self.current_function_return_ty = None;
    }

    /// Convert HIR TypeId to type inference TyId
    fn hir_type_to_ty_id(
        &mut self,
        hir_ty_id: rv_hir::TypeId,
        hir_types: &la_arena::Arena<rv_hir::Type>,
        structs: &std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
        interner: &rv_intern::Interner,
    ) -> TyId {
        self.hir_type_to_ty_id_impl(hir_ty_id, hir_types, structs, interner, 0)
    }

    fn hir_type_to_ty_id_impl(
        &mut self,
        hir_ty_id: rv_hir::TypeId,
        hir_types: &la_arena::Arena<rv_hir::Type>,
        structs: &std::collections::HashMap<rv_hir::TypeDefId, rv_hir::StructDef>,
        interner: &rv_intern::Interner,
        depth: usize,
    ) -> TyId {
        // Prevent infinite recursion with depth limit
        if depth > 50 {
            // Too deep - likely a cycle, return a type variable
            return self.ctx.fresh_ty_var();
        }

        // Check cache first to prevent redundant conversions
        if let Some(&cached_ty) = self.type_conversion_cache.get(&hir_ty_id) {
            return cached_ty;
        }

        let hir_type = &hir_types[hir_ty_id];

        let result_ty = match hir_type {
            rv_hir::Type::Named { name, def, args, .. } => {
                // If it's a struct with resolved definition, create proper struct type
                if let Some(type_def_id) = def {
                    if let Some(struct_def) = structs.get(type_def_id) {
                        // Create struct type with fields
                        let field_types: Vec<(rv_intern::Symbol, TyId)> = struct_def
                            .fields
                            .iter()
                            .map(|field| {
                                let field_ty = self.hir_type_to_ty_id_impl(
                                    field.ty,
                                    hir_types,
                                    structs,
                                    interner,
                                    depth + 1,
                                );
                                (field.name, field_ty)
                            })
                            .collect();

                        self.ctx.types.alloc(TyKind::Struct {
                            def_id: *type_def_id,
                            fields: field_types,
                        })
                    } else if let Some(enums) = self.enums {
                        if let Some(enum_def) = enums.get(type_def_id) {
                            // Enum type — convert args to TyIds
                            let ty_args: Vec<TyId> = args
                                .iter()
                                .map(|arg_ty_id| {
                                    self.hir_type_to_ty_id_impl(
                                        *arg_ty_id,
                                        hir_types,
                                        structs,
                                        interner,
                                        depth + 1,
                                    )
                                })
                                .collect();

                            self.ctx.types.alloc(TyKind::Named {
                                name: enum_def.name,
                                def: *type_def_id,
                                args: ty_args,
                            })
                        } else {
                            // Type definition not found in structs or enums
                            self.ctx.fresh_ty_var()
                        }
                    } else {
                        // No enums context available
                        self.ctx.fresh_ty_var()
                    }
                } else {
                    // ARCHITECTURE NOTE: For generic parameters (like T), monomorphization
                    // should pass substitutions via lower_function_with_subst, not var_types

                    // Check if it's a primitive type
                    let type_name = interner.resolve(name);
                    match type_name.as_str() {
                        "i8" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I8, rv_hir::Signedness::Signed),
                        "i16" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I16, rv_hir::Signedness::Signed),
                        "i32" | "int" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I32, rv_hir::Signedness::Signed),
                        "i64" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I64, rv_hir::Signedness::Signed),
                        "i128" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I128, rv_hir::Signedness::Signed),
                        "isize" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::Isize, rv_hir::Signedness::Signed),
                        "u8" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I8, rv_hir::Signedness::Unsigned),
                        "u16" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I16, rv_hir::Signedness::Unsigned),
                        "u32" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I32, rv_hir::Signedness::Unsigned),
                        "u64" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I64, rv_hir::Signedness::Unsigned),
                        "u128" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::I128, rv_hir::Signedness::Unsigned),
                        "usize" => self
                            .ctx
                            .types
                            .int_typed(rv_hir::IntWidth::Isize, rv_hir::Signedness::Unsigned),
                        "f32" => self.ctx.types.float_typed(rv_hir::FloatWidth::F32),
                        "f64" | "float" => self.ctx.types.float_typed(rv_hir::FloatWidth::F64),
                        "char" => self.ctx.types.char(),
                        "bool" => self.ctx.types.bool(),
                        "str" | "String" => self.ctx.types.string(),
                        "()" => self.ctx.types.unit(),
                        _ => {
                            // Unknown named type, use type variable
                            self.ctx.fresh_ty_var()
                        }
                    }
                }
            }

            rv_hir::Type::Generic { name, .. } => {
                // Generic type parameters become type variables
                // Check if we have a mapping for this generic parameter (from current function)
                if let Some(&ty_var) = self.generic_param_map.get(name) {
                    // Use the mapped type variable (ensures all occurrences of T use the same variable)
                    ty_var
                } else {
                    // Not a known generic parameter, create a fresh type variable
                    self.ctx.fresh_ty_var()
                }
            }

            rv_hir::Type::Function { params, ret, .. } => {
                let param_tys: Vec<TyId> = params
                    .iter()
                    .map(|p| {
                        self.hir_type_to_ty_id_impl(*p, hir_types, structs, interner, depth + 1)
                    })
                    .collect();
                let ret_ty =
                    self.hir_type_to_ty_id_impl(**ret, hir_types, structs, interner, depth + 1);

                self.ctx.types.alloc(TyKind::Function {
                    params: param_tys,
                    ret: Box::new(ret_ty),
                })
            }

            rv_hir::Type::Tuple { elements, .. } => {
                let elem_tys: Vec<TyId> = elements
                    .iter()
                    .map(|e| {
                        self.hir_type_to_ty_id_impl(*e, hir_types, structs, interner, depth + 1)
                    })
                    .collect();

                self.ctx.types.alloc(TyKind::Tuple { elements: elem_tys })
            }

            rv_hir::Type::QualifiedPath {
                base,
                assoc_type,
                trait_ref,
                ..
            } => {
                // Resolve associated types by looking up trait impl blocks
                // Example: Self::Item where Self is a type implementing Container trait
                // Example: <T as Iterator>::Item with explicit trait_ref

                // Step 1: Extract TypeDefId from base type
                let base_hir_ty = &hir_types[**base];
                let base_type_def_id = match base_hir_ty {
                    rv_hir::Type::Named {
                        def: Some(def_id), ..
                    } => Some(*def_id),
                    _ => None,
                };

                // Step 2: Look up associated type in impl blocks
                if let (Some(def_id), Some(impl_blocks)) = (base_type_def_id, self.impl_blocks) {
                    for impl_block in impl_blocks.values() {
                        // Check if this impl is for our type
                        let impl_self_ty = &hir_types[impl_block.self_ty];
                        let matches_type = match impl_self_ty {
                            rv_hir::Type::Named {
                                def: Some(impl_def_id),
                                ..
                            } => *impl_def_id == def_id,
                            _ => false,
                        };

                        if !matches_type {
                            continue;
                        }

                        // If trait_ref is specified, only match that trait
                        let matches_trait = match (trait_ref, impl_block.trait_ref) {
                            (Some(required), Some(actual)) => *required == actual,
                            (Some(_), None) => false,
                            (None, Some(_)) => true, // No constraint — any trait impl matches
                            (None, None) => false,   // Need a trait impl for associated types
                        };

                        if matches_trait {
                            for assoc_impl in &impl_block.associated_type_impls {
                                if assoc_impl.name == *assoc_type {
                                    return self.hir_type_to_ty_id_impl(
                                        assoc_impl.ty,
                                        hir_types,
                                        structs,
                                        interner,
                                        depth + 1,
                                    );
                                }
                            }
                        }
                    }
                }

                // Associated type could not be resolved — create a type variable as fallback
                self.ctx.fresh_ty_var()
            }

            rv_hir::Type::Reference {
                inner,
                mutable,
                lifetime,
                ..
            } => {
                // Reference type - convert inner type and wrap in Ref
                let inner_ty =
                    self.hir_type_to_ty_id_impl(**inner, hir_types, structs, interner, depth + 1);
                // Use the HIR lifetime if explicitly annotated, otherwise generate a fresh one
                let lt = lifetime.unwrap_or_else(|| self.fresh_lifetime());
                self.ctx.types.alloc(TyKind::Ref {
                    inner: Box::new(inner_ty),
                    mutable: *mutable,
                    lifetime: Some(lt),
                })
            }

            rv_hir::Type::Pointer { inner, mutable, .. } => {
                let inner_ty =
                    self.hir_type_to_ty_id_impl(**inner, hir_types, structs, interner, depth + 1);
                self.ctx.types.alloc(TyKind::Pointer {
                    inner: Box::new(inner_ty),
                    mutable: *mutable,
                })
            }

            rv_hir::Type::Array { element, .. } => {
                let elem_ty =
                    self.hir_type_to_ty_id_impl(**element, hir_types, structs, interner, depth + 1);
                // Size is not yet resolved at this point (requires const eval)
                self.ctx.types.alloc(TyKind::Array {
                    element: Box::new(elem_ty),
                    size: 0,
                })
            }

            rv_hir::Type::Never { .. } => self.ctx.types.alloc(TyKind::Never),

            rv_hir::Type::DynTrait { bounds, .. } => {
                // Use the first bound's name as the principal trait
                let principal_name = bounds
                    .first()
                    .map(|b| b.name)
                    .unwrap_or_else(|| interner.intern("dyn"));
                // Resolve the trait by name
                let principal = self
                    .trait_defs
                    .and_then(|traits| {
                        traits
                            .iter()
                            .find(|(_, td)| td.name == principal_name)
                            .map(|(id, _)| *id)
                    })
                    .unwrap_or(rv_hir::TraitId(u32::MAX)); // Sentinel for unresolved
                self.ctx.types.alloc(TyKind::DynTrait {
                    principal,
                    principal_name,
                })
            }

            rv_hir::Type::ImplTrait { bounds, .. } => {
                // Use the first bound's name as the principal trait
                let principal = bounds
                    .first()
                    .map(|b| b.name)
                    .unwrap_or_else(|| interner.intern("impl"));
                self.ctx.types.alloc(TyKind::ImplTrait { principal })
            }

            rv_hir::Type::Unknown { span } => {
                panic!(
                    "ICE: Encountered Unknown type during type inference at {:?}. \
                     Parser should not produce Unknown types in well-formed code.",
                    span
                )
            }
        };

        // Update cache with the computed type
        self.type_conversion_cache.insert(hir_ty_id, result_ty);
        result_ty
    }

    /// Infer types for a function body
    fn infer_body(&mut self, body: &Body) {
        // Infer root expression with expected return type
        let expected = self.current_function_return_ty;
        self.infer_expr(body, body.root_expr, expected);
    }

    /// Infer type of an expression
    ///
    /// # Parameters
    /// - `body`: The function body containing the expression
    /// - `expr_id`: The ID of the expression to infer
    /// - `expected`: Optional expected type (for bidirectional type flow)
    #[allow(
        clippy::too_many_lines,
        reason = "Type inference requires comprehensive pattern matching"
    )]
    fn infer_expr(&mut self, body: &Body, expr_id: ExprId, expected: Option<TyId>) -> TyId {
        let expr = &body.exprs[expr_id];

        let inferred_ty = match expr {
            Expr::Literal { kind, .. } => self.infer_literal(kind),

            Expr::Variable { name, def, .. } => {
                // Prefer using resolved DefId from name resolution
                let result_ty = if let Some(def_id) = def {
                    match def_id {
                        // Special handling for function references
                        rv_hir::DefId::Function(func_id) => {
                            // Look up function signature from HIR (no inference needed!)
                            if let Some(functions) = self.functions {
                                if let Some(func) = functions.get(func_id) {
                                    // Extract signature and convert to Function type
                                    let param_tys: Vec<TyId> = func
                                        .parameters
                                        .iter()
                                        .map(|p| {
                                            if let (
                                                Some(hir_types),
                                                Some(structs),
                                                Some(interner),
                                            ) = (self.hir_types, self.structs, self.interner)
                                            {
                                                self.hir_type_to_ty_id(
                                                    p.ty, hir_types, structs, interner,
                                                )
                                            } else {
                                                self.ctx.fresh_ty_var()
                                            }
                                        })
                                        .collect();

                                    let ret_ty = if let Some(ret_hir_ty) = func.return_type {
                                        if let (Some(hir_types), Some(structs), Some(interner)) =
                                            (self.hir_types, self.structs, self.interner)
                                        {
                                            self.hir_type_to_ty_id(
                                                ret_hir_ty, hir_types, structs, interner,
                                            )
                                        } else {
                                            self.ctx.types.unit()
                                        }
                                    } else {
                                        self.ctx.types.unit()
                                    };

                                    // Create Function type
                                    self.ctx.types.alloc(TyKind::Function {
                                        params: param_tys,
                                        ret: Box::new(ret_ty),
                                    })
                                } else {
                                    self.ctx.fresh_ty_var()
                                }
                            } else {
                                self.ctx.fresh_ty_var()
                            }
                        }
                        // Other DefIds: look up from context or name-based lookup
                        _ => {
                            if let Some(def_ty) = self.ctx.get_def_type(*def_id) {
                                def_ty
                            } else {
                                // DefId not yet typed, try name-based lookup (for parameters)
                                if let Some(var_ty) = self.lookup_var(*name) {
                                    var_ty
                                } else {
                                    // Unknown definition, create fresh variable
                                    self.ctx.fresh_ty_var()
                                }
                            }
                        }
                    }
                } else {
                    // Unresolved variable - name resolution should have caught this
                    // This can happen with core library trait implementations where self
                    // isn't properly resolved. Create a fresh type variable to allow
                    // compilation to continue.
                    self.ctx.fresh_ty_var()
                };

                // ARCHITECTURE: Unify variable type with expected type
                // This enables bidirectional type flow, e.g., for:
                //   let n = Option::None;  // n has type Option<T> where T is a type variable
                //   f(n, 99);              // f expects Option<i64>, so unify to resolve T = i64
                if let Some(expected_ty) = expected {
                    if self.generate_mode {
                        let source = ConstraintSource::new(
                            rv_span::FileId(0),
                            rv_span::Span::new(0, 0),
                            "variable expected type".to_string(),
                        );
                        self.constraints.add_equality(result_ty, expected_ty, source);
                    } else if let Err(_error) = Unifier::new(&mut self.ctx).unify(result_ty, expected_ty) {
                        // Don't report error here - the mismatch will be caught at the call site
                    }
                }

                result_ty
            }

            Expr::Call { callee, args, type_args: _, span } => {
                // Check if calling an unsafe function from a safe context
                if self.unsafe_depth == 0 {
                    if let Some(func_id) = self.resolve_callee_function(body, *callee) {
                        if let Some(functions) = self.functions {
                            if let Some(func) = functions.get(&func_id) {
                                if func.is_unsafe {
                                    self.errors
                                        .push(TypeError::UnsafeCallInSafeContext { span: *span });
                                }
                            }
                        }
                    }
                }

                // Infer callee type (no expected type for callee)
                let callee_ty = self.infer_expr(body, *callee, None);

                // Extract parameter types from callee to pass as expected types to arguments
                let callee_ty_normalized = self.ctx.types.get(callee_ty);
                let param_expected_types =
                    if let TyKind::Function { params, .. } = &callee_ty_normalized.kind {
                        params.clone()
                    } else {
                        vec![]
                    };

                // Infer argument types with expected types from function signature
                let arg_tys: Vec<_> = args
                    .iter()
                    .enumerate()
                    .map(|(idx, arg)| {
                        let expected_arg_ty = param_expected_types.get(idx).copied();
                        self.infer_expr(body, *arg, expected_arg_ty)
                    })
                    .collect();

                // Create fresh type variable for return type
                let ret_ty = self.ctx.fresh_ty_var();

                // Unify callee with function type
                let func_ty = self.ctx.types.alloc(TyKind::Function {
                    params: arg_tys,
                    ret: Box::new(ret_ty),
                });

                if self.generate_mode {
                    // Generate constraint instead of immediate unification
                    let source = ConstraintSource::new(
                        rv_span::FileId(0),
                        rv_span::Span::new(0, 0),
                        "function call".to_string(),
                    );
                    self.constraints.add_equality(callee_ty, func_ty, source);
                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(callee_ty, func_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(expr_id),
                    });
                }

                ret_ty
            }

            Expr::BinaryOp {
                op,
                left,
                right,
                span,
            } => {
                // Infer left operand first (no expected type)
                let left_ty = self.infer_expr(body, *left, None);

                // Right operand should match left operand type
                let right_ty = self.infer_expr(body, *right, Some(left_ty));

                // Unify both operands to ensure they have the same type
                if self.generate_mode {
                    let source =
                        ConstraintSource::binary_op(span.file, span.span, &format!("{op:?}"));
                    self.constraints.add_equality(left_ty, right_ty, source);
                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(left_ty, right_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(expr_id),
                    });
                }

                // Comparison and logical operators return Bool, others return operand type
                match op {
                    rv_hir::BinaryOp::Eq
                    | rv_hir::BinaryOp::Ne
                    | rv_hir::BinaryOp::Lt
                    | rv_hir::BinaryOp::Le
                    | rv_hir::BinaryOp::Gt
                    | rv_hir::BinaryOp::Ge
                    | rv_hir::BinaryOp::And
                    | rv_hir::BinaryOp::Or => self.ctx.types.bool(),
                    _ => left_ty,
                }
            }

            Expr::UnaryOp { op, operand, .. } => {
                use rv_hir::UnaryOp;
                match op {
                    UnaryOp::Ref | UnaryOp::RefMut => {
                        // Reference operations: &x or &mut x
                        // Infer the operand type first
                        let operand_ty = self.infer_expr(body, *operand, None);
                        // Generate a fresh lifetime for this borrow
                        let lifetime = self.fresh_lifetime();
                        // Create a reference type wrapping the operand type
                        let ref_ty = self.ctx.types.alloc(TyKind::Ref {
                            inner: Box::new(operand_ty),
                            mutable: matches!(op, UnaryOp::RefMut),
                            lifetime: Some(lifetime),
                        });
                        self.ctx.set_expr_type(expr_id, ref_ty);
                        ref_ty
                    }
                    UnaryOp::Deref => {
                        // Dereference: *ptr or *ref
                        let operand_ty = self.infer_expr(body, *operand, None);
                        let resolved = self.ctx.follow_var(operand_ty);
                        let kind = self.ctx.types.get(resolved).kind.clone();
                        match kind {
                            TyKind::Pointer { inner, .. } => {
                                // Raw pointer dereference requires unsafe context
                                if self.unsafe_depth == 0 {
                                    eprintln!(
                                        "error: dereference of raw pointer requires unsafe block"
                                    );
                                }
                                let result = *inner;
                                self.ctx.set_expr_type(expr_id, result);
                                result
                            }
                            TyKind::Ref { inner, .. } => {
                                // Reference dereference is always safe
                                let result = *inner;
                                self.ctx.set_expr_type(expr_id, result);
                                result
                            }
                            _ => {
                                // Unknown type — return fresh var
                                self.ctx.fresh_ty_var()
                            }
                        }
                    }
                    _ => {
                        // Other unary ops (Neg, Not, BitNot) return same type as operand
                        self.infer_expr(body, *operand, expected)
                    }
                }
            }

            Expr::Block {
                statements, expr, ..
            } => {
                // Push a new scope for the block
                self.push_scope();

                // Infer statement types
                for stmt_id in statements {
                    self.infer_stmt(body, *stmt_id);
                }

                // Block type is trailing expression type or unit
                // Pass expected type down to trailing expression
                let block_ty = if let Some(trailing) = expr {
                    self.infer_expr(body, *trailing, expected)
                } else {
                    self.ctx.types.unit()
                };

                // Pop the block scope
                self.pop_scope();

                block_ty
            }

            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                // Condition must be bool (no expected type for condition)
                let cond_ty = self.infer_expr(body, *condition, None);
                let bool_ty = self.ctx.types.bool();

                if self.generate_mode {
                    let source = ConstraintSource::new(
                        rv_span::FileId(0),
                        rv_span::Span::new(0, 0),
                        "if condition".to_string(),
                    );
                    self.constraints.add_equality(cond_ty, bool_ty, source);
                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(cond_ty, bool_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(*condition),
                    });
                }

                // Both branches should have the expected type
                let then_ty = self.infer_expr(body, *then_branch, expected);

                if let Some(else_expr) = else_branch {
                    let else_ty = self.infer_expr(body, *else_expr, expected);

                    if self.generate_mode {
                        let source = ConstraintSource::new(
                            rv_span::FileId(0),
                            rv_span::Span::new(0, 0),
                            "if branches".to_string(),
                        );
                        self.constraints.add_equality(then_ty, else_ty, source);
                    } else if let Err(error) = Unifier::new(&mut self.ctx).unify(then_ty, else_ty) {
                        self.errors.push(TypeError::Unification {
                            error,
                            expr: Some(expr_id),
                        });
                    }

                    then_ty
                } else {
                    // No else branch, result is unit
                    self.ctx.types.unit()
                }
            }

            Expr::Match {
                scrutinee, arms, ..
            } => {
                // Infer scrutinee type — used to type-check patterns against
                let scrutinee_ty = self.infer_expr(body, *scrutinee, None);

                // Type-check patterns: unify literal patterns with the scrutinee type
                // so that e.g. matching an i64 against bool literals is caught.
                for arm in arms {
                    let pat = &body.patterns[arm.pattern];
                    if let rv_hir::Pattern::Literal { kind, .. } = pat {
                        let pat_ty = self.infer_literal(kind);
                        if self.generate_mode {
                            let source = ConstraintSource::new(
                                rv_span::FileId(0),
                                rv_span::Span::new(0, 0),
                                "match pattern vs scrutinee".to_string(),
                            );
                            self.constraints.add_equality(scrutinee_ty, pat_ty, source);
                        } else if let Err(error) =
                            Unifier::new(&mut self.ctx).unify(scrutinee_ty, pat_ty)
                        {
                            self.errors.push(TypeError::Unification {
                                error,
                                expr: Some(*scrutinee),
                            });
                        }
                    }
                }

                // All arms should produce the expected type
                // Use expected type as the initial result type if provided
                let mut result_ty = expected;

                #[allow(
                    clippy::excessive_nesting,
                    reason = "Match arm unification requires nested checks"
                )]
                for arm in arms {
                    // Register pattern bindings with inferred types before inferring arm body
                    let pat = &body.patterns[arm.pattern];
                    self.infer_pattern_bindings(body, pat, scrutinee_ty);

                    // Pass expected type down to each arm body
                    let arm_ty = self.infer_expr(body, arm.body, expected);

                    result_ty = if let Some(expected_arm_ty) = result_ty {
                        if self.generate_mode {
                            let source = ConstraintSource::new(
                                rv_span::FileId(0),
                                rv_span::Span::new(0, 0),
                                "match arms".to_string(),
                            );
                            self.constraints
                                .add_equality(expected_arm_ty, arm_ty, source);
                        } else if let Err(error) =
                            Unifier::new(&mut self.ctx).unify(expected_arm_ty, arm_ty)
                        {
                            self.errors.push(TypeError::Unification {
                                error,
                                expr: Some(arm.body),
                            });
                        }
                        Some(expected_arm_ty)
                    } else {
                        Some(arm_ty)
                    };
                }

                result_ty.unwrap_or_else(|| {
                    panic!(
                        "ICE: Match expression has no arms and no expected type. \
                         Parser should ensure match expressions have at least one arm, \
                         or type checker should handle uninhabited types explicitly."
                    )
                })
            }

            Expr::Field { base, field, .. } => {
                // Infer base type (no expected type for base)
                let base_ty = self.infer_expr(body, *base, None);

                // Follow type variable substitutions to resolve the concrete type.
                // After unification, base_ty may be a type variable that was unified
                // with a Struct type — we must follow the chain to find it.
                let resolved_base_ty = self.ctx.follow_var(base_ty);

                // Look up the field type from the struct DEFINITION, not the inferred type
                // This ensures we get concrete types, not type variables from struct construction
                let base_ty_kind = &self.ctx.types.get(resolved_base_ty).kind;
                match base_ty_kind {
                    TyKind::Struct { def_id, .. } => {
                        // Look up the struct definition to get field types
                        if let Some(structs) = self.structs {
                            if let Some(struct_def) = structs.get(def_id) {
                                // Find the field in the struct definition
                                if let Some(field_def) =
                                    struct_def.fields.iter().find(|f| f.name == *field)
                                {
                                    // Convert HIR TypeId to TyId
                                    if let (Some(hir_types), Some(interner)) =
                                        (self.hir_types, self.interner)
                                    {
                                        self.hir_type_to_ty_id(
                                            field_def.ty,
                                            hir_types,
                                            structs,
                                            interner,
                                        )
                                    } else {
                                        self.ctx.fresh_ty_var()
                                    }
                                } else {
                                    // Field not found in struct definition
                                    self.ctx.fresh_ty_var()
                                }
                            } else {
                                // Struct definition not found
                                self.ctx.fresh_ty_var()
                            }
                        } else {
                            // No struct context available
                            self.ctx.fresh_ty_var()
                        }
                    }
                    _ => {
                        // Not a struct type, return type variable
                        self.ctx.fresh_ty_var()
                    }
                }
            }

            Expr::MethodCall {
                receiver,
                method,
                args,
                ..
            } => {
                // Infer receiver type (no expected type for receiver)
                let receiver_ty = self.infer_expr(body, *receiver, None);

                // Check receiver mutability and store it for MIR lowering
                let receiver_is_mutable = self.is_expr_mutable(body, *receiver);
                self.receiver_mutability
                    .insert(expr_id, receiver_is_mutable);

                // Follow type variable substitutions to resolve the concrete receiver type
                let resolved_receiver_ty = self.ctx.follow_var(receiver_ty);

                // Extract receiver TypeDefId for method lookup
                // Handles both structs (TyKind::Struct) and enums (TyKind::Named)
                let receiver_ty_kind = &self.ctx.types.get(resolved_receiver_ty).kind;
                let type_def_id = match receiver_ty_kind {
                    TyKind::Struct { def_id, .. } => Some(*def_id),
                    TyKind::Named { def, .. } => Some(*def),
                    _ => None,
                };

                // Try to find the method from impl blocks
                let method_func =
                    if let (Some(impl_blocks), Some(functions), Some(hir_types), Some(def_id)) = (
                        self.impl_blocks,
                        self.functions,
                        self.hir_types,
                        type_def_id,
                    ) {
                        let mut found_func = None;
                        // Find impl blocks for this type
                        'outer: for impl_block in impl_blocks.values() {
                            // Check if this impl block is for the receiver type
                            let impl_self_ty = &hir_types[impl_block.self_ty];
                            if let rv_hir::Type::Named {
                                def: Some(impl_def_id),
                                ..
                            } = impl_self_ty
                            {
                                if *impl_def_id == def_id {
                                    // Search methods in this impl block
                                    for &func_id in &impl_block.methods {
                                        if let Some(func) = functions.get(&func_id) {
                                            if func.name == *method {
                                                found_func = Some(func);
                                                break 'outer;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        found_func
                    } else {
                        None
                    };

                // If we found the method, type-check arguments and get return type
                if let Some(method_func) = method_func {
                    // Type-check arguments against method parameters (skip first param which is self)
                    let method_params: Vec<TyId> = method_func
                        .parameters
                        .iter()
                        .skip(1) // Skip self parameter
                        .map(|p| {
                            if let (Some(hir_types), Some(structs), Some(interner)) =
                                (self.hir_types, self.structs, self.interner)
                            {
                                self.hir_type_to_ty_id(p.ty, hir_types, structs, interner)
                            } else {
                                self.ctx.fresh_ty_var()
                            }
                        })
                        .collect();

                    // Infer argument types with expected types from method signature
                    for (idx, arg) in args.iter().enumerate() {
                        let expected_arg_ty = method_params.get(idx).copied();
                        let arg_ty = self.infer_expr(body, *arg, expected_arg_ty);

                        // Unify with expected type if available
                        if let Some(expected_ty) = expected_arg_ty {
                            if self.generate_mode {
                                let source = ConstraintSource::new(
                                    rv_span::FileId(0),
                                    rv_span::Span::new(0, 0),
                                    format!("method argument {}", idx),
                                );
                                self.constraints.add_equality(arg_ty, expected_ty, source);
                            } else if let Err(error) =
                                Unifier::new(&mut self.ctx).unify(arg_ty, expected_ty)
                            {
                                self.errors.push(TypeError::Unification {
                                    error,
                                    expr: Some(*arg),
                                });
                            }
                        }
                    }

                    // Get return type
                    if let Some(return_type_id) = method_func.return_type {
                        if let (Some(hir_types), Some(structs), Some(interner)) =
                            (self.hir_types, self.structs, self.interner)
                        {
                            self.hir_type_to_ty_id(return_type_id, hir_types, structs, interner)
                        } else {
                            self.ctx.types.unit()
                        }
                    } else {
                        self.ctx.types.unit()
                    }
                } else {
                    // Method not found - infer arguments anyway and return type variable
                    for arg in args {
                        self.infer_expr(body, *arg, None);
                    }
                    self.ctx.fresh_ty_var()
                }
            }

            Expr::StructConstruct { def, fields, .. } => {
                // Create struct type if we have a type definition
                let result_ty = if let Some(type_def_id) = def {
                    // Look up the struct definition to get declared field types
                    if let Some(structs) = self.structs {
                        if let Some(struct_def) = structs.get(type_def_id) {
                            // Build field types from the struct definition
                            let mut field_tys: Vec<(rv_intern::Symbol, TyId)> = Vec::new();

                            for (field_name, field_expr) in fields {
                                // Look up the declared field type in the struct definition
                                let declared_ty = if let Some(field_def) =
                                    struct_def.fields.iter().find(|f| f.name == *field_name)
                                {
                                    // Convert HIR TypeId to inference TyId
                                    if let (Some(hir_types), Some(interner)) =
                                        (self.hir_types, self.interner)
                                    {
                                        self.hir_type_to_ty_id(
                                            field_def.ty,
                                            hir_types,
                                            structs,
                                            interner,
                                        )
                                    } else {
                                        self.ctx.fresh_ty_var()
                                    }
                                } else {
                                    self.ctx.fresh_ty_var()
                                };

                                // Infer the expression type with expected type from field declaration
                                let expr_ty = self.infer_expr(body, *field_expr, Some(declared_ty));

                                // Unify expression type with declared type
                                if self.generate_mode {
                                    let source = ConstraintSource::new(
                                        rv_span::FileId(0),
                                        rv_span::Span::new(0, 0),
                                        format!("struct field '{field_name:?}'"),
                                    );
                                    self.constraints.add_equality(expr_ty, declared_ty, source);
                                } else if let Err(error) =
                                    Unifier::new(&mut self.ctx).unify(expr_ty, declared_ty)
                                {
                                    self.errors.push(TypeError::Unification {
                                        error,
                                        expr: Some(*field_expr),
                                    });
                                }

                                // After unification, follow the substitution chain to get the most resolved type
                                // Prefer expr_ty since it comes from actual expression inference
                                let field_ty = self.ctx.follow_var(expr_ty);
                                field_tys.push((*field_name, field_ty));
                            }

                            self.ctx.types.alloc(TyKind::Struct {
                                def_id: *type_def_id,
                                fields: field_tys,
                            })
                        } else {
                            panic!(
                                "ICE: Struct type {:?} has no definition in structs map. \
                                 Name resolution should have linked all struct types to their definitions.",
                                type_def_id
                            )
                        }
                    } else {
                        panic!(
                            "ICE: Struct construct has type_def_id {:?} but structs context is None. \
                             Type inference should be provided with struct definitions.",
                            type_def_id
                        )
                    }
                } else {
                    // No type definition resolved, create type variable
                    self.ctx.fresh_ty_var()
                };
                result_ty
            }

            Expr::EnumVariant {
                variant,
                def,
                fields,
                ..
            } => {
                // Infer variant field types
                let field_tys: Vec<TyId> = fields
                    .iter()
                    .map(|field_expr| self.infer_expr(body, *field_expr, None))
                    .collect();

                // Return a Named type referencing the enum if we have the type definition
                // Enums are nominal types, so we use Named with the TypeDefId
                let type_def_id = def.unwrap_or_else(|| {
                    let variant_name = self.interner
                        .map(|i| i.resolve(variant))
                        .unwrap_or_else(|| "?".to_string());
                    panic!(
                        "ICE: Enum variant construct '{}' has no type definition. \
                         Name resolution should have linked all enum variants to their type definitions.",
                        variant_name
                    )
                });

                let enums = self.enums.unwrap_or_else(|| {
                    panic!(
                        "ICE: Type inference called without enums context. \
                         All compilation contexts should provide enum definitions."
                    )
                });

                let enum_def = enums.get(&type_def_id).unwrap_or_else(|| {
                    panic!(
                        "ICE: Enum type {:?} has no definition in enums map. \
                         Name resolution should have linked all enum types to their definitions.",
                        type_def_id
                    )
                });

                // Build generic type args by matching field types against variant definition
                // For Option::Some(42), we match the inferred type of 42 (i64) against T
                // to get args = [i64]
                //
                // For unit variants like Option::None, we try to use the expected type's args
                // (from type annotation) since there are no fields to infer from.
                let expected_args: Option<Vec<TyId>> = expected.and_then(|exp_ty| {
                    let resolved = self.ctx.follow_var(exp_ty);
                    let ty = self.ctx.types.get(resolved);
                    if let TyKind::Named { args, def, .. } = &ty.kind {
                        // Only use if the expected type is the same enum
                        if *def == type_def_id {
                            Some(args.clone())
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                });

                let args = if enum_def.generic_params.is_empty() {
                    // No generic params, no args needed
                    vec![]
                } else {
                    // Find the variant definition
                    let variant_def = enum_def.variants.iter()
                        .find(|v| v.name == *variant);

                    if let Some(variant_def) = variant_def {
                        // Create type args by matching variant field types to inferred types
                        // For each generic param, find the corresponding inferred type
                        let mut args = vec![];
                        for (param_idx, param) in enum_def.generic_params.iter().enumerate() {
                            // Look for this generic param in variant field types
                            // and use the corresponding inferred type
                            let inferred_ty = match &variant_def.fields {
                                rv_hir::VariantFields::Unit => {
                                    // Unit variant has no fields to infer from
                                    // Use expected type's args if available, otherwise create type variable
                                    expected_args.as_ref()
                                        .and_then(|args| args.get(param_idx).copied())
                                        .unwrap_or_else(|| self.ctx.fresh_ty_var())
                                }
                                rv_hir::VariantFields::Tuple(field_type_ids) => {
                                    // Find which field position corresponds to this generic param
                                    let mut found_ty = None;
                                    if let Some(hir_types) = self.hir_types {
                                        for (idx, field_ty_id) in field_type_ids.iter().enumerate() {
                                            let field_ty = &hir_types[*field_ty_id];
                                            if let rv_hir::Type::Generic { name, .. } = field_ty {
                                                if *name == param.name && idx < field_tys.len() {
                                                    found_ty = Some(field_tys[idx]);
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                    // If not found in fields, try expected type's args (for params
                                    // not used in this variant, e.g., E in Result::Ok(T))
                                    found_ty
                                        .or_else(|| expected_args.as_ref().and_then(|args| args.get(param_idx).copied()))
                                        .unwrap_or_else(|| self.ctx.fresh_ty_var())
                                }
                                rv_hir::VariantFields::Struct(field_defs) => {
                                    // Find which field corresponds to this generic param
                                    let mut found_ty = None;
                                    if let Some(hir_types) = self.hir_types {
                                        for (idx, field_def) in field_defs.iter().enumerate() {
                                            let field_ty = &hir_types[field_def.ty];
                                            if let rv_hir::Type::Generic { name, .. } = field_ty {
                                                if *name == param.name && idx < field_tys.len() {
                                                    found_ty = Some(field_tys[idx]);
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                    // If not found in fields, try expected type's args (for params
                                    // not used in this variant, e.g., E in Result::Ok(T))
                                    found_ty
                                        .or_else(|| expected_args.as_ref().and_then(|args| args.get(param_idx).copied()))
                                        .unwrap_or_else(|| self.ctx.fresh_ty_var())
                                }
                            };
                            args.push(inferred_ty);
                        }
                        args
                    } else {
                        // Variant not found, use type variables for all params
                        enum_def.generic_params.iter()
                            .map(|_| self.ctx.fresh_ty_var())
                            .collect()
                    }
                };

                self.ctx.types.alloc(TyKind::Named {
                    name: enum_def.name,
                    def: type_def_id,
                    args,
                })
            }

            Expr::Closure {
                params,
                return_type,
                body: closure_body,
                captures,
                ..
            } => {
                // Push a new scope for the closure
                self.push_scope();

                // Infer parameter types - use annotations if available, otherwise create type variables
                let mut param_tys = vec![];
                for param in params {
                    let param_ty = if let (Some(hir_types), Some(structs), Some(interner)) =
                        (self.hir_types, self.structs, self.interner)
                    {
                        // Use annotated type if available
                        self.hir_type_to_ty_id(param.ty, hir_types, structs, interner)
                    } else {
                        // Create a fresh type variable for parameter
                        self.ctx.fresh_ty_var()
                    };

                    // Register parameter in current scope
                    self.insert_var(param.name, param_ty);
                    param_tys.push(param_ty);
                }

                // Add captured variables to closure scope with their types from parent scope
                for capture in captures {
                    if let Some(capture_ty) = self.lookup_var(*capture) {
                        self.insert_var(*capture, capture_ty);
                    }
                }

                // Infer closure body with expected return type if annotated
                let expected_return_ty = return_type.and_then(|rt_id| {
                    if let (Some(hir_types), Some(structs), Some(interner)) =
                        (self.hir_types, self.structs, self.interner)
                    {
                        Some(self.hir_type_to_ty_id(rt_id, hir_types, structs, interner))
                    } else {
                        None
                    }
                });

                let body_ty = self.infer_expr(body, *closure_body, expected_return_ty);

                // Unify with expected return type if provided
                if let Some(expected_ret_ty) = expected_return_ty {
                    if self.generate_mode {
                        let source = ConstraintSource::return_type(
                            rv_span::FileId(0),
                            rv_span::Span::new(0, 0),
                        );
                        self.constraints
                            .add_equality(body_ty, expected_ret_ty, source);
                    } else if let Err(error) =
                        Unifier::new(&mut self.ctx).unify(body_ty, expected_ret_ty)
                    {
                        self.errors.push(TypeError::Unification {
                            error,
                            expr: Some(*closure_body),
                        });
                    }
                }

                // Pop the closure scope
                self.pop_scope();

                // Create function type for the closure
                self.ctx.types.alloc(TyKind::Function {
                    params: param_tys,
                    ret: Box::new(body_ty),
                })
            }

            Expr::PathCall { args, .. } => {
                // Cross-module function call: infer argument types but return type is unknown
                for arg in args {
                    self.infer_expr(body, *arg, None);
                }
                // Return type is unknown for cross-module calls, use type variable
                self.ctx.fresh_ty_var()
            }

            Expr::Assign { target, value, .. } => {
                // Infer target and value types
                self.infer_expr(body, *target, None);
                self.infer_expr(body, *value, None);
                // Assignment expressions evaluate to unit
                self.ctx.types.unit()
            }

            Expr::CompoundAssign {
                target, op, value, ..
            } => {
                // Infer target type
                let target_ty = self.infer_expr(body, *target, None);
                // Value should match target type
                let value_ty = self.infer_expr(body, *value, Some(target_ty));
                // Unify target and value types
                if self.generate_mode {
                    let source = ConstraintSource::new(
                        rv_span::FileId(0),
                        rv_span::Span::new(0, 0),
                        format!("compound assignment {:?}", op),
                    );
                    self.constraints.add_equality(target_ty, value_ty, source);
                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(target_ty, value_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(expr_id),
                    });
                }
                // Compound assignment evaluates to unit
                self.ctx.types.unit()
            }

            Expr::WhileLoop {
                condition,
                body: loop_body,
                ..
            } => {
                // Condition must be bool
                let cond_ty = self.infer_expr(body, *condition, None);
                let bool_ty = self.ctx.types.bool();
                if self.generate_mode {
                    let source = ConstraintSource::new(
                        rv_span::FileId(0),
                        rv_span::Span::new(0, 0),
                        "while condition".to_string(),
                    );
                    self.constraints.add_equality(cond_ty, bool_ty, source);
                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(cond_ty, bool_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(*condition),
                    });
                }
                // Infer body type
                self.infer_expr(body, *loop_body, None);
                // While loops evaluate to unit
                self.ctx.types.unit()
            }

            Expr::Loop {
                body: loop_body, ..
            } => {
                self.infer_expr(body, *loop_body, None);
                // Infinite loops without break evaluate to Never, loops with break evaluate
                // to the break value type. Currently returns Unit which is correct for
                // statement-position loops. Full break-value propagation requires a loop
                // result type variable that break expressions unify against.
                self.ctx.types.unit()
            }

            Expr::Break { value, .. } => {
                if let Some(val) = value {
                    self.infer_expr(body, *val, None);
                }
                self.ctx.types.never()
            }

            Expr::Continue { .. } => self.ctx.types.never(),

            Expr::Array { elements, span } => {
                let elem_ty = if let Some(first) = elements.first() {
                    let first_ty = self.infer_expr(body, *first, None);
                    for elem in elements.iter().skip(1) {
                        let ty = self.infer_expr(body, *elem, Some(first_ty));
                        if self.generate_mode {
                            let source = ConstraintSource::new(
                                span.file,
                                span.span,
                                "array element".to_string(),
                            );
                            self.constraints.add_equality(first_ty, ty, source);
                        } else if let Err(error) = Unifier::new(&mut self.ctx).unify(first_ty, ty) {
                            self.errors.push(TypeError::Unification {
                                error,
                                expr: Some(*elem),
                            });
                        }
                    }
                    first_ty
                } else {
                    self.ctx.fresh_ty_var()
                };
                let size = elements.len();
                self.ctx.types.alloc(TyKind::Array {
                    element: Box::new(elem_ty),
                    size,
                })
            }

            Expr::Tuple { elements, .. } => {
                let elem_tys: Vec<_> = elements
                    .iter()
                    .map(|elem| self.infer_expr(body, *elem, None))
                    .collect();
                self.ctx.types.alloc(TyKind::Tuple { elements: elem_tys })
            }

            Expr::Index { base, index, span } => {
                let base_ty = self.infer_expr(body, *base, None);
                let index_ty = self.infer_expr(body, *index, None);
                let int_ty = self.ctx.types.int();
                if self.generate_mode {
                    let source =
                        ConstraintSource::new(span.file, span.span, "array index".to_string());
                    self.constraints.add_equality(index_ty, int_ty, source);
                } else if let Err(error) = Unifier::new(&mut self.ctx).unify(index_ty, int_ty) {
                    self.errors.push(TypeError::Unification {
                        error,
                        expr: Some(*index),
                    });
                }
                // Extract element type from base if it resolves to an array
                let resolved_base = self.ctx.follow_var(base_ty);
                match &self.ctx.types.get(resolved_base).kind.clone() {
                    TyKind::Array { element, .. } => **element,
                    _ => self.ctx.fresh_ty_var(),
                }
            }

            Expr::Cast {
                expr: cast_expr,
                ty,
                ..
            } => {
                // Infer expression type
                self.infer_expr(body, *cast_expr, None);
                // Return the target type if we can resolve it, otherwise fresh var
                if let (Some(hir_types), Some(structs), Some(interner)) =
                    (self.hir_types, self.structs, self.interner)
                {
                    self.hir_type_to_ty_id(*ty, hir_types, structs, interner)
                } else {
                    self.ctx.fresh_ty_var()
                }
            }
            Expr::UnsafeBlock { body: inner, .. } => {
                self.unsafe_depth += 1;
                let ty = self.infer_expr(body, *inner, expected);
                self.unsafe_depth -= 1;
                ty
            }
            Expr::Error { .. } => {
                // Error expression — return a fresh type variable so
                // inference can continue and report additional errors.
                self.ctx.fresh_ty_var()
            }

            Expr::WhileLet { pattern: _, value, body: loop_body, .. } => {
                // while let pattern = value { body }
                self.infer_expr(body, *value, None);
                self.infer_expr(body, *loop_body, None);
                self.ctx.types.unit()
            }

            Expr::IfLet { pattern: _, value, then_branch, else_branch, .. } => {
                // if let pattern = value { then } else { else }
                self.infer_expr(body, *value, None);
                let then_ty = self.infer_expr(body, *then_branch, expected);
                if let Some(else_expr) = else_branch {
                    let else_ty = self.infer_expr(body, *else_expr, expected);
                    // Unify branches
                    let mut unifier = Unifier::new(&mut self.ctx);
                    let _ = unifier.unify(then_ty, else_ty);
                    then_ty
                } else {
                    self.ctx.types.unit()
                }
            }

            Expr::Range { start, end, .. } => {
                // Range expressions: 1..10, 1..=10, ..10, 1.., ..
                // Infer types of start and end if present
                if let Some(s) = start {
                    self.infer_expr(body, *s, None);
                }
                if let Some(e) = end {
                    self.infer_expr(body, *e, None);
                }
                // Range type would be std::ops::Range<T> etc.
                // For now, return a fresh type variable
                self.ctx.fresh_ty_var()
            }

            Expr::Try { expr: inner, .. } => {
                // Try operator: expr?
                // The inner expression should be Result<T, E> or Option<T>
                // The overall type is T (unwrapped success type)
                self.infer_expr(body, *inner, None);
                // Return fresh type variable for the unwrapped type
                self.ctx.fresh_ty_var()
            }

            Expr::ForLoop { iterator, body: loop_body, .. } => {
                // for pattern in iterator { body }
                // Infer iterator type
                self.infer_expr(body, *iterator, None);
                // Infer body type (result is unit)
                self.infer_expr(body, *loop_body, None);
                self.ctx.types.unit()
            }

            Expr::Box { value, .. } => {
                // Box::new(value) - infer type of inner value, return Box<T>
                let inner_ty = self.infer_expr(body, *value, None);
                self.ctx.types.boxed(inner_ty)
            }
        };

        // Bidirectional unification: unify inferred type with expected type
        if let Some(expected_ty) = expected {
            if self.generate_mode {
                let source = ConstraintSource::new(
                    rv_span::FileId(0),
                    rv_span::Span::new(0, 0),
                    "expected type".to_string(),
                );
                self.constraints
                    .add_equality(inferred_ty, expected_ty, source);
            } else if let Err(error) = Unifier::new(&mut self.ctx).unify(inferred_ty, expected_ty) {
                self.errors.push(TypeError::Unification {
                    error,
                    expr: Some(expr_id),
                });
            }
        }

        // Record expression type
        self.ctx.set_expr_type(expr_id, inferred_ty);

        inferred_ty
    }

    /// Infer type of a literal
    fn infer_literal(&mut self, kind: &LiteralKind) -> TyId {
        match kind {
            LiteralKind::Integer(_, Some((w, s))) => self.ctx.types.int_typed(*w, *s),
            // Unsuffixed integer literal: create an inference variable that can unify
            // with any integer type. Defaults to i32 when unconstrained (Rust semantics).
            LiteralKind::Integer(_, None) => self.ctx.fresh_int_var(),
            LiteralKind::Float(_, Some(w)) => self.ctx.types.float_typed(*w),
            // Unsuffixed float literal: create an inference variable that can unify
            // with any float type. Defaults to f64 when unconstrained (Rust semantics).
            LiteralKind::Float(_, None) => self.ctx.fresh_float_var(),
            LiteralKind::Char(_) => self.ctx.types.char(),
            LiteralKind::String(_) => self.ctx.types.string(),
            LiteralKind::Bool(_) => self.ctx.types.bool(),
            LiteralKind::Unit => self.ctx.types.unit(),
        }
    }

    /// Infer statement
    fn infer_stmt(&mut self, body: &Body, stmt_id: StmtId) {
        let stmt = &body.stmts[stmt_id];

        match stmt {
            Stmt::Let {
                pattern,
                ty,
                initializer,
                mutable,
                ..
            } => {
                if let Some(init_expr) = initializer {
                    // If there's a type annotation, use it as expected type
                    let expected_ty = ty.and_then(|type_id| {
                        if let (Some(hir_types), Some(structs), Some(interner)) =
                            (self.hir_types, self.structs, self.interner)
                        {
                            Some(self.hir_type_to_ty_id(type_id, hir_types, structs, interner))
                        } else {
                            None
                        }
                    });

                    // Infer initializer with expected type from annotation
                    let init_ty = self.infer_expr(body, *init_expr, expected_ty);

                    // Generate lifetime outlives constraint for reference assignments:
                    // If `let x: &'a T = &'b expr`, then 'b must outlive 'a
                    if let (Some(expected), Some(init_lt)) =
                        (expected_ty, self.ref_lifetime(init_ty))
                    {
                        if let Some(expected_lt) = self.ref_lifetime(expected) {
                            self.add_lifetime_outlives(init_lt, expected_lt, Some(*init_expr));
                        }
                    }

                    // Record the type for the variable name in the current scope
                    let pat = &body.patterns[*pattern];
                    if let rv_hir::Pattern::Binding {
                        name,
                        mutable: pat_mutable,
                        ..
                    } = pat
                    {
                        self.insert_var(*name, init_ty);
                        // Track variable mutability (from either let mut or pattern)
                        let is_mutable = *mutable || *pat_mutable;
                        self.insert_var_mutability(*name, is_mutable);
                    }
                }
            }

            Stmt::Expr { expr, .. } => {
                // Expression statements don't have expected types
                self.infer_expr(body, *expr, None);
            }

            Stmt::Return { value, .. } => {
                if let Some(val_expr) = value {
                    // Use function return type as expected type
                    let val_ty = self.infer_expr(body, *val_expr, self.current_function_return_ty);

                    // Generate lifetime outlives constraint for returned references:
                    // If returning &'a T where function returns &'b T, then 'a must outlive 'b
                    if let Some(val_lt) = self.ref_lifetime(val_ty) {
                        if let Some(expected_return_ty) = self.current_function_return_ty {
                            if let Some(ret_lt) = self.ref_lifetime(expected_return_ty) {
                                self.add_lifetime_outlives(val_lt, ret_lt, Some(*val_expr));
                            }
                        }
                    }

                    // Unify with expected function return type
                    if let Some(expected_return_ty) = self.current_function_return_ty {
                        if self.generate_mode {
                            let source = ConstraintSource::return_type(
                                rv_span::FileId(0),
                                rv_span::Span::new(0, 0),
                            );
                            self.constraints
                                .add_equality(val_ty, expected_return_ty, source);
                        } else {
                            let mut unifier = Unifier::new(&mut self.ctx);
                            if let Err(error) = unifier.unify(val_ty, expected_return_ty) {
                                self.errors.push(TypeError::Unification {
                                    error,
                                    expr: Some(*val_expr),
                                });
                            }
                        }
                    }
                }
            }

            Stmt::Box { value, .. } => {
                // Box expression - infer the value type
                self.infer_expr(body, *value, None);
            }
        }
    }

    /// Finish inference and return result
    pub fn finish(mut self) -> InferenceResult {
        // Transfer receiver mutability to context
        self.ctx.receiver_mutability = self.receiver_mutability;

        InferenceResult {
            ctx: self.ctx,
            errors: self.errors,
            lifetime_constraints: self.lifetime_constraints,
        }
    }
}

impl<'a> Default for TypeInference<'a> {
    fn default() -> Self {
        Self::new()
    }
}
