//! Type checking context

#![allow(
    clippy::min_ident_chars,
    reason = "Ty and TyId are conventional names in type system implementations"
)]

use crate::ty::{TyArena, TyId, TyKind, TyVarId};
use rustc_hash::FxHashMap;
use rv_hir::{DefId, ExprId};

/// Type checking context
#[derive(Debug, Clone, PartialEq)]
pub struct TyContext {
    /// Type arena
    pub types: TyArena,
    /// Next type variable ID
    next_var_id: u32,
    /// Type variable substitutions (solutions from unification)
    pub subst: FxHashMap<TyVarId, TyId>,
    /// Expression types
    pub expr_types: FxHashMap<ExprId, TyId>,
    /// Definition types
    pub def_types: FxHashMap<DefId, TyId>,
    /// Variable types (for parameters and let bindings)
    pub var_types: FxHashMap<rv_intern::Symbol, TyId>,
    /// Receiver mutability for method calls (ExprId → is_mutable)
    pub receiver_mutability: FxHashMap<ExprId, bool>,
}

impl TyContext {
    /// Create a new type context
    pub fn new() -> Self {
        Self {
            types: TyArena::new(),
            next_var_id: 0,
            subst: FxHashMap::default(),
            expr_types: FxHashMap::default(),
            def_types: FxHashMap::default(),
            var_types: FxHashMap::default(),
            receiver_mutability: FxHashMap::default(),
        }
    }

    /// Allocate a fresh type variable
    pub fn fresh_var(&mut self) -> TyVarId {
        let id = TyVarId(self.next_var_id);
        self.next_var_id += 1;
        id
    }

    /// Create a fresh type variable and allocate it
    pub fn fresh_ty_var(&mut self) -> TyId {
        let var_id = self.fresh_var();
        self.types.var(var_id)
    }

    /// Apply substitutions to a type
    pub fn apply_subst(&self, ty_id: TyId) -> TyId {
        let ty = self.types.get(ty_id);
        match &ty.kind {
            TyKind::Var { id } => self
                .subst
                .get(id)
                .map_or(ty_id, |subst_ty| self.apply_subst(*subst_ty)),
            _ => ty_id,
        }
    }

    /// Record the type of an expression
    pub fn set_expr_type(&mut self, expr: ExprId, ty: TyId) {
        self.expr_types.insert(expr, ty);
    }

    /// Get the type of an expression
    pub fn get_expr_type(&self, expr: ExprId) -> Option<TyId> {
        self.expr_types.get(&expr).copied()
    }

    /// Record the type of a definition
    pub fn set_def_type(&mut self, def: DefId, ty: TyId) {
        self.def_types.insert(def, ty);
    }

    /// Get the type of a definition
    pub fn get_def_type(&self, def: DefId) -> Option<TyId> {
        self.def_types.get(&def).copied()
    }
}

impl Default for TyContext {
    fn default() -> Self {
        Self::new()
    }
}
