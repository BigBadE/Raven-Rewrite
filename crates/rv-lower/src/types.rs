//! The module-level type registry built from `struct`/`enum` declarations.
//!
//! Lowering needs to resolve, by interned name:
//!   * a struct's field name -> field index (and the struct's declared field list),
//!   * an enum's variant name -> (variant index, field arity),
//!   * a surface ADT type name -> whether it's a struct or an enum.
//!
//! These maps are derived once per module and threaded (immutably) through the
//! per-function lowering so it can place fields, order struct-literal operands,
//! and resolve match-arm variants.

use std::collections::HashMap;
use std::collections::HashSet;

use rv_core::{Sym, Symbols, Ty as CoreTy};
use rv_ir::{FieldDef, TypeDef, VariantDef};
use rv_syntax::ast::{EnumDecl, StructDecl, Ty as AstTy};

/// Resolved information about a single struct.
pub struct StructInfo {
    /// Field names in declaration order (index = field index).
    pub fields: Vec<Sym>,
    /// name -> index, for resolving `s.f` and reordering struct-literal fields.
    pub field_index: HashMap<Sym, u32>,
}

/// Resolved information about a single enum.
pub struct EnumInfo {
    /// variant name -> (index, arity).
    pub variant_index: HashMap<Sym, (u32, u32)>,
}

/// The `Result`/`Option`-shaped variant pair the `?` operator propagates over:
/// a success variant carrying exactly one payload field, plus a no-/single-field
/// failure variant (`Err`/`None`).
pub struct TryShape {
    /// Index of the SUCCESS variant (`Ok` / `Some`); its arity is always 1.
    pub success_idx: u32,
    /// Index of the FAILURE variant (`Err` / `None`).
    pub failure_idx: u32,
    /// The failure variant's arity (1 for `Err(e)`, 0 for `None`). Determines
    /// whether `?` re-aggregates the failure with or without a payload.
    pub failure_arity: u32,
}

/// The whole-module type registry.
#[derive(Default)]
pub struct Types {
    structs: HashMap<Sym, StructInfo>,
    enums: HashMap<Sym, EnumInfo>,
    /// The `TypeDef`s to embed into `Program.types`, in declaration order.
    pub defs: Vec<TypeDef>,
    /// Method-resolution table: `(receiver ADT name, method name) -> mangled
    /// top-level function name`. Populated from `impl` blocks (both inherent and
    /// trait impls share this table). Used to desugar `recv.m(args)` calls.
    methods: HashMap<(Sym, Sym), Sym>,
    /// Optional record of declared trait method-name sets, keyed by trait name.
    /// Kept for validation only; never affects code generation.
    traits: HashMap<Sym, HashSet<Sym>>,
    /// Function (and mangled-method) name -> the ADT its return type names, when it
    /// returns a struct/enum. Lets `adt_of_expr` resolve the ADT of a call result,
    /// so `match`/`?`/method-calls compose on call results.
    fn_ret_adt: HashMap<Sym, Sym>,
}

impl Types {
    /// Build the registry from a module's struct/enum declarations.
    ///
    /// Field/variant types are resolved to `rv_core::Ty` (an `IDENT` type becomes
    /// `Ty::Adt`). Duplicate type names are rejected.
    pub fn build(
        structs: &[&StructDecl],
        enums: &[&EnumDecl],
        syms: &mut Symbols,
    ) -> Result<Self, String> {
        let mut t = Types::default();

        for s in structs {
            if t.structs.contains_key(&s.name) || t.enums.contains_key(&s.name) {
                return Err(format!("duplicate type name `{}`", syms.resolve(s.name)));
            }
            // The struct's own type parameters scope its field types: a field
            // type naming one of them lowers to `Ty::Param`.
            let type_params: Vec<Sym> = s.generics.iter().map(|g| g.name).collect();
            let scope: HashSet<Sym> = type_params.iter().copied().collect();
            let mut fields = Vec::with_capacity(s.fields.len());
            let mut field_index = HashMap::new();
            let mut field_defs = Vec::with_capacity(s.fields.len());
            for (i, f) in s.fields.iter().enumerate() {
                if field_index.insert(f.name, i as u32).is_some() {
                    return Err(format!(
                        "duplicate field `{}` in struct `{}`",
                        syms.resolve(f.name),
                        syms.resolve(s.name)
                    ));
                }
                fields.push(f.name);
                field_defs.push(FieldDef { name: f.name, ty: resolve_ty(&f.ty, &scope) });
            }
            t.structs.insert(s.name, StructInfo { fields, field_index });
            t.defs.push(TypeDef::Struct { name: s.name, type_params, fields: field_defs });
        }

        for e in enums {
            if t.structs.contains_key(&e.name) || t.enums.contains_key(&e.name) {
                return Err(format!("duplicate type name `{}`", syms.resolve(e.name)));
            }
            // The enum's own type parameters scope its variant field types.
            let type_params: Vec<Sym> = e.generics.iter().map(|g| g.name).collect();
            let scope: HashSet<Sym> = type_params.iter().copied().collect();
            let mut variant_index = HashMap::new();
            let mut variant_defs = Vec::with_capacity(e.variants.len());
            for (i, v) in e.variants.iter().enumerate() {
                if variant_index.insert(v.name, (i as u32, v.fields.len() as u32)).is_some() {
                    return Err(format!(
                        "duplicate variant `{}` in enum `{}`",
                        syms.resolve(v.name),
                        syms.resolve(e.name)
                    ));
                }
                let tys = v.fields.iter().map(|ty| resolve_ty(ty, &scope)).collect();
                variant_defs.push(VariantDef { name: v.name, fields: tys });
            }
            t.enums.insert(e.name, EnumInfo { variant_index });
            t.defs.push(TypeDef::Enum { name: e.name, type_params, variants: variant_defs });
        }

        Ok(t)
    }

    pub fn struct_info(&self, name: Sym) -> Option<&StructInfo> {
        self.structs.get(&name)
    }

    /// Identify the success/failure variant pair of a `Result`/`Option`-like enum
    /// `name`, for lowering the `?` operator.
    ///
    /// The FAILURE variant is the one named `Err` or `None`; the OTHER variant is
    /// SUCCESS and must carry exactly one payload field (`Ok(T)` / `Some(T)`). The
    /// enum must have exactly two variants. Returns a clear `Err` otherwise.
    pub fn try_shape(&self, name: Sym, syms: &Symbols) -> Result<TryShape, String> {
        let info = self.enums.get(&name).ok_or_else(|| {
            format!("`?` applied to value of non-enum type `{}`", syms.resolve(name))
        })?;
        if info.variant_index.len() != 2 {
            return Err(format!(
                "`?` requires a two-variant `Result`/`Option`-like enum, but `{}` has {} variant(s)",
                syms.resolve(name),
                info.variant_index.len()
            ));
        }
        // Find the failure variant by name (`Err` or `None`); the other is success.
        let mut failure: Option<(u32, u32)> = None; // (idx, arity)
        let mut success: Option<(Sym, u32, u32)> = None; // (name, idx, arity)
        for (&vname, &(vidx, arity)) in &info.variant_index {
            let text = syms.resolve(vname);
            if text == "Err" || text == "None" {
                failure = Some((vidx, arity));
            } else {
                success = Some((vname, vidx, arity));
            }
        }
        let (failure_idx, failure_arity) = failure.ok_or_else(|| {
            format!(
                "`?` requires enum `{}` to have an `Err` or `None` failure variant",
                syms.resolve(name)
            )
        })?;
        let (success_name, success_idx, success_arity) = success.ok_or_else(|| {
            format!(
                "`?` requires enum `{}` to have a success variant distinct from its failure variant",
                syms.resolve(name)
            )
        })?;
        // The success variant must carry exactly one payload (`Ok(T)` / `Some(T)`).
        if success_arity != 1 {
            return Err(format!(
                "`?` requires the success variant `{}` of `{}` to carry exactly one field, but it carries {}",
                syms.resolve(success_name),
                syms.resolve(name),
                success_arity
            ));
        }
        Ok(TryShape { success_idx, failure_idx, failure_arity })
    }

    pub fn enum_info(&self, name: Sym) -> Option<&EnumInfo> {
        self.enums.get(&name)
    }

    /// Whether `name` is a known user ADT (struct or enum).
    /// Record that function `name` returns ADT `adt`.
    pub fn set_fn_ret(&mut self, name: Sym, adt: Sym) {
        self.fn_ret_adt.insert(name, adt);
    }
    /// The ADT a function's return type names, if any.
    pub fn fn_ret(&self, name: Sym) -> Option<Sym> {
        self.fn_ret_adt.get(&name).copied()
    }

    pub fn is_adt(&self, name: Sym) -> bool {
        self.structs.contains_key(&name) || self.enums.contains_key(&name)
    }

    /// Look up the mangled top-level function implementing `method` on receiver
    /// type `adt`, if any impl provided it.
    pub fn method(&self, adt: Sym, method: Sym) -> Option<Sym> {
        self.methods.get(&(adt, method)).copied()
    }

    /// Record a trait's declared method-name set (validation only).
    pub fn register_trait(&mut self, trait_name: Sym, method_names: impl IntoIterator<Item = Sym>) {
        self.traits.insert(trait_name, method_names.into_iter().collect());
    }

    /// Register one impl method: resolve its mangled name and add it to the
    /// method-resolution table. Returns the mangled `Sym` so the caller can lower
    /// the method body under that name.
    ///
    /// Mangling is `"TypeName::method"` (interned). Distinct receiver types get
    /// distinct mangled names; the trait name (if any) is used only for the
    /// optional bound check below, never in the mangled symbol.
    pub fn register_method(
        &mut self,
        type_name: Sym,
        method: Sym,
        syms: &mut Symbols,
    ) -> Result<Sym, String> {
        if !self.is_adt(type_name) {
            return Err(format!(
                "`impl` targets unknown type `{}` (only user structs/enums are supported)",
                syms.resolve(type_name)
            ));
        }
        let mangled = mangle_method(type_name, method, syms);
        if self.methods.insert((type_name, method), mangled).is_some() {
            return Err(format!(
                "duplicate method `{}` for type `{}`",
                syms.resolve(method),
                syms.resolve(type_name)
            ));
        }
        Ok(mangled)
    }

    /// Validate that a trait impl provides exactly the trait's declared methods
    /// (best-effort; only runs when the trait was declared in this module).
    pub fn check_trait_impl(
        &self,
        trait_name: Sym,
        type_name: Sym,
        provided: &HashSet<Sym>,
        syms: &Symbols,
    ) -> Result<(), String> {
        if let Some(required) = self.traits.get(&trait_name) {
            for m in required {
                if !provided.contains(m) {
                    return Err(format!(
                        "impl of trait `{}` for `{}` is missing method `{}`",
                        syms.resolve(trait_name),
                        syms.resolve(type_name),
                        syms.resolve(*m)
                    ));
                }
            }
        }
        Ok(())
    }
}

/// Compute the mangled top-level name for a method: `"TypeName::method"`.
pub(crate) fn mangle_method(type_name: Sym, method: Sym, syms: &mut Symbols) -> Sym {
    let mangled = format!("{}::{}", syms.resolve(type_name), syms.resolve(method));
    syms.intern(&mangled)
}

/// Resolve a surface type annotation to a core type within a set of in-scope
/// type parameters (`scope`).
///
/// * `IDENT` whose name is in `scope` -> `Ty::Param` (a generic type parameter);
///   otherwise -> `Ty::Adt` (a named struct/enum).
/// * `Base<args...>` -> `Ty::Adt(Base)` — generic type arguments are **erased**
///   (the VM is dynamic / type-erased), so `Option<i64>` becomes `Adt(Option)`.
/// * `&T` / `&mut T` -> `Ty::Ref`.
pub(crate) fn resolve_ty(ty: &AstTy, scope: &HashSet<Sym>) -> CoreTy {
    match ty {
        AstTy::I64 => CoreTy::Int,
        AstTy::Bool => CoreTy::Bool,
        AstTy::Unit => CoreTy::Unit,
        AstTy::Adt(name) => {
            if scope.contains(name) {
                CoreTy::Param(*name)
            } else {
                CoreTy::Adt(*name)
            }
        }
        AstTy::Param(name) => CoreTy::Param(*name),
        // Erase the type arguments to the base ADT.
        AstTy::Generic { base, .. } => CoreTy::Adt(*base),
        AstTy::Ref { mutable, inner } => {
            CoreTy::Ref { mutable: *mutable, inner: Box::new(resolve_ty(inner, scope)) }
        }
    }
}
