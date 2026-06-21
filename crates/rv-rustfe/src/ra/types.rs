//! Module-level type registry and `ast::Type` -> `rv_core::Ty` resolution for
//! the rust-analyzer-based front-end. Mirrors the tree-sitter `ty.rs`, reading
//! `ra_ap_syntax` AST instead of a CST.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use ra_ap_syntax::ast::{self, HasGenericParams, HasName};
use ra_ap_syntax::AstNode;

use rv_core::{IntTy, Sym, Symbols, Ty as CoreTy};
use rv_ir::{FieldDef, TypeDef, VariantDef};

pub struct StructInfo {
    pub fields: Vec<Sym>,
    pub field_index: HashMap<Sym, u32>,
}
pub struct EnumInfo {
    pub variant_index: HashMap<Sym, (u32, u32)>,
}
pub struct TryShape {
    pub success_idx: u32,
    pub failure_idx: u32,
    pub failure_arity: u32,
}

#[derive(Default)]
pub struct Types {
    structs: HashMap<Sym, StructInfo>,
    enums: HashMap<Sym, EnumInfo>,
    pub defs: Vec<TypeDef>,
    fn_ret_adt: HashMap<Sym, Sym>,
    /// variant name -> owning enum, for resolving *unqualified* variants
    /// (`None`, `Some(x)`, `Ok`, ...). Ambiguous names (shared by >1 enum) map
    /// to `None` so we don't guess.
    variant_to_enum: HashMap<Sym, Option<Sym>>,
    /// A monotonic counter for naming lifted closure functions. `Types` is shared
    /// (`&Types`) across the whole module's lowering, so this gives program-unique,
    /// deterministic `__closure_N` names via interior mutability.
    closure_ctr: Cell<u32>,
}

impl Types {
    pub fn struct_info(&self, name: Sym) -> Option<&StructInfo> {
        self.structs.get(&name)
    }
    pub fn enum_info(&self, name: Sym) -> Option<&EnumInfo> {
        self.enums.get(&name)
    }
    pub fn is_adt(&self, name: Sym) -> bool {
        self.structs.contains_key(&name) || self.enums.contains_key(&name)
    }
    pub fn set_fn_ret(&mut self, name: Sym, adt: Sym) {
        self.fn_ret_adt.insert(name, adt);
    }
    pub fn fn_ret(&self, name: Sym) -> Option<Sym> {
        self.fn_ret_adt.get(&name).copied()
    }

    /// The enum that *uniquely* owns an unqualified variant name, if any.
    pub fn variant_enum(&self, variant: Sym) -> Option<Sym> {
        self.variant_to_enum.get(&variant).copied().flatten()
    }

    /// A fresh, program-unique id for naming a lifted closure function.
    pub fn fresh_closure_id(&self) -> u32 {
        let n = self.closure_ctr.get();
        self.closure_ctr.set(n + 1);
        n
    }

    /// Record an enum's variants in the unqualified-variant index. A name owned
    /// by more than one enum becomes ambiguous (`None`) and won't auto-resolve.
    fn index_variants(&mut self, enum_name: Sym, variants: impl IntoIterator<Item = Sym>) {
        for v in variants {
            self.variant_to_enum
                .entry(v)
                .and_modify(|e| {
                    if *e != Some(enum_name) {
                        *e = None;
                    }
                })
                .or_insert(Some(enum_name));
        }
    }

    /// Inject the built-in `Option`/`Result` enums unless the program declares
    /// its own type of that name.
    pub fn add_builtin_prelude(&mut self, syms: &mut Symbols) {
        let option = syms.intern("Option");
        if !self.is_adt(option) {
            self.add_prelude_enum(option, &[("None", 0), ("Some", 1)], syms);
        }
        let result = syms.intern("Result");
        if !self.is_adt(result) {
            self.add_prelude_enum(result, &[("Ok", 1), ("Err", 1)], syms);
        }
    }
    fn add_prelude_enum(&mut self, name: Sym, variants: &[(&str, u32)], syms: &mut Symbols) {
        let tparam = syms.intern("T");
        let mut variant_index = HashMap::new();
        let mut variant_defs = Vec::new();
        for (i, (vname, arity)) in variants.iter().enumerate() {
            let vsym = syms.intern(vname);
            variant_index.insert(vsym, (i as u32, *arity));
            let fields = (0..*arity).map(|_| CoreTy::Param(tparam)).collect();
            variant_defs.push(VariantDef { name: vsym, fields });
        }
        let vnames: Vec<Sym> = variant_index.keys().copied().collect();
        self.enums.insert(name, EnumInfo { variant_index });
        self.index_variants(name, vnames);
        self.defs.push(TypeDef::Enum { name, type_params: vec![tparam], variants: variant_defs });
    }

    /// Identify the success/failure variant pair of an Option/Result-like enum.
    pub fn try_shape(&self, name: Sym, syms: &Symbols) -> Result<TryShape, String> {
        let info = self
            .enums
            .get(&name)
            .ok_or_else(|| format!("`?` applied to value of non-enum type `{}`", syms.resolve(name)))?;
        if info.variant_index.len() != 2 {
            return Err(format!(
                "`?` requires a two-variant Result/Option-like enum, but `{}` has {}",
                syms.resolve(name),
                info.variant_index.len()
            ));
        }
        let mut failure = None;
        let mut success = None;
        for (&vname, &(vidx, arity)) in &info.variant_index {
            let text = syms.resolve(vname);
            if text == "Err" || text == "None" {
                failure = Some((vidx, arity));
            } else {
                success = Some((vname, vidx, arity));
            }
        }
        let (failure_idx, failure_arity) =
            failure.ok_or_else(|| format!("`?` needs an `Err`/`None` variant on `{}`", syms.resolve(name)))?;
        let (sname, success_idx, sarity) =
            success.ok_or_else(|| format!("`?` needs a success variant on `{}`", syms.resolve(name)))?;
        if sarity != 1 {
            return Err(format!(
                "`?` success variant `{}` must carry exactly one field, not {}",
                syms.resolve(sname),
                sarity
            ));
        }
        Ok(TryShape { success_idx, failure_idx, failure_arity })
    }

    pub fn add_struct(&mut self, s: &ast::Struct, syms: &mut Symbols) -> Result<(), String> {
        let name = syms.intern(&name_text(s.name())?);
        if self.is_adt(name) {
            return Err(format!("duplicate type name `{}`", syms.resolve(name)));
        }
        let type_params = generic_params(s, syms);
        let scope: HashSet<Sym> = type_params.iter().copied().collect();
        let mut fields = Vec::new();
        let mut field_index = HashMap::new();
        let mut field_defs = Vec::new();
        match s.field_list() {
            Some(ast::FieldList::RecordFieldList(rl)) => {
                for f in rl.fields() {
                    let fname = syms.intern(&name_text(f.name())?);
                    let idx = fields.len() as u32;
                    if field_index.insert(fname, idx).is_some() {
                        return Err(format!("duplicate field `{}`", syms.resolve(fname)));
                    }
                    let ty = f.ty().map(|t| resolve_ty(&t, &scope, syms)).transpose()?.unwrap_or(CoreTy::Int);
                    fields.push(fname);
                    field_defs.push(FieldDef { name: fname, ty });
                }
            }
            Some(ast::FieldList::TupleFieldList(tl)) => {
                for (i, f) in tl.fields().enumerate() {
                    // Tuple-struct fields are positional; name them "0", "1", ...
                    let fname = syms.intern(&i.to_string());
                    field_index.insert(fname, i as u32);
                    let ty = f.ty().map(|t| resolve_ty(&t, &scope, syms)).transpose()?.unwrap_or(CoreTy::Int);
                    fields.push(fname);
                    field_defs.push(FieldDef { name: fname, ty });
                }
            }
            None => {} // unit struct
        }
        self.structs.insert(name, StructInfo { fields, field_index });
        self.defs.push(TypeDef::Struct { name, type_params, fields: field_defs });
        Ok(())
    }

    pub fn add_enum(&mut self, e: &ast::Enum, syms: &mut Symbols) -> Result<(), String> {
        let name = syms.intern(&name_text(e.name())?);
        if self.is_adt(name) {
            return Ok(()); // duplicate name (`#[cfg]`-gated): keep the first.
        }
        let type_params = generic_params(e, syms);
        let scope: HashSet<Sym> = type_params.iter().copied().collect();
        let mut variant_index = HashMap::new();
        let mut variant_defs = Vec::new();
        if let Some(vl) = e.variant_list() {
            for v in vl.variants() {
                let vname = syms.intern(&name_text(v.name())?);
                let idx = variant_defs.len() as u32;
                let mut tys = Vec::new();
                if let Some(ast::FieldList::TupleFieldList(tl)) = v.field_list() {
                    for f in tl.fields() {
                        let ty = f.ty().map(|t| resolve_ty(&t, &scope, syms)).transpose()?.unwrap_or(CoreTy::Int);
                        tys.push(ty);
                    }
                }
                let arity = tys.len() as u32;
                if variant_index.insert(vname, (idx, arity)).is_some() {
                    return Err(format!("duplicate variant `{}`", syms.resolve(vname)));
                }
                variant_defs.push(VariantDef { name: vname, fields: tys });
            }
        }
        let vnames: Vec<Sym> = variant_index.keys().copied().collect();
        self.enums.insert(name, EnumInfo { variant_index });
        self.index_variants(name, vnames);
        self.defs.push(TypeDef::Enum { name, type_params, variants: variant_defs });
        Ok(())
    }
}

/// The generic type-parameter names of a declaration, in declaration order.
pub fn generic_params(item: &impl HasGenericParams, syms: &mut Symbols) -> Vec<Sym> {
    let mut out = Vec::new();
    if let Some(gpl) = item.generic_param_list() {
        for p in gpl.type_or_const_params() {
            if let ast::TypeOrConstParam::Type(tp) = p {
                if let Some(n) = tp.name() {
                    out.push(syms.intern(&n.text()));
                }
            }
        }
    }
    out
}

fn name_text(n: Option<ast::Name>) -> Result<String, String> {
    n.map(|n| n.text().to_string()).ok_or_else(|| "missing name".to_string())
}

/// Resolve an `ast::Type` to a core `Ty` within a set of in-scope generic params.
pub fn resolve_ty(ty: &ast::Type, scope: &HashSet<Sym>, syms: &mut Symbols) -> Result<CoreTy, String> {
    match ty {
        ast::Type::PathType(p) => resolve_path_type(p, scope, syms),
        ast::Type::RefType(r) => {
            let mutable = r.mut_token().is_some();
            let inner = r
                .ty()
                .map(|t| resolve_ty(&t, scope, syms))
                .transpose()?
                .unwrap_or(CoreTy::Int);
            Ok(CoreTy::Ref { mutable, inner: Box::new(inner) })
        }
        ast::Type::TupleType(t) => {
            let mut elems = Vec::new();
            for el in t.fields() {
                elems.push(resolve_ty(&el, scope, syms)?);
            }
            // `()` (no fields) is unit.
            if elems.is_empty() {
                Ok(CoreTy::Unit)
            } else {
                Ok(CoreTy::Tuple(elems))
            }
        }
        ast::Type::ArrayType(a) => {
            let elem = a.ty().map(|t| resolve_ty(&t, scope, syms)).transpose()?.unwrap_or(CoreTy::Int);
            // A statically-known length is a fixed array; a const-generic / non-
            // literal length (`[T; N]`) is a sequence of unknown-but-fixed size —
            // modeled (like a slice) as the dynamic-length sequence type, with
            // bounds-checked indexing. Sound: it forgets the exact length.
            match a.const_arg().and_then(|c| c.expr()).and_then(|e| int_literal_usize(&e)) {
                Some(n) => Ok(CoreTy::Array(Box::new(elem), n)),
                None => Ok(CoreTy::Vec(Box::new(elem))),
            }
        }
        // `[T]` — an unsized slice. Its verification semantics are exactly the
        // kernel's sequence model: a dynamic length with bounds-checked indexing
        // (`v[i]` guarded by `0 <= i < len`), i.e. the same as `Vec<T>`. We reuse
        // that model rather than inventing a separate kernel type.
        ast::Type::SliceType(s) => {
            let elem = s.ty().map(|t| resolve_ty(&t, scope, syms)).transpose()?.unwrap_or(CoreTy::Int);
            Ok(CoreTy::Vec(Box::new(elem)))
        }
        other => Err(format!("unsupported type `{:?}`", other.syntax().kind())),
    }
}

fn resolve_path_type(p: &ast::PathType, scope: &HashSet<Sym>, syms: &mut Symbols) -> Result<CoreTy, String> {
    let path = p.path().ok_or_else(|| "empty path type".to_string())?;
    let seg = path.segment().ok_or_else(|| "path type without segment".to_string())?;
    let name = seg
        .name_ref()
        .map(|n| n.text().to_string())
        .ok_or_else(|| "path type without name".to_string())?;

    // Primitives.
    match name.as_str() {
        "bool" => return Ok(CoreTy::Bool),
        "i8" => return Ok(CoreTy::IntN(IntTy { signed: true, bits: 8 })),
        "i16" => return Ok(CoreTy::IntN(IntTy { signed: true, bits: 16 })),
        "i32" => return Ok(CoreTy::IntN(IntTy { signed: true, bits: 32 })),
        "u8" => return Ok(CoreTy::IntN(IntTy { signed: false, bits: 8 })),
        "u16" => return Ok(CoreTy::IntN(IntTy { signed: false, bits: 16 })),
        "u32" => return Ok(CoreTy::IntN(IntTy { signed: false, bits: 32 })),
        "i64" | "i128" | "isize" | "u64" | "u128" | "usize" => return Ok(CoreTy::Int),
        _ => {}
    }
    // `Vec<T>` is a first-class growable vector.
    if name == "Vec" {
        let elem = seg
            .syntax()
            .children()
            .find_map(ast::GenericArgList::cast)
            .and_then(first_type_arg)
            .map(|t| resolve_ty(&t, scope, syms))
            .transpose()?
            .unwrap_or(CoreTy::Int);
        return Ok(CoreTy::Vec(Box::new(elem)));
    }
    let sym = syms.intern(&name);
    if scope.contains(&sym) {
        Ok(CoreTy::Param(sym))
    } else {
        // `Self` and any other named path resolve as a named ADT (last segment).
        Ok(CoreTy::Adt(sym))
    }
}

fn first_type_arg(args: ast::GenericArgList) -> Option<ast::Type> {
    args.generic_args().find_map(|a| match a {
        ast::GenericArg::TypeArg(t) => t.ty(),
        _ => None,
    })
}

/// Replace `Self` (resolved to `self_sym`) with the concrete impl type `real`
/// throughout a type, including nested positions (`&Self`, `Vec<Self>`, ...).
pub fn subst_self(ty: CoreTy, self_sym: Sym, real: Sym) -> CoreTy {
    match ty {
        CoreTy::Adt(s) if s == self_sym => CoreTy::Adt(real),
        CoreTy::Ref { mutable, inner } => {
            CoreTy::Ref { mutable, inner: Box::new(subst_self(*inner, self_sym, real)) }
        }
        CoreTy::Tuple(v) => CoreTy::Tuple(v.into_iter().map(|t| subst_self(t, self_sym, real)).collect()),
        CoreTy::Array(e, n) => CoreTy::Array(Box::new(subst_self(*e, self_sym, real)), n),
        CoreTy::Vec(e) => CoreTy::Vec(Box::new(subst_self(*e, self_sym, real))),
        other => other,
    }
}

/// Parse an integer-literal expression to a `usize` (array lengths / repeats).
pub fn int_literal_usize(e: &ast::Expr) -> Option<usize> {
    if let ast::Expr::Literal(lit) = e {
        if let ast::LiteralKind::IntNumber(n) = lit.kind() {
            return n.value().ok().map(|v| v as usize);
        }
    }
    None
}
