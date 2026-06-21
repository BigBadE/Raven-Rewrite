//! rust-analyzer-based front-end: parse real Rust with `ra_ap_syntax` and lower
//! a well-scoped subset to `rv_ir::Program<Parsed>`.
//!
//! Public entry: [`parse_modules`]. The IR it produces is shape-identical to the
//! tree-sitter front-end's, so the rest of the pipeline is unchanged.

mod build;
mod lower;
mod spec;
mod types;

use ra_ap_syntax::ast::{self, HasModuleItem, HasName};
use ra_ap_syntax::{Edition, SourceFile};

use rv_core::{Symbols, Ty};
use rv_ir::{BlockId, Function, Parsed, Program};

use build::FnBuilder;
use types::Types;

/// Parse and lower one or more Rust source files (compiled together) into one
/// `Program`. All type declarations across all files are collected before any
/// body is lowered, so references may cross file boundaries.
pub fn parse_modules(sources: &[&str], syms: &mut Symbols) -> Result<Program<Parsed>, String> {
    let mut files = Vec::new();
    for src in sources {
        let parse = SourceFile::parse(src, Edition::Edition2021);
        if let Some(err) = parse.errors().first() {
            return Err(format!("syntax error: {err}"));
        }
        files.push(parse.tree());
    }

    // Flatten inline `mod m { .. }` so nested items are seen as top-level.
    let mut items: Vec<ast::Item> = Vec::new();
    for f in &files {
        flatten_items(f.items(), &mut items);
    }

    // Pass 1: type declarations.
    let mut types = Types::default();
    for it in &items {
        match it {
            ast::Item::Struct(s) => types.add_struct(s, syms)?,
            ast::Item::Enum(e) => types.add_enum(e, syms)?,
            _ => {}
        }
    }
    types.add_builtin_prelude(syms);

    // Pass 2: function / method return ADTs.
    for it in &items {
        match it {
            ast::Item::Fn(f) => register_fn_ret(f, None, &mut types, syms),
            ast::Item::Impl(im) => {
                if let Some(tn) = impl_type_name(im, syms) {
                    for f in impl_methods(im) {
                        register_fn_ret(&f, Some(tn), &mut types, syms);
                    }
                }
            }
            _ => {}
        }
    }

    // Pass 3: lower functions and impl methods.
    let mut funcs = Vec::new();
    for it in &items {
        match it {
            ast::Item::Fn(f) => funcs.extend(lower_fn(f, None, &types, syms)?),
            ast::Item::Impl(im) => {
                let tn = impl_type_name(im, syms)
                    .ok_or_else(|| "`impl` on unsupported type".to_string())?;
                if !types.is_adt(tn) {
                    return Err(format!("`impl` on unknown type `{}`", syms.resolve(tn)));
                }
                for f in impl_methods(im) {
                    funcs.extend(lower_fn(&f, Some(tn), &types, syms)?);
                }
            }
            // trait decls, use, etc.: no IR.
            _ => {}
        }
    }

    Ok(Program { types: types.defs, funcs })
}

fn flatten_items(items: ast::AstChildren<ast::Item>, out: &mut Vec<ast::Item>) {
    for it in items {
        if let ast::Item::Module(m) = &it {
            if let Some(list) = m.item_list() {
                flatten_items(list.items(), out);
                continue;
            }
        }
        out.push(it);
    }
}

fn impl_type_name(im: &ast::Impl, syms: &mut Symbols) -> Option<rv_core::Sym> {
    let ty = im.self_ty()?;
    if let ast::Type::PathType(p) = ty {
        let seg = p.path()?.segment()?;
        return Some(syms.intern(&seg.name_ref()?.text().to_string()));
    }
    None
}

fn impl_methods(im: &ast::Impl) -> Vec<ast::Fn> {
    im.assoc_item_list()
        .map(|l| l.assoc_items().filter_map(|a| match a {
            ast::AssocItem::Fn(f) => Some(f),
            _ => None,
        }).collect())
        .unwrap_or_default()
}

fn register_fn_ret(f: &ast::Fn, self_ty: Option<rv_core::Sym>, types: &mut Types, syms: &mut Symbols) {
    let Some(adt) = ret_adt(f, self_ty, types, syms) else { return };
    let Some(name) = f.name() else { return };
    let method = syms.intern(&name.text());
    let call_name = match self_ty {
        Some(tn) => mangle(tn, method, syms),
        None => method,
    };
    types.set_fn_ret(call_name, adt);
}

/// The ADT a function's return type names, if it is a known struct/enum (`Self`
/// resolves to the impl type).
fn ret_adt(f: &ast::Fn, self_ty: Option<rv_core::Sym>, types: &Types, syms: &mut Symbols) -> Option<rv_core::Sym> {
    let ty = f.ret_type()?.ty()?;
    if let ast::Type::PathType(p) = ty {
        let text = p.path()?.segment()?.name_ref()?.text().to_string();
        if text == "Self" {
            return self_ty;
        }
        let name = syms.intern(&text);
        return types.is_adt(name).then_some(name);
    }
    None
}

/// Lower one function (free or, with `self_ty`, an impl method) to IR. Returns the
/// function itself followed by any closure functions lifted out of its body during
/// lowering (closure conversion), all to be added to the program together.
fn lower_fn(
    f: &ast::Fn,
    self_ty: Option<rv_core::Sym>,
    types: &Types,
    syms: &mut Symbols,
) -> Result<Vec<Function<Parsed>>, String> {
    let method = syms.intern(&f.name().ok_or("function without a name")?.text());
    let name = match self_ty {
        Some(tn) => mangle(tn, method, syms),
        None => method,
    };
    let type_params = types::generic_params(f, syms);
    let scope: std::collections::HashSet<rv_core::Sym> = type_params.iter().copied().collect();

    let mut b = FnBuilder::new(types);
    if let Some(tn) = self_ty {
        b.set_self_ty(tn);
    }
    let self_sym = syms.intern("Self");
    let mut params = Vec::new();

    if let Some(pl) = f.param_list() {
        if let Some(_self) = pl.self_param() {
            let self_sym = syms.intern("self");
            let id = b.new_local(Some(self_sym));
            if let Some(tn) = self_ty {
                b.set_local_adt(id, tn);
                b.set_decl_ty(id, Ty::Adt(tn));
            }
            b.bind(self_sym, id);
            params.push(id);
        }
        for p in pl.params() {
            let Some(ast::Pat::IdentPat(ip)) = p.pat() else {
                return Err("only simple identifier parameters are supported".to_string());
            };
            let pname = syms.intern(&ip.name().ok_or("param without name")?.text());
            let id = b.new_local(Some(pname));
            if let Some(ty) = p.ty() {
                let mut cty = types::resolve_ty(&ty, &scope, syms)?;
                if let Some(tn) = self_ty {
                    cty = types::subst_self(cty, self_sym, tn);
                }
                // A `&[T]` / `&Vec<T>` parameter is modeled as the sequence it
                // views (method calls and indexing auto-deref): peel the borrow so
                // the local is the underlying `Vec<T>` for `.len()` / indexing /
                // `for`-iteration. (Cross-call *execution* of references is limited
                // by the VM's frame-local store; the verification model is exact.)
                if let Ty::Ref { inner, .. } = &cty {
                    if matches!(**inner, Ty::Vec(_)) {
                        cty = (**inner).clone();
                    }
                }
                match &cty {
                    Ty::Adt(a) => b.set_local_adt(id, *a),
                    Ty::Vec(_) => b.mark_vec(id),
                    _ => {}
                }
                b.set_decl_ty(id, cty);
            }
            b.bind(pname, id);
            params.push(id);
        }
    }

    let (pre, post) = spec::collect(f, syms)?;
    if let Some(body) = f.body() {
        b.lower_fn_body(&body, syms)?;
    }
    b.finish_with_default_return();

    let lifted = b.take_lifted();
    let (locals, blocks) = b.into_parts();
    let main = Function {
        name,
        type_params,
        params,
        ret: None,
        pre,
        post,
        locals,
        blocks,
        entry: BlockId(0),
    };
    let mut out = Vec::with_capacity(1 + lifted.len());
    out.push(main);
    out.extend(lifted);
    Ok(out)
}

fn mangle(ty: rv_core::Sym, method: rv_core::Sym, syms: &mut Symbols) -> rv_core::Sym {
    let s = format!("{}::{}", syms.resolve(ty), syms.resolve(method));
    syms.intern(&s)
}
