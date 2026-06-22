//! The single front-end: translate the one `rv-syntax` AST into kernel surface
//! [`Command`]s, so the proof/verify path no longer needs a second text parser.
//!
//! `rv-syntax` is the sole lexer+parser for Raven. Its AST has two disjoint halves:
//! the *executable* fragment (statements, refs, loops, …) flows to `rv-lower`→VM, and
//! the *proof* fragment (`fun`, `forall`, `Type`/`Prop`, propositions, dependent
//! `match`, …) is translated here into the kernel's [`Command`]/[`Expr`] AST and handed
//! to [`rv_kernel::verify::Session`]. The kernel re-checks every elaborated term, so a
//! bug in this translation can only make a proof *fail to verify* — never make an
//! unsound program verify.
//!
//! This is the proof-side replacement for `rv_kernel::surface`'s hand-written parser.

use rv_core::{BinOp, Symbols};
use rv_kernel::surface::{Binder, Command, Expr as KExpr, MatchArm, Pattern as KPat};
use rv_syntax::ast::{self, Expr, Item, Module, Pattern, Stmt, Ty};

/// Translate a parsed [`Module`] into the kernel command stream. The `(usize, usize)`
/// line/column pairs are placeholders (`(0, 0)`): the unified front-end reports parse
/// errors itself, and the kernel reports elaboration errors against the source set via
/// [`rv_kernel::verify::Session::set_source`].
pub fn module_to_commands(m: &Module, syms: &Symbols) -> Result<Vec<(Command, (usize, usize))>, String> {
    let t = Tr { syms };
    let mut out = Vec::new();
    for item in &m.items {
        out.push((t.item(item)?, (0, 0)));
    }
    Ok(out)
}

/// Translator state: just the symbol table (to resolve interned names to strings).
struct Tr<'a> {
    syms: &'a Symbols,
}

impl Tr<'_> {
    fn name(&self, s: rv_core::Sym) -> String {
        self.syms.resolve(s).to_string()
    }

    /// A constructor/variable path `Enum::Variant` → the kernel's dotted name `Enum.Variant`.
    fn dotted(&self, a: rv_core::Sym, b: rv_core::Sym) -> String {
        format!("{}.{}", self.syms.resolve(a), self.syms.resolve(b))
    }

    // ---- items --------------------------------------------------------------

    fn item(&self, item: &Item) -> Result<Command, String> {
        match item {
            Item::Enum(e) => self.enum_decl(e),
            Item::Fn(f) => self.fn_decl(f),
            Item::Def(d) => Ok(Command::Def {
                name: self.name(d.name),
                levels: vec![],
                params: self.params(&d.generics, &d.params)?,
                ty: self.ty(&d.ty)?,
                body: self.expr(&d.body)?,
            }),
            Item::Axiom(a) => Ok(Command::Axiom {
                name: self.name(a.name),
                levels: vec![],
                params: self.params(&a.generics, &a.params)?,
                ty: self.ty(&a.ty)?,
            }),
            Item::Struct(_) | Item::Trait(_) | Item::Impl(_) => Err(format!(
                "this item form is not yet supported in the unified proof front-end: {item:?}"
            )),
        }
    }

    /// A data `enum Name<G…> { … }` or an indexed relation
    /// `enum R<G…>(i: T…) -> Prop { C(f: T…) where i == e; … }` → an inductive. Mirrors the
    /// construction the kernel's own `enum` parser performs (uniform params, then indices in
    /// the conclusion; each constructor binds its unpinned indices and fields).
    fn enum_decl(&self, e: &ast::EnumDecl) -> Result<Command, String> {
        let name = self.name(e.name);
        // Generic parameters become uniform `(G : Type)` parameters of the inductive.
        let params: Vec<Binder> = e
            .generics
            .iter()
            .map(|g| Binder { names: vec![self.name(g.name)], ty: KExpr::Type(0), implicit: false })
            .collect();
        // Index binders `(i : T)` and the result sort.
        let indices: Vec<(String, KExpr)> = e
            .indices
            .iter()
            .map(|p| Ok((self.name(p.name), self.ty(&p.ty)?)))
            .collect::<Result<_, String>>()?;
        let result_sort = match &e.result_sort {
            Some(t) => self.ty(t)?,
            None if indices.is_empty() => KExpr::Type(0),
            None => KExpr::Prop,
        };
        // Type former: `T0 -> … -> Tn -> Sort`.
        let result = indices
            .iter()
            .rev()
            .fold(result_sort, |acc, (_, ity)| KExpr::Arrow(Box::new(ity.clone()), Box::new(acc)));

        let mut ctors = Vec::new();
        for v in &e.variants {
            // `where` pins for this constructor.
            let pins: Vec<(String, KExpr)> = v
                .pins
                .iter()
                .map(|(k, val)| Ok((self.name(*k), self.expr(val)?)))
                .collect::<Result<_, String>>()?;
            let pin = |nm: &str| pins.iter().find(|(k, _)| k == nm).map(|(_, e)| e.clone());
            // Conclusion `Name params… indices…` (pinned indices use their `where` value).
            let mut concl = KExpr::Var(name.clone(), None);
            for g in &e.generics {
                concl = KExpr::App(Box::new(concl), Box::new(KExpr::Var(self.name(g.name), None)));
            }
            for (iname, _) in &indices {
                let arg = pin(iname).unwrap_or_else(|| KExpr::Var(iname.clone(), None));
                concl = KExpr::App(Box::new(concl), Box::new(arg));
            }
            // Binders, outermost-first: unpinned indices, then fields (named or positional).
            let mut binders: Vec<(Option<String>, KExpr)> = Vec::new();
            for (iname, ity) in &indices {
                if pin(iname).is_none() {
                    binders.push((Some(iname.clone()), ity.clone()));
                }
            }
            for (i, fty) in v.fields.iter().enumerate() {
                let fname = v.field_names.get(i).and_then(|n| n.map(|s| self.name(s)));
                binders.push((fname, self.ty(fty)?));
            }
            let cty = binders.into_iter().rev().fold(concl, |acc, (nm, ty)| match nm {
                Some(n) => KExpr::Pi(
                    Box::new(Binder { names: vec![n], ty, implicit: false }),
                    Box::new(acc),
                ),
                None => KExpr::Arrow(Box::new(ty), Box::new(acc)),
            });
            ctors.push((self.name(v.name), cty));
        }
        Ok(Command::Inductive { name, levels: vec![], params, result, ctors })
    }

    /// A function declaration. A proof `fn` (return type a proposition / `Type`, body a
    /// single expression) becomes `Command::Fn`; the kernel detects structural recursion
    /// and discharges the obligation.
    fn fn_decl(&self, f: &ast::FnDecl) -> Result<Command, String> {
        let ret = f
            .ret
            .as_ref()
            .ok_or_else(|| format!("proof fn `{}` needs an explicit return type", self.name(f.name)))?;
        Ok(Command::Fn {
            name: self.name(f.name),
            levels: vec![],
            params: self.params(&f.generics, &f.params)?,
            ret: self.ty(ret)?,
            requires: f.requires.iter().map(|e| self.expr(e)).collect::<Result<_, _>>()?,
            ensures: f.ensures.iter().map(|e| self.expr(e)).collect::<Result<_, _>>()?,
            body: self.block_to_expr(&f.body)?,
        })
    }

    /// Generic parameters (auto-inserted implicit `{G : Type}`) followed by value
    /// parameters `(x : T)`.
    fn params(&self, generics: &[ast::GenericParam], value: &[ast::Param]) -> Result<Vec<Binder>, String> {
        let mut out = Vec::new();
        for g in generics {
            out.push(Binder { names: vec![self.name(g.name)], ty: KExpr::Type(0), implicit: true });
        }
        for p in value {
            out.push(Binder { names: vec![self.name(p.name)], ty: self.ty(&p.ty)?, implicit: false });
        }
        Ok(out)
    }

    // ---- function bodies ----------------------------------------------------

    /// Convert a (proof) block into a single kernel expression: a chain of
    /// `let x = e;` bindings ending in a tail expression (`return e` / bare tail).
    fn block_to_expr(&self, b: &ast::Block) -> Result<KExpr, String> {
        self.stmts_to_expr(&b.stmts)
    }

    fn stmts_to_expr(&self, stmts: &[Stmt]) -> Result<KExpr, String> {
        match stmts {
            [Stmt::Return(Some(e))] => self.expr(e),
            [Stmt::Expr(e)] => self.expr(e),
            [Stmt::Let { name, ty, init }, rest @ ..] => {
                let ty = ty.as_ref().map(|t| self.ty(t)).transpose()?;
                Ok(KExpr::Let(
                    self.name(*name),
                    ty.map(Box::new),
                    Box::new(self.expr(init)?),
                    Box::new(self.stmts_to_expr(rest)?),
                ))
            }
            _ => Err("a proof function body must be a (let-chain ending in a) single \
                      expression — imperative statements are not part of the proof fragment"
                .to_string()),
        }
    }

    // ---- types (which are expressions in the dependent setting) -------------

    fn ty(&self, t: &Ty) -> Result<KExpr, String> {
        Ok(match t {
            Ty::Adt(s) | Ty::Param(s) => KExpr::Var(self.name(*s), None),
            Ty::Generic { base, args } => {
                let mut e = KExpr::Var(self.name(*base), None);
                for a in args {
                    e = KExpr::App(Box::new(e), Box::new(self.ty(a)?));
                }
                e
            }
            Ty::Term(e) => self.expr(e)?,
            Ty::I64 | Ty::Bool | Ty::Unit | Ty::Ref { .. } => {
                return Err(format!("this type is not part of the proof fragment: {t:?}"))
            }
        })
    }

    // ---- expressions --------------------------------------------------------

    fn expr(&self, e: &Expr) -> Result<KExpr, String> {
        Ok(match e {
            Expr::Var(s) => KExpr::Var(self.name(*s), None),
            Expr::Call { func, args } => {
                self.apply(KExpr::Var(self.name(*func), None), args)?
            }
            Expr::Apply { callee, args } => {
                let c = self.expr(callee)?;
                self.apply(c, args)?
            }
            Expr::EnumCtor { enum_name, variant, args } => {
                self.apply(KExpr::Var(self.dotted(*enum_name, *variant), None), args)?
            }
            Expr::Bin(BinOp::Eq, a, b) => {
                KExpr::EqOp(Box::new(self.expr(a)?), Box::new(self.expr(b)?))
            }
            Expr::MatchExpr { scrut, arms } => {
                let arms = arms
                    .iter()
                    .map(|(p, body)| Ok(MatchArm { pat: self.pat(p), body: self.expr(body)? }))
                    .collect::<Result<Vec<_>, String>>()?;
                KExpr::Match(Box::new(self.expr(scrut)?), arms)
            }
            Expr::Fun { params, body } => {
                let mut acc = self.expr(body)?;
                for (name, ty) in params.iter().rev() {
                    let ty = match ty {
                        Some(t) => self.expr(t)?,
                        None => KExpr::Hole,
                    };
                    acc = KExpr::Lam(
                        Box::new(Binder { names: vec![self.name(*name)], ty, implicit: false }),
                        Box::new(acc),
                    );
                }
                acc
            }
            Expr::Forall { params, body } => {
                let mut acc = self.expr(body)?;
                for (name, ty) in params.iter().rev() {
                    acc = KExpr::Pi(
                        Box::new(Binder {
                            names: vec![self.name(*name)],
                            ty: self.expr(ty)?,
                            implicit: false,
                        }),
                        Box::new(acc),
                    );
                }
                acc
            }
            Expr::LetIn { name, ty, init, body } => KExpr::Let(
                self.name(*name),
                ty.as_ref().map(|t| self.expr(t)).transpose()?.map(Box::new),
                Box::new(self.expr(init)?),
                Box::new(self.expr(body)?),
            ),
            // `recv.method(args)` in the proof fragment is application of the dotted name
            // `recv.method` (e.g. the IH `hf.rec(gnil)`).
            Expr::MethodCall { recv, method, args } => {
                let callee = match self.expr(recv)? {
                    KExpr::Var(n, None) => KExpr::Var(format!("{n}.{}", self.name(*method)), None),
                    _ => {
                        return Err("a proof-fragment method call must be on a dotted name \
                                    (e.g. `h.rec(..)`)"
                            .to_string())
                    }
                };
                self.apply(callee, args)?
            }
            Expr::Arrow(a, b) => KExpr::Arrow(Box::new(self.expr(a)?), Box::new(self.expr(b)?)),
            Expr::TypeUniv(n) => KExpr::Type(*n),
            Expr::Prop => KExpr::Prop,
            Expr::Hole => KExpr::Hole,
            Expr::Rewrite { eqn, body } => {
                KExpr::Rewrite(Box::new(self.expr(eqn)?), Box::new(self.expr(body)?))
            }
            // `h.rec` — the structural-recursion induction hypothesis on a recursive field,
            // and other dotted projections, are dotted names in the kernel.
            Expr::Field { base, field } => match self.expr(base)? {
                KExpr::Var(n, None) => KExpr::Var(format!("{n}.{}", self.name(*field)), None),
                _ => {
                    return Err("only a dotted name projection (e.g. `h.rec`) is supported in \
                                the proof fragment"
                        .to_string())
                }
            },
            Expr::Decide => KExpr::Decide,
            Expr::ByCases { scrut, tbody, fbody } => KExpr::ByCases(
                Box::new(self.expr(scrut)?),
                Box::new(self.expr(tbody)?),
                Box::new(self.expr(fbody)?),
            ),
            other => {
                return Err(format!(
                    "this expression form is not part of the proof fragment: {other:?}"
                ))
            }
        })
    }

    /// Apply `head` to a list of argument expressions (left-associated `App`s).
    fn apply(&self, mut head: KExpr, args: &[Expr]) -> Result<KExpr, String> {
        for a in args {
            head = KExpr::App(Box::new(head), Box::new(self.expr(a)?));
        }
        Ok(head)
    }

    fn pat(&self, p: &Pattern) -> KPat {
        match p {
            Pattern::Wildcard => KPat::Var("_".to_string()),
            Pattern::Variant { enum_name, variant, binds } => {
                let subs = binds
                    .iter()
                    .map(|b| match b {
                        ast::PatBind::Name(s) => KPat::Var(self.name(*s)),
                        ast::PatBind::Wildcard => KPat::Var("_".to_string()),
                    })
                    .collect();
                KPat::Ctor(self.dotted(*enum_name, *variant), subs)
            }
        }
    }
}
