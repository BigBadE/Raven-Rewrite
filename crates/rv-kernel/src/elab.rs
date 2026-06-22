//! Elaboration: surface ([`crate::surface`]) → core ([`crate::term`]).
//!
//! The elaborator's main job is turning **named** binders into **de Bruijn** indices
//! and resolving every name to either a local variable or an environment constant. It
//! also resolves named universe parameters and the self-reference of an inductive
//! while its own constructors are being elaborated.
//!
//! It is intentionally *not* a unifier: there is no implicit-argument inference or
//! metavariables yet. Universe-polymorphic constants need explicit `name.{…}` level
//! arguments (except a self-reference inside an `inductive`, which is filled with the
//! inductive's own parameters). What it does give you is the ability to *write*
//! definitions, inductives, and proofs as readable text and have the trusted
//! [`Kernel`] check them.

use crate::check::{Checker, LocalCtx};
use crate::generate::{CtorSpec, IndSpec};
use crate::kernel::Kernel;
use crate::level::Level;
use crate::surface::{self, Binder, Command, Expr, SLevel};
use crate::term::{name, Term};
use crate::Env;

/// Elaborates surface expressions against a fixed environment.
pub struct Elaborator<'a> {
    env: &'a Env,
    /// Local binders (name, type), innermost last. Carrying the type lets us infer
    /// the operands of `==` and assemble the typing context for obligations.
    locals: Vec<(String, Term)>,
    /// Universe-parameter names in scope.
    level_params: Vec<String>,
    /// The inductive(s) currently being declared (name, universe arity), so their
    /// constructors can reference them — and, for a **mutual** group, each other —
    /// before they are fully installed.
    self_inds: Vec<(String, u32)>,
}

impl<'a> Elaborator<'a> {
    pub fn new(env: &'a Env) -> Self {
        Self { env, locals: Vec::new(), level_params: Vec::new(), self_inds: Vec::new() }
    }

    /// Push a named binder of the given type (innermost). Caller balances with
    /// [`Self::pop_local`].
    pub fn push_local(&mut self, name: &str, ty: Term) {
        self.locals.push((name.to_string(), ty));
    }
    pub fn pop_local(&mut self) {
        self.locals.pop();
    }
    /// Current binder depth.
    pub fn depth(&self) -> usize {
        self.locals.len()
    }
    /// The local typing context (binder types, outermost first).
    pub fn local_ctx(&self) -> LocalCtx {
        let mut ctx = LocalCtx::new();
        for (_, ty) in &self.locals {
            ctx.push(ty.clone());
        }
        ctx
    }

    pub fn with_levels(mut self, levels: &[String]) -> Self {
        self.level_params = levels.to_vec();
        self
    }

    fn elab_level(&self, l: &SLevel) -> Result<Level, String> {
        match l {
            SLevel::Nat(n) => Ok(Level::of_nat(*n)),
            SLevel::Var(s) => self
                .level_params
                .iter()
                .position(|p| p == s)
                .map(|i| Level::param(i as u32))
                .ok_or_else(|| format!("unknown universe parameter '{s}'")),
            SLevel::Add(inner, n) => {
                let mut lv = self.elab_level(inner)?;
                for _ in 0..*n {
                    lv = Level::succ(lv);
                }
                Ok(lv)
            }
        }
    }

    /// Universe arity of a (possibly self-referential) global name.
    fn global_levels(&self, n: &str) -> Option<u32> {
        if let Some((_, l)) = self.self_inds.iter().find(|(sn, _)| sn == n) {
            return Some(*l);
        }
        self.env.get(n).map(|d| d.num_levels())
    }

    /// Resolve a name to a `Const`, supplying universe arguments.
    fn resolve_const(&self, n: &str, levels: Option<&Vec<SLevel>>) -> Result<Term, String> {
        let arity = self.global_levels(n).ok_or_else(|| format!("unknown name '{n}'"))?;
        let level_args = match levels {
            Some(ls) => ls.iter().map(|l| self.elab_level(l)).collect::<Result<Vec<_>, _>>()?,
            None => {
                if arity == 0 {
                    Vec::new()
                } else if self.self_inds.iter().any(|(s, _)| s == n) {
                    // Self/sibling reference: apply the inductive's own universe params.
                    (0..arity).map(Level::param).collect()
                } else {
                    return Err(format!(
                        "'{n}' is universe-polymorphic; supply {arity} level argument(s) as {n}.{{…}}"
                    ));
                }
            }
        };
        if level_args.len() as u32 != arity {
            return Err(format!(
                "'{n}' expects {arity} universe argument(s), got {}",
                level_args.len()
            ));
        }
        Ok(Term::cnst(name(n), level_args))
    }

    /// Elaborate a surface expression to a core term.
    pub fn elab(&mut self, e: &Expr) -> Result<Term, String> {
        match e {
            Expr::Spanned(_, inner) => self.elab(inner),
            Expr::Type(n) => Ok(Term::typ(*n)),
            Expr::Prop => Ok(Term::prop()),
            Expr::Sort(l) => Ok(Term::Sort(self.elab_level(l)?)),
            Expr::Var(n, levels) => {
                // Local variable? (only when no explicit level args)
                if levels.is_none() {
                    if let Some(pos) = self.locals.iter().rposition(|(x, _)| x == n) {
                        return Ok(Term::Var(self.locals.len() - 1 - pos));
                    }
                }
                self.resolve_const(n, levels.as_ref())
            }
            Expr::Hole => Err("`_` (hole) requires the inferring elaborator (crate::elab2)".into()),
            Expr::Match(..) => {
                Err("`match` requires the inferring elaborator (crate::elab2)".into())
            }
            Expr::App(f, a) => Ok(Term::app(self.elab(f)?, self.elab(a)?)),
            Expr::EqOp(a, b) => {
                let ta = self.elab(a)?;
                let tb = self.elab(b)?;
                // Infer `a`'s type (and its universe) to fill `Eq`'s implicit args.
                let chk = Checker::new(self.env);
                let mut ctx = self.local_ctx();
                let ty = chk
                    .infer(&mut ctx, &ta)
                    .map_err(|e| format!("`==`: cannot infer the type of the left side: {e}"))?;
                let lvl = chk
                    .infer_sort(&mut ctx, &ty)
                    .map_err(|e| format!("`==`: left side's type is not a type: {e}"))?;
                Ok(Term::apps(Term::cnst(name("Eq"), vec![lvl]), [ty, ta, tb]))
            }
            Expr::Arrow(a, b) => {
                let ta = self.elab(a)?;
                self.locals.push(("_".to_string(), ta.clone()));
                let tb = self.elab(b);
                self.locals.pop();
                Ok(Term::pi(ta, tb?))
            }
            Expr::Lam(binder, body) => self.elab_binders(binder, body, true),
            Expr::Pi(binder, body) => self.elab_binders(binder, body, false),
            Expr::Let(n, ty, val, body) => {
                let tval = self.elab(val)?;
                let tty = match ty {
                    Some(t) => self.elab(t)?,
                    None => {
                        return Err(
                            "`let` requires a type annotation (`let x : T := …`)".to_string()
                        )
                    }
                };
                self.locals.push((n.clone(), tty.clone()));
                let tbody = self.elab(body);
                self.locals.pop();
                Ok(Term::let_(tty, tval, tbody?))
            }
            Expr::Rewrite(..) | Expr::Decide | Expr::ByCases(..) => Err(
                "`rewrite`/`decide`/`by_cases` are only supported by the inferring elaborator \
                 (use them in a `def`/`fn` with a declared type)"
                    .into(),
            ),
        }
    }

    /// Elaborate a (possibly multi-name) binder group around `body`, building a `λ`
    /// (`is_lam`) or a `Π`. Each name re-elaborates the shared domain in the growing
    /// context, so de Bruijn lifting is automatic.
    fn elab_binders(&mut self, binder: &Binder, body: &Expr, is_lam: bool) -> Result<Term, String> {
        self.elab_names(&binder.names, &binder.ty, body, is_lam)
    }

    fn elab_names(
        &mut self,
        names: &[String],
        ty: &Expr,
        body: &Expr,
        is_lam: bool,
    ) -> Result<Term, String> {
        match names.split_first() {
            None => self.elab(body),
            Some((first, rest)) => {
                let tty = self.elab(ty)?;
                self.locals.push((first.clone(), tty.clone()));
                let inner = self.elab_names(rest, ty, body, is_lam);
                self.locals.pop();
                let inner = inner?;
                Ok(if is_lam { Term::lam(tty, inner) } else { Term::pi(tty, inner) })
            }
        }
    }
}

/// Elaborate a closed surface expression against `env`.
pub fn elaborate(env: &Env, e: &Expr) -> Result<Term, String> {
    Elaborator::new(env).elab(e)
}

/// Parse-and-elaborate a single closed expression string.
pub fn term_of_str(env: &Env, src: &str) -> Result<Term, String> {
    elaborate(env, &surface::parse_expr(src)?)
}

fn count_params(params: &[Binder]) -> usize {
    params.iter().map(|b| b.names.len()).sum()
}

/// Run one command against the kernel.
pub fn run_command(k: &mut Kernel, cmd: &Command) -> Result<(), String> {
    match cmd {
        Command::Def { name: nm, levels, params, ty, body } => {
            let full_ty = surface::pi_telescope(params.clone(), ty.clone());
            let full_body = surface::lam_telescope(params.clone(), body.clone());
            let (tty, tbody) = {
                let mut e = Elaborator::new(k.env()).with_levels(levels);
                let tty = e.elab(&full_ty)?;
                let tbody = e.elab(&full_body)?;
                (tty, tbody)
            };
            k.add_definition(nm, levels.len() as u32, tty, tbody)
        }
        Command::Axiom { name: nm, levels, params, ty } => {
            let full_ty = surface::pi_telescope(params.clone(), ty.clone());
            let tty = Elaborator::new(k.env()).with_levels(levels).elab(&full_ty)?;
            k.add_axiom(nm, levels.len() as u32, tty)
        }
        Command::Inductive { name: nm, levels, params, result, ctors } => {
            let group = [(nm.clone(), levels.len() as u32)];
            let spec = ind_spec_of(k.env(), nm, levels, params, result, ctors, &group)?;
            k.declare_inductive(spec)
        }
        Command::Mutual(members) => {
            // The names+arities of every member, so each constructor can reference any
            // sibling before the group is installed.
            let group: Vec<(String, u32)> = members
                .iter()
                .map(|m| match m {
                    Command::Inductive { name: nm, levels, .. } => Ok((nm.clone(), levels.len() as u32)),
                    _ => Err("a `mutual` block may only contain `inductive` declarations".to_string()),
                })
                .collect::<Result<_, _>>()?;
            let mut specs = Vec::with_capacity(members.len());
            for m in members {
                let Command::Inductive { name: nm, levels, params, result, ctors } = m else {
                    return Err("a `mutual` block may only contain `inductive` declarations".into());
                };
                specs.push(ind_spec_of(k.env(), nm, levels, params, result, ctors, &group)?);
            }
            k.declare_mutual(specs)
        }
        Command::Check(e) => {
            let t = Elaborator::new(k.env()).elab(e)?;
            k.infer(&t).map(|_| ())
        }
        Command::Class(_) => Ok(()), // a class marker is a no-op at the bare-kernel level
        Command::Fn { .. } | Command::Prove { .. } | Command::Instance { .. } => {
            Err("`fn`/`prove`/`instance` require a verification session (see crate::verify)"
                .to_string())
        }
    }
}

/// Elaborate one inductive's surface data into an [`IndSpec`]. `group` is the
/// name+arity of every type being declared together (just this one, or all of a mutual
/// group) so its constructors can reference siblings before installation.
fn ind_spec_of(
    env: &Env,
    nm: &str,
    levels: &[String],
    params: &[Binder],
    result: &Expr,
    ctors: &[(String, Expr)],
    group: &[(String, u32)],
) -> Result<IndSpec, String> {
    let num_levels = levels.len() as u32;
    let num_params = count_params(params);
    let former_ty = {
        let full = surface::pi_telescope(params.to_vec(), result.clone());
        let mut e = Elaborator::new(env).with_levels(levels);
        e.self_inds = group.to_vec();
        e.elab(&full)?
    };
    let mut ctor_specs = Vec::new();
    for (cname, cty) in ctors {
        let full = surface::pi_telescope(params.to_vec(), cty.clone());
        let mut e = Elaborator::new(env).with_levels(levels);
        e.self_inds = group.to_vec();
        let t = e.elab(&full)?;
        // Constructors are qualified by their inductive: `| succ` ⇒ `Nat.succ`
        // (unless the surface name is already dotted).
        let qualified = if cname.contains('.') { cname.clone() } else { format!("{nm}.{cname}") };
        ctor_specs.push(CtorSpec { name: name(&qualified), ty: t });
    }
    Ok(IndSpec {
        name: name(nm),
        num_levels,
        ty: former_ty,
        num_params,
        ctors: ctor_specs,
        rec_name: name(&format!("{nm}.rec")),
    })
}

/// Parse and run a whole program against the kernel.
pub fn run_program(k: &mut Kernel, src: &str) -> Result<(), String> {
    for cmd in surface::parse_program(src)? {
        run_command(k, &cmd)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn elaborate_identity() {
        let env = Env::new();
        let t = term_of_str(&env, "fun (A : Type) (x : A) => x").unwrap();
        let expected = Term::lam(Term::typ(0), Term::lam(Term::Var(0), Term::Var(0)));
        assert_eq!(t, expected);
    }

    #[test]
    fn elaborate_dependent_pi() {
        let env = Env::new();
        let t = term_of_str(&env, "(A : Type) -> A -> A").unwrap();
        let expected = Term::pi(Term::typ(0), Term::pi(Term::Var(0), Term::Var(1)));
        assert_eq!(t, expected);
    }

    #[test]
    fn nat_and_term_in_surface() {
        let mut k = Kernel::new();
        run_program(&mut k, "inductive Nat : Type | zero : Nat | succ : Nat -> Nat").unwrap();
        assert!(k.env().contains("Nat"));
        assert!(k.env().contains("Nat.rec"));
        let two = term_of_str(k.env(), "Nat.succ (Nat.succ Nat.zero)").unwrap();
        k.check(&two, &Term::cnst(name("Nat"), vec![])).unwrap();
    }

    #[test]
    fn polymorphic_def_in_surface() {
        let mut k = Kernel::new();
        run_program(&mut k, "def id.{u} (A : Sort u) (x : A) : A := x").unwrap();
        assert!(k.env().contains("id"));
        run_program(&mut k, "axiom T : Type axiom t : T").unwrap();
        let app = term_of_str(k.env(), "id.{1} T t").unwrap();
        k.check(&app, &Term::cnst(name("T"), vec![])).unwrap();
        assert!(k.def_eq(&app, &Term::cnst(name("t"), vec![])));
    }

    /// Generated recursors respect the `Prop` elimination restriction: a single-constructor
    /// `Prop` (`And`) can large-eliminate (its `rec` carries the extra universe parameter),
    /// while a multi-constructor `Prop` (`Or`) is restricted to `Prop` (no universe param).
    /// Written in Rust-like surface (`enum`/`fn`), checked by the kernel.
    #[test]
    fn generated_recursors_respect_prop_restriction() {
        let mut k = Kernel::new();
        let program = "\
            enum FalseP -> Prop { }
            enum TrueP -> Prop { intro }
            enum Bit -> Prop { lo; hi }";
        run_program(&mut k, program).expect("the propositional connectives should check");

        // A single-/zero-constructor subsingleton `Prop` large-eliminates (its `rec` carries the
        // extra universe param); a two-constructor `Prop` is restricted to `Prop` (no param).
        assert_eq!(k.env().get("TrueP.rec").unwrap().num_levels(), 1);
        assert_eq!(k.env().get("FalseP.rec").unwrap().num_levels(), 1);
        assert_eq!(k.env().get("Bit.rec").unwrap().num_levels(), 0);
    }

    /// Rust-style generic parameters on `enum` (`enum List<A> { … }`) become the
    /// inductive's `num_params`. Constructors thread the parameter, field/return types
    /// use `List<A>`, and—crucially—a *parameterised* single-constructor `Prop`
    /// large-eliminates (its `rec` carries the extra universe param), so `And`-style
    /// connectives are now writeable with real parameters rather than indices.
    #[test]
    fn generic_enum_parameters() {
        let mut k = Kernel::new();
        run_program(
            &mut k,
            "enum Nat { Zero, Succ(Nat) }\n\
             enum Lst<A: Type> { nil, cons(A, Lst<A>) }",
        )
        .expect("a polymorphic list should declare");

        match k.env().get("Lst").unwrap() {
            crate::env::Decl::Inductive(i) => {
                assert_eq!(i.num_params, 1, "the <A> parameter is a param, not an index");
                assert_eq!(i.num_indices, 0);
            }
            _ => panic!("Lst should be an inductive"),
        }

        // The parameter threads through constructors and recursion (`Lst::cons(A, …)`,
        // a length function over any element type).
        run_program(
            &mut k,
            "def len.{} (A : Type) (xs : Lst A) : Nat := \
               Lst.rec.{1} A (fun (_ : Lst A) => Nat) Nat.Zero \
                 (fun (h : A) (t : Lst A) (ih : Nat) => Nat.Succ ih) xs",
        )
        .expect("a generic length should type-check");

        // A parameterised single-constructor `Prop` large-eliminates.
        run_program(&mut k, "enum AndP<a: Prop, b: Prop> -> Prop { mk(x: a, y: b) }")
            .expect("parameterised And should declare");
        assert_eq!(
            k.env().get("AndP.rec").unwrap().num_levels(),
            1,
            "a single-ctor Prop *parameter* type must still large-eliminate"
        );
    }
}
