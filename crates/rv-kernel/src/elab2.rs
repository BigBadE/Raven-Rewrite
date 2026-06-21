//! The **inferring** elaborator: bidirectional elaboration with metavariables, so
//! holes (`_`) and **implicit arguments** (`{A : T}` binders) are *solved by
//! unification* instead of written out.
//!
//! Two judgments, the standard bidirectional pair:
//! * [`Infer::infer`] — synthesize `(term, type)`;
//! * [`Infer::check`] — check an expression against a known type (the mode that
//!   solves holes and runs unification).
//!
//! It produces terms that may contain [`Term::Meta`]; [`Infer::finish`] **zonks** them
//! (substituting solved metas, erroring on unsolved) so the result is metavariable-free
//! and ready for the trusted kernel.
//!
//! This is the **engineer-facing** elaborator (the Rust-like `fn`/`def` surface in
//! [`crate::verify`]). The core/library path ([`crate::elab`]) stays on the explicit,
//! non-inferring elaborator — fully explicit code needs no inference, and keeping it
//! separate means inductive self-references (a name used before it is in the
//! environment) never have to be *typed* by this elaborator.
//!
//! ## Implicit arguments
//!
//! A declaration's surface params record which binders are `implicit` (written
//! `{A : T}`). That implicitness is flattened to a boolean **mask** per name and stored
//! in an [`Implicits`] registry keyed by the global's name. When an application's head
//! is such a global, [`Infer::infer_app`] walks the head's `Π` telescope alongside the
//! mask: at an implicit position it inserts a fresh metavariable (auto-insertion); at an
//! explicit position it consumes the next user argument. So `id(n)` elaborates as
//! `id ?A n` with `?A` solved by unification from `n`'s type.

use std::collections::HashMap;

use crate::check::{Checker, LocalCtx};
use crate::level::Level;
use crate::surface::{Expr, SLevel};
use crate::term::{name, Term};
use crate::unify::{unify, Metas};
use crate::Env;

/// A registry of implicit-argument masks: global name → one `bool` per leading `Π`
/// binder (`true` = implicit, auto-inserted). Trailing entries may be omitted (a
/// missing entry means explicit).
pub type Implicits = HashMap<String, Vec<bool>>;

pub struct Infer<'a> {
    env: &'a Env,
    implicits: &'a Implicits,
    /// Type-class instance registry (class head → instance names), for instance resolution.
    instances: &'a HashMap<String, Vec<String>>,
    metas: Metas,
    /// Local binders `(name, type)`, innermost last.
    locals: Vec<(String, Term)>,
    level_params: Vec<String>,
    /// An inductive being declared (name, universe arity), so its constructors can
    /// reference it before it is installed. Only its `Const` head is produced — never
    /// typed — so this is sound to use during constructor elaboration.
    self_ind: Option<(String, u32)>,
    /// Counter for fresh names generated when desugaring nested `match` patterns.
    fresh_counter: u32,
    /// The source text, for rendering a caret under the offending sub-term on a type error.
    src: Option<&'a str>,
    /// Set once the first (innermost) span-annotated error has had its caret rendered, so
    /// outer `Spanned` wrappers don't re-annotate the same error.
    err_annotated: bool,
    /// Auto-inserted refinement obligations that [`Self::try_discharge`] could not close:
    /// metavariable id → the obligation type. If one is still unsolved at finalization we
    /// report "unsatisfied refinement obligation: <p>" rather than a bare "?N" meta error.
    obligations: HashMap<u32, Term>,
}

impl<'a> Infer<'a> {
    pub fn new(env: &'a Env) -> Self {
        Self::with_implicits(env, EMPTY_IMPLICITS.get_or_init(Implicits::new))
    }

    /// An elaborator that consults `implicits` for auto-insertion.
    pub fn with_implicits(env: &'a Env, implicits: &'a Implicits) -> Self {
        Self {
            env,
            implicits,
            instances: EMPTY_INSTANCES.get_or_init(HashMap::new),
            metas: Metas::new(),
            locals: Vec::new(),
            level_params: Vec::new(),
            self_ind: None,
            fresh_counter: 0,
            src: None,
            err_annotated: false,
            obligations: HashMap::new(),
        }
    }

    /// Supply the source text so type errors can render a caret under the offending sub-term.
    pub fn with_src(mut self, src: &'a str) -> Self {
        self.src = Some(src);
        self
    }

    /// Annotate an error with a caret at `r`, but only the first (innermost) time — outer
    /// `Spanned` wrappers around an already-annotated error leave it untouched.
    fn annotate(&mut self, r: &core::ops::Range<usize>, msg: String) -> String {
        if self.err_annotated || self.src.is_none() {
            return msg;
        }
        self.err_annotated = true;
        self.caret(r, msg)
    }

    /// Render a caret pointing at the source range `r`, appended below `msg`. Produces e.g.
    /// `<msg>\n  at 3:18\n   | def bad : T := offending\n   |                ^^^^^^^^^`.
    fn caret(&self, r: &core::ops::Range<usize>, msg: String) -> String {
        let Some(src) = self.src else { return msg };
        let (start, end) = (r.start.min(src.len()), r.end.min(src.len()));
        // Line containing `start`.
        let line_start = src[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
        let line_end = src[start..].find('\n').map(|i| start + i).unwrap_or(src.len());
        let line_no = src[..start].bytes().filter(|&b| b == b'\n').count() + 1;
        let col = start - line_start + 1;
        let line_text = &src[line_start..line_end];
        // Carets under the [start, end) span, clamped to this line.
        let pad = " ".repeat(start - line_start);
        let span_end = end.min(line_end);
        let underline = "^".repeat((span_end.saturating_sub(start)).max(1));
        format!("{msg}\n  at {line_no}:{col}\n   | {line_text}\n   | {pad}{underline}")
    }

    /// Supply the type-class instance registry, enabling instance resolution (`decide` and
    /// class-typed implicit holes).
    pub fn with_instances(mut self, instances: &'a HashMap<String, Vec<String>>) -> Self {
        self.instances = instances;
        self
    }

    pub fn with_levels(mut self, levels: &[String]) -> Self {
        self.level_params = levels.to_vec();
        self
    }

    pub fn with_self_ind(mut self, name: &str, num_levels: u32) -> Self {
        self.self_ind = Some((name.to_string(), num_levels));
        self
    }

    /// Push a named binder of `ty` (innermost). Balance with [`Self::pop_local`].
    pub fn push_local(&mut self, name: &str, ty: Term) {
        self.locals.push((name.to_string(), ty));
    }
    pub fn pop_local(&mut self) {
        self.locals.pop();
    }
    pub fn depth(&self) -> usize {
        self.locals.len()
    }

    fn local_ctx(&self) -> LocalCtx {
        let mut c = LocalCtx::new();
        for (_, ty) in &self.locals {
            c.push(ty.clone());
        }
        c
    }

    /// The sort of a (just-built) `Π`/`→` type, computed with the kernel's `imax` rule —
    /// crucially `imax _ 0 = 0`, so `(x : A) → Prop` is itself a `Prop` (impredicative
    /// `Prop`). Falls back to `Type 0` if the type still has metavariables that prevent a
    /// definite sort (the previous unconditional behaviour).
    fn pi_sort(&self, t: &Term) -> Level {
        let tz = self.metas.zonk(t).unwrap_or_else(|_| t.clone());
        Checker::new(self.env)
            .infer_sort(&mut self.local_ctx(), &tz)
            .unwrap_or_else(|_| Level::succ(Level::Zero))
    }

    fn lookup_local(&self, n: &str) -> Option<(usize, Term)> {
        let pos = self.locals.iter().rposition(|(x, _)| x == n)?;
        let idx = self.locals.len() - 1 - pos;
        let ty = self.locals[pos].1.lift(idx as isize + 1, 0);
        Some((idx, ty))
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

    /// Synthesize `(term, type)`.
    pub fn infer(&mut self, e: &Expr) -> Result<(Term, Term), String> {
        match e {
            Expr::Spanned(r, inner) => self.infer(inner).map_err(|m| self.annotate(r, m)),
            Expr::Type(n) => Ok((Term::typ(*n), Term::typ(n + 1))),
            Expr::Prop => Ok((Term::prop(), Term::typ(0))),
            Expr::Sort(l) => {
                let lv = self.elab_level(l)?;
                Ok((Term::Sort(lv.clone()), Term::Sort(Level::succ(lv))))
            }
            Expr::Hole => {
                // Unknown value of unknown type; both fresh.
                let ty = self.metas.fresh();
                let t = self.metas.fresh();
                Ok((t, ty))
            }
            Expr::Var(n, levels) => self.infer_name(n, levels.as_ref()),
            Expr::App(..) => {
                let (head, args) = unfold_surface_apps(e);
                self.infer_app(head, &args)
            }
            Expr::Lam(binder, body) => self.infer_lam(&binder.names, &binder.ty, body),
            Expr::Pi(binder, body) => {
                let t = self.build_pi(&binder.names, &binder.ty, body)?;
                let s = self.pi_sort(&t);
                Ok((t, Term::Sort(s)))
            }
            Expr::Arrow(a, b) => {
                let (at, _) = self.infer(a)?;
                // `b` is inferred *under* the arrow's (anonymous) binder so its references
                // to outer locals are already lifted into the binder's context; build the
                // `Π` directly. (Do **not** use `Term::arrow`, which would lift `b` a
                // second time and corrupt any free variable in the codomain.)
                self.locals.push(("_".into(), at.clone()));
                let r = self.infer(b);
                self.locals.pop();
                let (bt, _) = r?;
                let t = Term::pi(at, bt);
                let s = self.pi_sort(&t);
                Ok((t, Term::Sort(s)))
            }
            Expr::EqOp(a, b) => {
                let (ta, tya) = self.infer(a)?;
                let tb = self.check(b, &tya)?;
                // Eq's universe: the sort of `tya` (computed from a zonked, meta-free type).
                let tya_z = self.metas.zonk(&tya)?;
                let lvl = Checker::new(self.env)
                    .infer_sort(&mut self.local_ctx(), &tya_z)
                    .map_err(|err| format!("`==`: {err}"))?;
                Ok((
                    Term::apps(Term::cnst(name("Eq"), vec![lvl]), [tya, ta, tb]),
                    Term::prop(),
                ))
            }
            Expr::Match(scrut, arms) => self.elab_match(scrut, arms, None),
            Expr::Rewrite(..) => Err(
                "`rewrite h => body` can only be used where the goal type is known (a checking \
                 position — e.g. a `def`/`fn` body with a declared return type)"
                    .into(),
            ),
            Expr::Decide => Err(
                "`decide` can only be used where the goal type is known (a checking position)"
                    .into(),
            ),
            Expr::ByCases(..) => Err(
                "`by_cases` can only be used where the goal type is known (a checking position)"
                    .into(),
            ),
            Expr::Let(n, ty, val, body) => {
                let tty = match ty {
                    Some(t) => self.infer(t)?.0,
                    None => return Err("`let` requires a type annotation (`let x : T := …`)".into()),
                };
                let tval = self.check(val, &tty)?;
                self.locals.push((n.clone(), tty.clone()));
                let r = self.infer(body);
                self.locals.pop();
                let (tb, tbty) = r?;
                Ok((Term::let_(tty, tval.clone(), tb), tbty.instantiate(&tval)))
            }
        }
    }

    /// `λ`-binders (possibly several names): build the lambda and its `Π` type.
    fn infer_lam(&mut self, names: &[String], ty: &Expr, body: &Expr) -> Result<(Term, Term), String> {
        match names.split_first() {
            None => self.infer(body),
            Some((first, rest)) => {
                let (dom, _) = self.infer(ty)?;
                self.locals.push((first.clone(), dom.clone()));
                let r = self.infer_lam(rest, ty, body);
                self.locals.pop();
                let (inner, inner_ty) = r?;
                Ok((Term::lam(dom.clone(), inner), Term::pi(dom, inner_ty)))
            }
        }
    }

    /// `Π`-binders (possibly several names): build the dependent function *type* term.
    fn build_pi(&mut self, names: &[String], ty: &Expr, body: &Expr) -> Result<Term, String> {
        match names.split_first() {
            None => Ok(self.infer(body)?.0),
            Some((first, rest)) => {
                let (dom, _) = self.infer(ty)?;
                self.locals.push((first.clone(), dom.clone()));
                let r = self.build_pi(rest, ty, body);
                self.locals.pop();
                Ok(Term::pi(dom, r?))
            }
        }
    }

    fn infer_name(&mut self, n: &str, levels: Option<&Vec<SLevel>>) -> Result<(Term, Term), String> {
        // Local variable (only when no explicit level args).
        if levels.is_none() {
            if let Some((idx, ty)) = self.lookup_local(n) {
                return Ok((Term::Var(idx), ty));
            }
        }
        // Self-reference inside an inductive being declared: produce its `Const` head
        // (we never need its type during constructor *type* elaboration).
        if let Some((sn, arity)) = self.self_ind.clone() {
            if sn == n {
                let level_args = self.resolve_level_args(n, levels, arity, true)?;
                // Its type is not yet in the environment; a constructor type expression
                // only ever puts the self-reference in type position, where `infer`
                // would ask for this. Return a placeholder sort type — sound because the
                // kernel re-checks the assembled inductive.
                return Ok((Term::cnst(name(n), level_args), Term::typ(0)));
            }
        }
        let decl = self.env.get(n).ok_or_else(|| format!("unknown name '{n}'"))?;
        let arity = decl.num_levels();
        let level_args = self.resolve_level_args(n, levels, arity, false)?;
        let ty = decl.ty().instantiate_levels(&level_args);
        Ok((Term::cnst(name(n), level_args), ty))
    }

    /// Resolve the universe arguments for `n`: use the explicit `.{…}` if given, else
    /// (arity 0) none, else fresh **level metavariables** to be solved by inference.
    fn resolve_level_args(
        &mut self,
        _n: &str,
        levels: Option<&Vec<SLevel>>,
        arity: u32,
        self_ref: bool,
    ) -> Result<Vec<Level>, String> {
        match levels {
            Some(ls) => ls.iter().map(|l| self.elab_level(l)).collect(),
            None if arity == 0 => Ok(Vec::new()),
            None if self_ref => Ok((0..arity).map(Level::param).collect()),
            None => Ok((0..arity).map(|_| self.metas.fresh_level()).collect()),
        }
    }

    /// Elaborate an application spine `head arg0 arg1 …`, auto-inserting implicit
    /// arguments declared for `head`.
    fn infer_app(&mut self, head: &Expr, args: &[&Expr]) -> Result<(Term, Term), String> {
        let (mut term, mut ty) = self.infer(head)?;
        let mask = self.implicit_mask(head);
        let mut ai = 0usize; // next user argument
        let mut pos = 0usize; // binder position (indexes the mask)
        loop {
            let tyw = self.force_whnf(&ty);
            let Term::Pi(_, dom, cod) = &tyw else {
                if ai < args.len() {
                    return Err(format!(
                        "too many arguments: applied {} but the head takes fewer",
                        args.len()
                    ));
                }
                break;
            };
            let dom = (**dom).clone();
            if mask.get(pos).copied().unwrap_or(false) {
                // Implicit binder. First try to *auto-discharge* it as a proof obligation
                // (a refinement `where p` whose `p` now reduces to a canonical proposition);
                // if that succeeds we fill the proof directly. Otherwise insert a fresh
                // metavariable carrying its declared domain type, so solving it can also fix
                // the binder's universe level.
                let arg = match self.try_discharge(&dom) {
                    Some(proof) => proof,
                    None => {
                        let m = self.metas.fresh_typed(self.depth(), dom.clone());
                        // Remember a *concrete* (meta-free) obligation we couldn't discharge,
                        // so a later "unsolved meta" is reported as a refinement failure.
                        if let (Term::Meta(id), Ok(z)) = (&m, self.metas.zonk(&dom)) {
                            if !z.has_meta() {
                                self.obligations.insert(*id, z);
                            }
                        }
                        m
                    }
                };
                ty = cod.instantiate(&arg);
                term = Term::app(term, arg);
                pos += 1;
                continue;
            }
            if ai >= args.len() {
                break; // out of explicit arguments — a partial application
            }
            let at = self.check(args[ai], &dom)?;
            ty = cod.instantiate(&at);
            term = Term::app(term, at);
            ai += 1;
            pos += 1;
        }
        Ok((term, ty))
    }

    /// Try to **auto-discharge** an implicit proof obligation `dom` (a refinement
    /// `where p` whose predicate is now concrete). Returns a closed proof term when the
    /// obligation reduces to something canonical, or `None` to fall back to a metavariable:
    ///
    /// * `True`           → `True.intro`;
    /// * `Eq A a b` with `a ≡ b` (defeq) → `Eq.refl A a`.
    ///
    /// The kernel re-checks whatever we emit, so an over-eager guess can never make an
    /// unsound program verify — at worst it would be rejected, which is why each arm only
    /// fires once the obligation is fully determined and provably canonical.
    fn try_discharge(&mut self, dom: &Term) -> Option<Term> {
        let p = self.metas.zonk(dom).ok()?;
        if p.has_meta() {
            return None; // an underdetermined obligation can't be discharged yet
        }
        let w = self.force_whnf(&p);
        let (head, args) = w.unfold_apps();
        match &head {
            // A decidable/`Prop`-valued predicate that reduced to `True`.
            Term::Const(n, _) if *n == name("True") => {
                Some(Term::cnst(name("True.intro"), vec![]))
            }
            // A reflexive equation precondition (`x where x == c` at a literal, etc.).
            Term::Const(n, ls) if *n == name("Eq") && args.len() == 3 && ls.len() == 1 => {
                let (ty_a, a, b) = (args[0].clone(), args[1].clone(), args[2].clone());
                if Checker::new(self.env).def_eq(&a, &b) {
                    Some(Term::apps(Term::cnst(name("Eq.refl"), ls.clone()), [ty_a, a]))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// The implicit mask for an application head, if it is a global with one.
    fn implicit_mask(&self, head: &Expr) -> Vec<bool> {
        if let Expr::Var(n, _) = head {
            if self.lookup_local(n).is_none() {
                if let Some(m) = self.implicits.get(n) {
                    return m.clone();
                }
            }
        }
        Vec::new()
    }

    /// Check `e` against `expected`, solving holes and unifying.
    pub fn check(&mut self, e: &Expr, expected: &Term) -> Result<Term, String> {
        match e {
            Expr::Spanned(r, inner) => {
                self.check(inner, expected).map_err(|m| self.annotate(r, m))
            }
            // A hole becomes a fresh metavariable *carrying its expected type*, so when
            // it is solved at a use site the type (and any universe level in it) flows
            // back. Unification at its use sites solves it.
            Expr::Hole => Ok(self.metas.fresh_typed(self.depth(), expected.clone())),
            // `match` checked against a known result type uses it directly as the motive.
            Expr::Match(scrut, arms) => {
                let (t, _) = self.elab_match(scrut, arms, Some(expected))?;
                Ok(t)
            }
            // Check a `λ` against its expected `Π` type bidirectionally: push the expected
            // codomain *inward* so a `match` (or another `λ`) in the body inherits its
            // motive/type from the expectation, instead of being inferred blind. Without
            // this, `match scrut { C(..) => fun x => match … }` loses the dependent motive
            // of the inner `match`. Falls back to infer+unify when the expected type isn't
            // (yet) a function type.
            Expr::Lam(binder, body) => self.check_lam(&binder.names, &binder.ty, body, expected),
            // `rewrite h => body`: rewrite the expected goal by `h : Eq A a b` (replacing `a`
            // with `b`), elaborate `body` against the rewritten goal, and wrap it back with
            // `Eq.subst`. The motive is abstracted from the *expected* type — which is why
            // this only works in checking position.
            Expr::Rewrite(eqn, body) => self.check_rewrite(eqn, body, expected),
            Expr::Decide => self.check_decide(expected),
            Expr::ByCases(scrut, tbody, fbody) => self.check_bycases(scrut, tbody, fbody, expected),
            _ => {
                let (t, ty) = self.infer(e)?;
                let ctx = self.local_ctx();
                unify(self.env, &mut self.metas, &ctx, &ty, expected)
                    .map_err(|err| format!("type mismatch: {err}"))?;
                Ok(t)
            }
        }
    }

    /// Elaborate `by_cases scrut => tbody | fbody` against `expected`: split the goal on the
    /// `Bool` scrutinee via `Bool.rec`, refining the goal in each branch (so a stuck `match
    /// scrut …` reduces), then check each branch body.
    fn check_bycases(
        &mut self,
        scrut: &Expr,
        tbody: &Expr,
        fbody: &Expr,
        expected: &Term,
    ) -> Result<Term, String> {
        let bool_ty = Term::cnst(name("Bool"), vec![]);
        let scrut_t = self.check(scrut, &bool_ty)?;
        let scrut_z = self.metas.zonk(&scrut_t)?;
        let g = self.metas.zonk(expected)?;
        // motive `fun (x : Bool) => expected[scrut := x]`, and the level of the goal.
        let motive_body = abstract_occurrences(&g, &scrut_z, 0);
        let motive = Term::lam(bool_ty.clone(), motive_body.clone());
        let lvl = Checker::new(self.env)
            .infer_sort(&mut self.local_ctx(), &g)
            .map_err(|e| format!("by_cases: {e}"))?;
        // Refined branch goals; check each body against its (now-reducible) goal.
        let tgoal = motive_body.instantiate(&Term::cnst(name("Bool.true"), vec![]));
        let fgoal = motive_body.instantiate(&Term::cnst(name("Bool.false"), vec![]));
        let tt = self.check(tbody, &tgoal)?;
        let ff = self.check(fbody, &fgoal)?;
        // Bool.rec.{lvl} motive (false-case) (true-case) scrut  : motive scrut (= expected).
        Ok(Term::apps(Term::cnst(name("Bool.rec"), vec![lvl]), [motive, ff, tt, scrut_t]))
    }

    /// Elaborate `decide` against `expected`: resolve `Decidable expected` and emit
    /// `of_decide_eq_true expected inst (Eq.refl Bool Bool.true)`. The kernel re-check
    /// accepts it exactly when `decide expected inst` reduces to `true`.
    fn check_decide(&mut self, expected: &Term) -> Result<Term, String> {
        // The goal must be fully known to resolve a `Decidable` instance for it.
        let p = self.metas.zonk(expected).map_err(|_| {
            "decide: the goal is not yet determined (needs a fully-known proposition)".to_string()
        })?;
        let dec_ty = Term::apps(Term::cnst(name("Decidable"), vec![]), [p.clone()]);
        let inst = self.metas.fresh_typed(self.depth(), dec_ty);
        // Resolve the instance now (the goal is concrete), then build the reflection proof.
        self.resolve_instances()?;
        let refl = Term::apps(
            Term::cnst(name("Eq.refl"), vec![Level::of_nat(1)]),
            [Term::cnst(name("Bool"), vec![]), Term::cnst(name("Bool.true"), vec![])],
        );
        Ok(Term::apps(Term::cnst(name("of_decide_eq_true"), vec![]), [p, inst, refl]))
    }

    /// Elaborate `rewrite h => body` against `expected` (see [`Self::check`]).
    fn check_rewrite(&mut self, eqn: &Expr, body: &Expr, expected: &Term) -> Result<Term, String> {
        // Elaborate the equation and read off `Eq.{u} A a b`.
        let (eqn_t, eqn_ty) = self.infer(eqn)?;
        let eqn_ty = self.force_whnf(&self.metas.zonk(&eqn_ty)?);
        let (head, args) = eqn_ty.unfold_apps();
        let lvl = match &head {
            Term::Const(n, ls) if *n == name("Eq") && args.len() == 3 && ls.len() == 1 => {
                ls[0].clone()
            }
            _ => {
                return Err(format!(
                    "rewrite: expected an equation `a == b`, but the proof has type {}",
                    eqn_ty.pretty()
                ))
            }
        };
        let ty_a = args[0].clone();
        let a = args[1].clone();
        let b = args[2].clone();
        // Motive `fun (x : A) => expected[a := x]`, the rewritten goal `expected[a := b]`.
        let expected_z = self.metas.zonk(expected)?;
        let motive_body = abstract_occurrences(&expected_z, &a, 0);
        let motive = Term::lam(ty_a.clone(), motive_body.clone());
        let new_goal = motive_body.instantiate(&b);
        let sub = self.check(body, &new_goal)?;
        // result : motive a (= expected) via `Eq.subst A motive b a (symm h) (sub : motive b)`.
        let symm = Term::apps(
            Term::cnst(name("Eq.symm"), vec![lvl.clone()]),
            [ty_a.clone(), a.clone(), b.clone(), eqn_t],
        );
        Ok(Term::apps(
            Term::cnst(name("Eq.subst"), vec![lvl]),
            [ty_a, motive, b, a, symm, sub],
        ))
    }

    /// Check a (possibly multi-name) `λ` against an expected type by peeling one binder at
    /// a time against the expected `Π`, checking the body against the codomain in the
    /// extended context. Falls back to infer+unify if the expected type isn't a `Π`.
    fn check_lam(
        &mut self,
        names: &[String],
        ty: &Expr,
        body: &Expr,
        expected: &Term,
    ) -> Result<Term, String> {
        let Some((first, rest)) = names.split_first() else {
            return self.check(body, expected);
        };
        let exp = self.force_whnf(expected);
        let Term::Pi(_, dom, cod) = &exp else {
            // Not (yet) a function type — recover by inferring the whole λ and unifying.
            let (t, t_ty) = self.infer_lam(names, ty, body)?;
            let ctx = self.local_ctx();
            unify(self.env, &mut self.metas, &ctx, &t_ty, expected)
                .map_err(|e| format!("type mismatch: {e}"))?;
            return Ok(t);
        };
        let dom = (**dom).clone();
        let cod = (**cod).clone();
        // The surface annotation must agree with the expected domain.
        let (ann, _) = self.infer(ty)?;
        let ctx = self.local_ctx();
        unify(self.env, &mut self.metas, &ctx, &ann, &dom)
            .map_err(|e| format!("λ binder type mismatch: {e}"))?;
        self.push_local(first, dom.clone());
        let inner = self.check_lam(rest, ty, body, &cod);
        self.pop_local();
        Ok(Term::lam(dom, inner?))
    }

    fn fresh_var(&mut self) -> String {
        self.fresh_counter += 1;
        format!("%p{}", self.fresh_counter)
    }

    /// **Pattern-matching compiler** (Maranget-style): desugar a `match` with nested
    /// patterns, wildcards, and catch-alls into a tree of *flat* single-level matches
    /// (each of which the recursor compiler handles). Operates on a pattern matrix whose
    /// columns are scrutinee expressions; at each step it switches the first constructor
    /// column on every constructor of its inductive, specialising the rows.
    fn compile_patterns(
        &mut self,
        scrut: &Expr,
        arms: &[crate::surface::MatchArm],
    ) -> Result<Expr, String> {
        let rows: Vec<(Vec<crate::surface::Pattern>, Expr)> =
            arms.iter().map(|a| (vec![a.pat.clone()], a.body.clone())).collect();
        self.compile_matrix(std::slice::from_ref(scrut), rows)
    }

    fn compile_matrix(
        &mut self,
        occs: &[Expr],
        rows: Vec<(Vec<crate::surface::Pattern>, Expr)>,
    ) -> Result<Expr, String> {
        use crate::env::Decl;
        use crate::surface::{MatchArm, Pattern};
        let (pats0, body0) = rows.first().ok_or("non-exhaustive match")?;
        // If the first row is all variables, it matches: bind each to its occurrence.
        if pats0.iter().all(|p| matches!(p, Pattern::Var(_))) {
            let mut b = body0.clone();
            for (p, occ) in pats0.iter().zip(occs) {
                if let Pattern::Var(x) = p {
                    if x != "_" {
                        b = subst_var(&b, x, occ);
                    }
                }
            }
            return Ok(b);
        }
        // Otherwise pick the first column whose row-0 pattern is a constructor, and find
        // its inductive (from any constructor mentioned in that column).
        let col = pats0.iter().position(|p| matches!(p, Pattern::Ctor(..))).unwrap();
        let cname = rows
            .iter()
            .find_map(|(ps, _)| match &ps[col] {
                Pattern::Ctor(c, _) => Some(c.clone()),
                _ => None,
            })
            .unwrap();
        let ind = match self.env.get(&cname) {
            Some(Decl::Constructor(c)) => match self.env.get(&c.ind) {
                Some(Decl::Inductive(i)) => i.clone(),
                _ => return Err(format!("'{}' has no inductive", c.ind)),
            },
            _ => return Err(format!("'{cname}' is not a constructor")),
        };
        // One flat arm per constructor of the inductive.
        let mut out_arms = Vec::new();
        for cj in ind.ctors.iter() {
            let arity = match self.env.get(cj) {
                Some(Decl::Constructor(c)) => c.num_fields,
                _ => return Err(format!("'{cj}' is not a constructor")),
            };
            let fresh: Vec<String> = (0..arity).map(|_| self.fresh_var()).collect();
            // New occurrences: the column is replaced by the constructor's field vars.
            let mut new_occs = occs.to_vec();
            let field_occs: Vec<Expr> = fresh.iter().map(|f| Expr::Var(f.clone(), None)).collect();
            new_occs.splice(col..col + 1, field_occs);
            // Specialise the rows that match `cj`.
            let mut new_rows = Vec::new();
            for (ps, body) in &rows {
                match &ps[col] {
                    Pattern::Ctor(c, subs) if *c == **cj => {
                        let mut np = ps.clone();
                        np.splice(col..col + 1, subs.iter().cloned());
                        new_rows.push((np, body.clone()));
                    }
                    Pattern::Var(x) => {
                        // A variable matches every constructor; the column becomes `arity`
                        // wildcards and `x` is bound to the whole scrutinee of this column.
                        let mut np = ps.clone();
                        np.splice(col..col + 1, (0..arity).map(|_| Pattern::Var("_".into())));
                        let nb = if x != "_" { subst_var(body, x, &occs[col]) } else { body.clone() };
                        new_rows.push((np, nb));
                    }
                    Pattern::Ctor(..) => {} // a different constructor — this row doesn't apply
                }
            }
            let arm_body = self.compile_matrix(&new_occs, new_rows)?;
            out_arms.push(MatchArm {
                pat: Pattern::Ctor(cj.to_string(), fresh.into_iter().map(Pattern::Var).collect()),
                body: arm_body,
            });
        }
        Ok(Expr::Match(Box::new(occs[col].clone()), out_arms))
    }

    /// Elaborate a `match`, compiling it to the scrutinee inductive's recursor with a
    /// **constant (non-dependent) motive**. Each arm becomes a minor premise; a
    /// recursive field's induction hypothesis is bound as `<field>.rec`, which is how
    /// structural recursion is expressed (no fixpoint in the kernel). Scope: inductives
    /// with parameters but *no indices*.
    fn elab_match(
        &mut self,
        scrut: &Expr,
        arms: &[crate::surface::MatchArm],
        expected: Option<&Term>,
    ) -> Result<(Term, Term), String> {
        use crate::env::Decl;
        // 0. Nested patterns / wildcards / catch-alls: desugar the whole `match` into a
        //    tree of *flat* single-level matches (each compiled to a recursor below), then
        //    elaborate that. Only flat constructor patterns reach the recursor compiler.
        if arms.iter().any(|a| !a.pat.is_flat()) {
            let flat = self.compile_patterns(scrut, arms)?;
            return match expected {
                Some(e) => self.check(&flat, e).map(|t| (t, e.clone())),
                None => self.infer(&flat),
            };
        }
        // 1. Elaborate the scrutinee and find its inductive head `I.{ls} params…`.
        let (e_term, e_ty) = self.infer(scrut)?;
        let e_ty = self.force_whnf(&e_ty);
        let (head, params) = e_ty.unfold_apps();
        let Term::Const(ind_name, ls) = &head else {
            return Err(format!("`match` scrutinee must have an inductive type, got {e_ty:?}"));
        };
        let ind = match self.env.get(ind_name) {
            Some(Decl::Inductive(i)) => i.clone(),
            _ => return Err(format!("`match` scrutinee type '{ind_name}' is not an inductive")),
        };
        let k = ind.num_params;
        let m = ind.num_indices;
        if params.len() != k + m {
            return Err(format!(
                "'{ind_name}' applied to {} args, expected {} param(s) + {m} index(es)",
                params.len(),
                k
            ));
        }
        let indices: Vec<Term> = params[k..].to_vec();
        let params: Vec<Term> = params[..k].to_vec();
        // 2. Exhaustiveness: exactly one arm per constructor, no unknown constructors.
        for arm in arms {
            let (ctor, _) = arm.pat.as_flat().unwrap();
            if !ind.ctors.iter().any(|c| **c == *ctor) {
                return Err(format!("'{ctor}' is not a constructor of '{ind_name}'"));
            }
        }

        // 3. The result type R (the motive's codomain). In check mode it is given; else
        //    inferred from the first arm.
        let r_ty = match expected.and_then(|e| self.metas.zonk(e).ok()).filter(|t| !t.has_meta()) {
            Some(r) => r,
            None => self.infer_match_result(ind_name, ls, k, &params, arms)?,
        };
        // The motive's elimination universe.
        let u_r = Checker::new(self.env)
            .infer_sort(&mut self.local_ctx(), &r_ty)
            .map_err(|e| format!("`match`: result type is not a type: {e}"))?;

        // 4. Recursor levels: a non-`Prop` (or subsingleton) inductive's recursor has one
        //    extra universe parameter (the elimination universe); a `Prop`-restricted one
        //    does not, and may only eliminate into `Prop`.
        let rec = match self.env.get(&ind.recursor) {
            Some(Decl::Recursor(r)) => r.clone(),
            _ => return Err(format!("inductive '{ind_name}' has no recursor")),
        };
        if rec.num_motives != 1 {
            // A member of a *mutual* inductive group: compile via the multi-motive recursor
            // (real motive+arms for this member, trivial motive+minors for the siblings).
            return self.compile_match_mutual(
                &ind, &rec, ind_name, ls, k, &params, &r_ty, &u_r, e_term, arms,
            );
        }
        let rec_levels: Vec<Level> = if rec.num_levels == ind.num_levels + 1 {
            ls.iter().cloned().chain(std::iter::once(u_r.clone())).collect()
        } else {
            if !matches!(u_r.normalize(), Level::Zero) {
                return Err(format!(
                    "`match` on '{ind_name}' can only produce a `Prop` (it is a \
                     large-elimination-restricted proposition)"
                ));
            }
            ls.to_vec()
        };

        // 5. Motive: `λ (i₀ … iₘ₋₁) (s : I params i₀…iₘ₋₁). R[indices,scrutinee ↦ binders]`
        //    — the result type with the index arguments *and* the scrutinee abstracted.
        //    With no indices and a result not mentioning the scrutinee this is the
        //    constant motive `λ s. R`; abstracting generalises both the dependent and the
        //    indexed cases (each branch is checked against the goal specialised to that
        //    constructor's indices).
        let index_doms = self.index_domains(&ind, ls, &params)?; // J₀ … Jₘ₋₁
        // I params i₀ … iₘ₋₁  (at binder depth m: params lifted past the index binders).
        let mut ind_app = Term::cnst(ind_name.clone(), ls.clone());
        for p in &params {
            ind_app = Term::app(ind_app, p.lift(m as isize, 0));
        }
        for l in 0..m {
            ind_app = Term::app(ind_app, Term::Var(m - 1 - l));
        }
        // Body M: R lifted past the m+1 motive binders, with each index aᵢ ↦ binder iᵢ
        // (de Bruijn `m-l` from the top) and the scrutinee ↦ `s` (de Bruijn 0).
        let mut motive_body = r_ty.lift(m as isize + 1, 0);
        motive_body = replace_with_var(&motive_body, &e_term.lift(m as isize + 1, 0), 0);
        for (l, a) in indices.iter().enumerate() {
            motive_body = replace_with_var(&motive_body, &a.lift(m as isize + 1, 0), m - l);
        }
        // Assemble: λ i₀ … iₘ₋₁ (s : I params i…). M.
        let mut motive = Term::lam(ind_app, motive_body);
        for d in index_doms.into_iter().rev() {
            motive = Term::lam(d, motive);
        }

        // 6. Peel the recursor's own type, substituting params then the motive, to obtain
        //    each minor premise's exact type — then build each minor λ. We thread the
        //    minor terms back in (via `instantiate`) so later minor types stay correct.
        let mut t = rec.ty.instantiate_levels(&rec_levels);
        for p in &params {
            let Term::Pi(_, _, body) = &t else {
                return Err("recursor type: expected a parameter Π".into());
            };
            t = body.instantiate(p);
        }
        let Term::Pi(_, _, body) = &t else {
            return Err("recursor type: expected the motive Π".into());
        };
        t = body.instantiate(&motive);

        let mut minors = Vec::with_capacity(ind.ctors.len());
        for cname in &ind.ctors {
            let Term::Pi(_, mdom, mbody) = &t else {
                return Err("recursor type: expected a minor-premise Π".into());
            };
            let minor_ty = (**mdom).clone();
            let arm = arms
                .iter()
                .find(|a| a.pat.as_flat().is_some_and(|(c, _)| c == &**cname))
                .ok_or_else(|| format!("non-exhaustive `match`: no arm for '{cname}'"))?;
            let minor =
                self.build_minor(&[ind_name.to_string()], ls, k, cname, &minor_ty, arm)?;
            t = mbody.instantiate(&minor);
            minors.push(minor);
        }

        // 7. Assemble: I.rec.{rec_levels} params… motive minors… indices… scrutinee.
        let mut call = Term::cnst(ind.recursor.clone(), rec_levels);
        for p in &params {
            call = Term::app(call, p.clone());
        }
        call = Term::app(call, motive);
        for minor in minors {
            call = Term::app(call, minor);
        }
        for a in &indices {
            call = Term::app(call, a.clone());
        }
        call = Term::app(call, e_term);
        Ok((call, r_ty))
    }

    /// The index domains `J₀ … Jₘ₋₁` of inductive `ind`, specialised to the actual
    /// `params` (each `Jₗ` in the context of the earlier indices). Peeled from the type
    /// former `Π params. Π indices. Sort _`.
    fn index_domains(
        &self,
        ind: &crate::env::Inductive,
        ls: &[Level],
        params: &[Term],
    ) -> Result<Vec<Term>, String> {
        let mut t = ind.ty.instantiate_levels(ls);
        for p in params {
            let Term::Pi(_, _, body) = &t else {
                return Err("type former: expected a parameter Π".into());
            };
            t = body.instantiate(p);
        }
        let (doms, _) = peel_all_pis(t);
        Ok(doms)
    }

    /// Compile a **bundle of mutually-recursive functions** (one per member of a mutual
    /// inductive group, each `fn f(x: Iₜ …) -> Rₜ { match x { … } }`) jointly into a
    /// single use of each member's recursor: shared motives (one per function) and a
    /// shared band of minors (the pooled branches), so a recursive `.rec` on a sibling's
    /// field resolves to that sibling's computation. Returns `(name, type, value)` for
    /// each function, ready to install. Scope: each function takes the scrutinee as its
    /// sole non-parametric argument (the common case — `tsize`/`fsize`, `even`/`odd`).
    pub fn compile_bundle(
        &mut self,
        members: &[BundleMember],
        group: &[String],
    ) -> Result<Vec<(String, Term, Term)>, String> {
        use crate::env::Decl;
        struct MInfo {
            ind: String,
            ls: Vec<Level>,
            ips: Vec<Term>,
            scrut_ty: Term,
            ret: Term,
        }
        // 1. Elaborate each function's scrutinee type and return type.
        let mut minfo = Vec::new();
        for m in members {
            let scrut_raw = self.infer(&m.scrut_ty)?.0;
            let scrut_ty = self.finish(&scrut_raw)?;
            let (head, ips) = scrut_ty.unfold_apps();
            let Term::Const(ind, ls) = &head else {
                return Err(format!("'{}' does not recurse on an inductive", m.def_name));
            };
            self.push_local(&m.scrut_name, scrut_ty.clone());
            let ret_raw = self.infer(&m.ret)?.0;
            let ret = self.finish(&ret_raw)?;
            self.pop_local();
            minfo.push(MInfo { ind: ind.to_string(), ls: ls.clone(), ips, scrut_ty, ret });
        }
        for (t, mi) in minfo.iter().enumerate() {
            if mi.ind != group[t] {
                return Err("mutual function bundle is not ordered by its inductive group".into());
            }
        }
        // 2. Recursor metadata + elimination universe.
        let ind0 = match self.env.get(&group[0]) {
            Some(Decl::Inductive(i)) => i.clone(),
            _ => return Err(format!("'{}' is not an inductive", group[0])),
        };
        let rec0 = match self.env.get(&ind0.recursor) {
            Some(Decl::Recursor(r)) => r.clone(),
            _ => return Err("missing recursor".into()),
        };
        let k = ind0.num_params;
        let u_r = Checker::new(self.env)
            .infer_sort(&mut LocalCtx::new(), &minfo[0].ret)
            .map_err(|e| format!("mutual fn return type: {e}"))?;
        let rec_levels: Vec<Level> = if rec0.num_levels == ind0.num_levels + 1 {
            minfo[0].ls.iter().cloned().chain(std::iter::once(u_r)).collect()
        } else {
            minfo[0].ls.clone()
        };
        // 3. Motives `C_t = λ (s : I_t ips). R_t` (R_t already in the `s` context).
        let motives: Vec<Term> =
            minfo.iter().map(|mi| Term::lam(mi.scrut_ty.clone(), mi.ret.clone())).collect();
        // 4. Peel the recursor type (substitute params + motives) and build the shared
        //    minor band from the pooled branches, in the group's constructor order.
        let mut t = rec0.ty.instantiate_levels(&rec_levels);
        for p in &minfo[0].ips {
            let Term::Pi(_, _, b) = &t else { return Err("recursor: parameter Π".into()) };
            t = b.instantiate(p);
        }
        for c in &motives {
            let Term::Pi(_, _, b) = &t else { return Err("recursor: motive Π".into()) };
            t = b.instantiate(c);
        }
        let mut minors = Vec::new();
        for (s, mem) in members.iter().enumerate() {
            let inds = match self.env.get(&group[s]) {
                Some(Decl::Inductive(i)) => i.clone(),
                _ => return Err("missing inductive".into()),
            };
            for cname in inds.ctors.iter() {
                let Term::Pi(_, mdom, mbody) = &t else {
                    return Err("recursor: minor Π".into());
                };
                let minor_ty = (**mdom).clone();
                let arm = mem
                    .arms
                    .iter()
                    .find(|a| a.pat.as_flat().is_some_and(|(c, _)| c == &**cname))
                    .ok_or_else(|| format!("'{}' has no arm for '{cname}'", mem.def_name))?;
                let minor = self.build_minor(group, &minfo[s].ls, k, cname, &minor_ty, arm)?;
                t = mbody.instantiate(&minor);
                minors.push(minor);
            }
        }
        // 5. Assemble each function: `λ (s : I_t ips). I_t.rec.{…} ips motives… minors… s`.
        let mut out = Vec::new();
        for (ti, mi) in minfo.iter().enumerate() {
            let mut call = Term::cnst(name(&format!("{}.rec", group[ti])), rec_levels.clone());
            for p in &mi.ips {
                call = Term::app(call, p.clone());
            }
            for c in &motives {
                call = Term::app(call, c.clone());
            }
            for mnr in &minors {
                call = Term::app(call, mnr.clone());
            }
            call = Term::app(call, Term::Var(0));
            let value = Term::lam(mi.scrut_ty.clone(), call);
            let def_ty = Term::pi(mi.scrut_ty.clone(), mi.ret.clone());
            out.push((members[ti].def_name.clone(), def_ty, value));
        }
        Ok(out)
    }

    /// Build one minor premise λ for constructor `cname`, given its expected `minor_ty`
    /// (already specialised to the actual params + motive). Binds the constructor's
    /// fields under the arm's pattern names, and each recursive field's induction
    /// hypothesis as `<field>.rec`; checks the body against the minor's conclusion.
    fn build_minor(
        &mut self,
        group: &[String],
        ls: &[Level],
        k: usize,
        cname: &str,
        minor_ty: &Term,
        arm: &crate::surface::MatchArm,
    ) -> Result<Term, String> {
        let kinds = self.ctor_rec_kinds(group, cname, k, ls)?;
        let (_, vars) = arm.pat.as_flat().ok_or("`match` arm is not a flat pattern")?;
        if vars.len() != kinds.len() {
            return Err(format!(
                "pattern '{cname}' binds {} field(s) but the constructor has {}",
                vars.len(),
                kinds.len()
            ));
        }
        let mut t = minor_ty.clone();
        let mut doms: Vec<Term> = Vec::new();
        let mut pushed = 0usize;
        for (i, &is_rec) in kinds.iter().enumerate() {
            let Term::Pi(_, fdom, fbody) = &t else {
                return Err(format!("minor for '{cname}': expected a field Π"));
            };
            let fdom = (**fdom).clone();
            doms.push(fdom.clone());
            self.push_local(vars[i], fdom);
            pushed += 1;
            t = (**fbody).clone();
            if is_rec {
                let Term::Pi(_, ihdom, ihbody) = &t else {
                    return Err(format!("minor for '{cname}': expected an IH Π"));
                };
                let ihdom = (**ihdom).clone();
                doms.push(ihdom.clone());
                self.push_local(&format!("{}.rec", vars[i]), ihdom);
                pushed += 1;
                t = (**ihbody).clone();
            }
        }
        // `t` is now the conclusion `motive (ctor params fields)` (β-reduces to R).
        let body = self.check(&arm.body, &t);
        for _ in 0..pushed {
            self.pop_local();
        }
        let mut lam = body?;
        for d in doms.into_iter().rev() {
            lam = Term::lam(d, lam);
        }
        Ok(lam)
    }

    /// Compile a `match` on a member of a **mutual** inductive group via its multi-motive
    /// recursor. The scrutinee's member gets the real motive `λ s. M` and real minors (from
    /// the arms); every *sibling* member gets a trivial motive `λ s. (R → R)` and identity
    /// minors `λ …fields…ih…. (λ z. z)` — `R → R` is inhabited regardless of whether `R`
    /// itself is, so no auxiliary `Unit` is needed. Non-indexed groups only (which is all
    /// the mutual-inductive machinery supports).
    #[allow(clippy::too_many_arguments)]
    fn compile_match_mutual(
        &mut self,
        ind: &crate::env::Inductive,
        rec: &crate::env::Recursor,
        ind_name: &str,
        ls: &[Level],
        k: usize,
        params: &[Term],
        r_ty: &Term,
        u_r: &Level,
        e_term: Term,
        arms: &[crate::surface::MatchArm],
    ) -> Result<(Term, Term), String> {
        use crate::env::Decl;
        if ind.num_indices != 0 {
            return Err(format!(
                "`match` on the indexed mutual inductive '{ind_name}' is not supported"
            ));
        }
        let group: Vec<String> = ind.group.iter().map(|n| n.to_string()).collect();
        let j = group
            .iter()
            .position(|n| n == ind_name)
            .ok_or_else(|| format!("'{ind_name}' is not in its own mutual group"))?;

        // Recursor levels: append the elimination universe unless the group is Prop-bound.
        let rec_levels: Vec<Level> = if rec.num_levels == ind.num_levels + 1 {
            ls.iter().cloned().chain(std::iter::once(u_r.clone())).collect()
        } else {
            if !matches!(u_r.normalize(), Level::Zero) {
                return Err(format!(
                    "`match` on '{ind_name}' can only produce a `Prop` (its group is \
                     large-elimination-restricted)"
                ));
            }
            ls.to_vec()
        };

        // The fully-applied type former `I_t params` for member t (the motive's domain).
        let member_app = |t: usize| -> Term {
            let mut a = Term::cnst(name(&group[t]), ls.to_vec());
            for p in params {
                a = Term::app(a, p.clone());
            }
            a
        };

        // Motives, in group order: the real `λ s. M` at the scrutinee member, the trivial
        // `λ s. (R → R)` elsewhere (R lifted past the `s` and `z` binders).
        let motives: Vec<Term> = (0..group.len())
            .map(|t| {
                if t == j {
                    let mut body = r_ty.lift(1, 0);
                    body = replace_with_var(&body, &e_term.lift(1, 0), 0);
                    Term::lam(member_app(t), body)
                } else {
                    let codom = Term::pi(r_ty.lift(1, 0), r_ty.lift(2, 0));
                    Term::lam(member_app(t), codom)
                }
            })
            .collect();

        // Peel the recursor type: params, then all motives, to expose the minor band.
        let mut t = rec.ty.instantiate_levels(&rec_levels);
        for p in params {
            let Term::Pi(_, _, b) = &t else { return Err("recursor: parameter Π".into()) };
            t = b.instantiate(p);
        }
        for c in &motives {
            let Term::Pi(_, _, b) = &t else { return Err("recursor: motive Π".into()) };
            t = b.instantiate(c);
        }

        // Minors for every member's constructors, in group order.
        let mut minors: Vec<Term> = Vec::new();
        for (t_idx, member) in group.iter().enumerate() {
            let inds = match self.env.get(member) {
                Some(Decl::Inductive(i)) => i.clone(),
                _ => return Err(format!("'{member}' is not an inductive")),
            };
            for cname in inds.ctors.iter() {
                let Term::Pi(_, mdom, mbody) = &t else {
                    return Err("recursor: minor Π".into());
                };
                let minor_ty = (**mdom).clone();
                let minor = if t_idx == j {
                    let arm = arms
                        .iter()
                        .find(|a| a.pat.as_flat().is_some_and(|(c, _)| c == &**cname))
                        .ok_or_else(|| format!("non-exhaustive `match`: no arm for '{cname}'"))?;
                    self.build_minor(&group, ls, k, cname, &minor_ty, arm)?
                } else {
                    self.build_dummy_minor(&group, ls, k, cname, &minor_ty)?
                };
                t = mbody.instantiate(&minor);
                minors.push(minor);
            }
        }

        // Assemble: I_j.rec.{levels} params… motives… minors… scrutinee.
        let mut call = Term::cnst(ind.recursor.clone(), rec_levels);
        for p in params {
            call = Term::app(call, p.clone());
        }
        for c in motives {
            call = Term::app(call, c);
        }
        for mnr in minors {
            call = Term::app(call, mnr);
        }
        call = Term::app(call, e_term);
        Ok((call, r_ty.clone()))
    }

    /// A trivial minor premise for a sibling member's constructor: bind the whole telescope
    /// (fields + recursive-field IHs) and return the identity `λ z. z`, which inhabits the
    /// conclusion `R → R`. Used by [`Self::compile_match_mutual`] for the members that are
    /// not the one being matched.
    fn build_dummy_minor(
        &self,
        group: &[String],
        ls: &[Level],
        k: usize,
        cname: &str,
        minor_ty: &Term,
    ) -> Result<Term, String> {
        let kinds = self.ctor_rec_kinds(group, cname, k, ls)?;
        let mut t = minor_ty.clone();
        let mut doms: Vec<Term> = Vec::new();
        for &is_rec in &kinds {
            let Term::Pi(_, fdom, fbody) = &t else {
                return Err(format!("dummy minor for '{cname}': expected a field Π"));
            };
            doms.push((**fdom).clone());
            t = (**fbody).clone();
            if is_rec {
                let Term::Pi(_, ihdom, ihbody) = &t else {
                    return Err(format!("dummy minor for '{cname}': expected an IH Π"));
                };
                doms.push((**ihdom).clone());
                t = (**ihbody).clone();
            }
        }
        // `t` is the conclusion `motive (c fields)`, which β-reduces to `R → R`.
        let concl = crate::reduce::Reducer::new(self.env).whnf(&t);
        let Term::Pi(_, cdom, _) = &concl else {
            return Err(format!("dummy minor for '{cname}': conclusion is not `R → R`"));
        };
        let mut lam = Term::lam((**cdom).clone(), Term::Var(0));
        for d in doms.into_iter().rev() {
            lam = Term::lam(d, lam);
        }
        Ok(lam)
    }

    /// Which fields of constructor `cname` are recursive — a direct occurrence of **any**
    /// member of `group` (so a mutual field, e.g. a `Forest` inside a `Tree` constructor,
    /// is detected as recursive). Derived from the constructor's declared type.
    fn ctor_rec_kinds(
        &self,
        group: &[String],
        cname: &str,
        k: usize,
        ls: &[Level],
    ) -> Result<Vec<bool>, String> {
        let decl = self.env.get(cname).ok_or_else(|| format!("unknown constructor '{cname}'"))?;
        let ty = decl.ty().instantiate_levels(ls);
        let (_, rest) =
            peel_pis(ty, k).ok_or_else(|| format!("constructor '{cname}' lacks {k} params"))?;
        let (fields, _) = peel_all_pis(rest);
        Ok(fields
            .iter()
            .map(|f| group.iter().any(|g| occurs_const(g, f)))
            .collect())
    }

    /// Infer a `match`'s result type from its first arm (used when no expected type is
    /// supplied): elaborate that arm's body with its fields bound (and recursive-field
    /// hypotheses bound to fresh metavariables), then read off and zonk its type.
    fn infer_match_result(
        &mut self,
        ind_name: &str,
        ls: &[Level],
        k: usize,
        params: &[Term],
        arms: &[crate::surface::MatchArm],
    ) -> Result<Term, String> {
        let arm = arms.first().ok_or("`match` has no arms and no result-type annotation")?;
        let (ctor, vars) = arm.pat.as_flat().ok_or("`match` arm is not a flat pattern")?;
        let kinds = self.ctor_rec_kinds(&[ind_name.to_string()], ctor, k, ls)?;
        if vars.len() != kinds.len() {
            return Err(format!("pattern '{ctor}' binds the wrong number of fields"));
        }
        // Field domains specialised to the actual params.
        let decl = self.env.get(ctor).unwrap();
        let cty = decl.ty().instantiate_levels(ls);
        let mut after = cty;
        for p in params {
            let Term::Pi(_, _, b) = &after else {
                return Err("constructor type: expected a parameter Π".into());
            };
            after = b.instantiate(p);
        }
        let mut pushed = 0usize;
        // Push the fields in order (the constructor type binds one Π per field, no IH).
        for var in &vars {
            let Term::Pi(_, fdom, fbody) = &after else {
                return Err("constructor type: expected a field Π".into());
            };
            let fdom = (**fdom).clone();
            self.push_local(var, fdom);
            pushed += 1;
            after = (**fbody).clone();
        }
        // Then bind each recursive field's hypothesis (fresh-typed) after the fields, so
        // they don't perturb the field-domain indices — enough to *infer* the body type.
        for (i, &is_rec) in kinds.iter().enumerate() {
            if is_rec {
                let ih = self.metas.fresh();
                self.push_local(&format!("{}.rec", vars[i]), ih);
                pushed += 1;
            }
        }
        let r = self.infer(&arm.body);
        for _ in 0..pushed {
            self.pop_local();
        }
        let (_, ty) = r?;
        self.metas
            .zonk(&ty)
            .map_err(|_| "could not infer the `match` result type; add a type annotation".into())
    }

    /// Push each name of a parameter telescope as a local, re-elaborating the shared
    /// domain type in the growing context. Returns the per-name domain terms (raw, i.e.
    /// possibly still containing metas — zonk later), suitable for re-wrapping a `Π`/`λ`
    /// telescope. The caller balances the pushes with [`Self::pop_local`].
    pub fn push_params(&mut self, params: &[crate::surface::Binder]) -> Result<Vec<Term>, String> {
        let mut doms = Vec::new();
        for b in params {
            for n in &b.names {
                let (dom, _) = self.infer(&b.ty)?;
                doms.push(dom.clone());
                self.push_local(n, dom);
            }
        }
        Ok(doms)
    }

    fn force_whnf(&self, t: &Term) -> Term {
        crate::nbe::Nbe::with_metas(self.env, self.metas.solutions())
            .normalize_open(self.depth(), t)
    }

    /// Zonk a term: substitute solved metas, error on unsolved. First reports any
    /// auto-inserted refinement obligation that was never discharged, with a precise
    /// message naming the precondition (instead of the bare "could not infer ?N").
    pub fn finish(&self, t: &Term) -> Result<Term, String> {
        self.check_obligations()?;
        self.metas.zonk(t)
    }

    /// Fail if any auto-inserted refinement obligation is still unsolved (the precondition
    /// could not be auto-discharged and no proof was supplied).
    fn check_obligations(&self) -> Result<(), String> {
        for (id, ty) in &self.obligations {
            if !self.metas.is_solved(*id) {
                return Err(format!(
                    "unsatisfied refinement obligation `{}`: the precondition could not be \
                     discharged automatically",
                    ty.pretty()
                ));
            }
        }
        Ok(())
    }

    /// **Instance resolution.** After a body has elaborated, fill every still-unsolved
    /// metavariable whose (now-zonkable) type is headed by a class that has registered
    /// instances. Runs to a fixpoint, so an instance that itself needs instances (e.g.
    /// `Show (List A)` needing `Show A`) is resolved by a later round. Speculative
    /// candidate attempts are rolled back via the metacontext checkpoint.
    pub fn resolve_instances(&mut self) -> Result<(), String> {
        if self.instances.is_empty() {
            return Ok(());
        }
        loop {
            let mut progress = false;
            let mut unresolved: Option<String> = None;
            for (id, _depth, ty) in self.metas.unsolved_typed() {
                if self.metas.is_solved(id) {
                    continue;
                }
                // The class goal must be fully determined (no remaining metas) to resolve.
                let Ok(goal) = self.metas.zonk(&ty) else { continue };
                let (head, _) = goal.unfold_apps();
                let Term::Const(c, _) = &head else { continue };
                let Some(cands) = self.instances.get(c.to_string().as_str()) else { continue };
                let mut solved = false;
                for inst in cands {
                    if self.try_instance(inst, &goal, id)? {
                        progress = true;
                        solved = true;
                        break;
                    }
                }
                if !solved {
                    unresolved = Some(goal.pretty());
                }
            }
            match unresolved {
                None => return Ok(()),
                Some(g) if !progress => {
                    return Err(format!("no instance found for `{g}`"));
                }
                _ => {} // made progress; another round may resolve the rest
            }
        }
    }

    /// Try to satisfy the class goal `goal` (= `C args…`) with instance `inst`, solving
    /// metavariable `id` to the instance term on success. Returns `false` (rolling back any
    /// speculative solving) if the instance's result type doesn't unify with `goal`.
    fn try_instance(&mut self, inst: &str, goal: &Term, id: u32) -> Result<bool, String> {
        let Some(decl) = self.env.get(inst) else { return Ok(false) };
        let nlev = decl.num_levels();
        let decl_ty = decl.ty().clone();
        let cp = self.metas.checkpoint();
        // Instantiate the instance's universe parameters with fresh level metas.
        let lvls: Vec<Level> = (0..nlev).map(|_| self.metas.fresh_level()).collect();
        let mut ty = decl_ty.instantiate_levels(&lvls);
        let mut term = Term::cnst(name(inst), lvls);
        // Auto-fill every leading Π binder of the instance with a fresh (typed) meta — these
        // are the instance's own parameters and premises (resolved in later fixpoint rounds).
        loop {
            let tw = self.force_whnf(&ty);
            let Term::Pi(_, dom, cod) = &tw else { break };
            let m = self.metas.fresh_typed(self.depth(), (**dom).clone());
            term = Term::app(term, m.clone());
            ty = cod.instantiate(&m);
        }
        let ctx = self.local_ctx();
        if unify(self.env, &mut self.metas, &ctx, &ty, goal).is_err() {
            self.metas.restore(cp);
            return Ok(false);
        }
        if unify(self.env, &mut self.metas, &ctx, &Term::Meta(id), &term).is_err() {
            self.metas.restore(cp);
            return Ok(false);
        }
        Ok(true)
    }
}

use std::sync::OnceLock;
static EMPTY_IMPLICITS: OnceLock<Implicits> = OnceLock::new();
static EMPTY_INSTANCES: OnceLock<HashMap<String, Vec<String>>> = OnceLock::new();

/// A member of a recursive-function bundle (one per mutual-inductive-group member).
pub struct BundleMember {
    pub def_name: String,
    pub scrut_name: String,
    pub scrut_ty: Expr,
    pub ret: Expr,
    pub arms: Vec<crate::surface::MatchArm>,
}

/// How a recursive function recurses: the parameter position it matches on, and its
/// parameter names (so non-recursive arguments can be checked to be passed unchanged).
pub type RecInfo = HashMap<String, (usize, Vec<String>)>;

/// Rewrite **recursive calls by name** into induction hypotheses: a call `f(a₀, …, aₙ)`
/// to a function `f` in the recursion group, whose recursion argument `aₛ` is a bound
/// variable and whose other arguments are the function's own parameters unchanged,
/// becomes `aₛ.rec` (the IH `match` binds for that field). This is the structural-
/// recursion discipline; non-structural calls are left as-is (and fail to elaborate,
/// which is the honest signal that the recursion isn't structural).
pub fn rewrite_rec_calls(e: &Expr, recs: &RecInfo) -> Expr {
    // Span wrappers are transparent to the rewrite (and dropped in the rewritten body).
    let e = e.peel();
    match e {
        Expr::App(..) => {
            let (head, args) = unfold_surface_apps(e);
            if let Expr::Var(g, None) = head {
                if let Some((spos, params)) = recs.get(g) {
                    // Allow over-application: a recursive call may be *partial* in the
                    // function's parameters and then applied further (e.g. an induction
                    // hypothesis that is itself a function, `f(a)(proof)`). Match the first
                    // `params.len()` arguments against the recursion pattern, rewrite that
                    // prefix to the IH `field.rec`, and re-apply any remaining arguments.
                    if args.len() >= params.len() && *spos < params.len() {
                        if let Expr::Var(field, None) = args[*spos] {
                            let others_ok = (0..params.len()).all(|i| {
                                i == *spos
                                    || matches!(&args[i], Expr::Var(n, None) if n == &params[i])
                            });
                            if others_ok {
                                let mut t = Expr::Var(format!("{field}.rec"), None);
                                for a in &args[params.len()..] {
                                    t = Expr::App(Box::new(t), Box::new(rewrite_rec_calls(a, recs)));
                                }
                                return t;
                            }
                        }
                    }
                }
            }
            let mut t = rewrite_rec_calls(head, recs);
            for a in &args {
                t = Expr::App(Box::new(t), Box::new(rewrite_rec_calls(a, recs)));
            }
            t
        }
        Expr::Match(scrut, arms) => Expr::Match(
            Box::new(rewrite_rec_calls(scrut, recs)),
            arms.iter()
                .map(|a| crate::surface::MatchArm {
                    pat: a.pat.clone(),
                    body: rewrite_rec_calls(&a.body, recs),
                })
                .collect(),
        ),
        Expr::Lam(b, body) => Expr::Lam(b.clone(), Box::new(rewrite_rec_calls(body, recs))),
        Expr::Pi(b, body) => Expr::Pi(b.clone(), Box::new(rewrite_rec_calls(body, recs))),
        Expr::Arrow(a, b) => {
            Expr::Arrow(Box::new(rewrite_rec_calls(a, recs)), Box::new(rewrite_rec_calls(b, recs)))
        }
        Expr::Let(n, ty, v, b) => Expr::Let(
            n.clone(),
            ty.clone(),
            Box::new(rewrite_rec_calls(v, recs)),
            Box::new(rewrite_rec_calls(b, recs)),
        ),
        Expr::EqOp(a, b) => {
            Expr::EqOp(Box::new(rewrite_rec_calls(a, recs)), Box::new(rewrite_rec_calls(b, recs)))
        }
        // Recurse through the tactic forms, so recursive calls used inside them (e.g. an IH
        // fed to `rewrite`) are still rewritten to the `.rec` hypothesis.
        Expr::Rewrite(h, body) => Expr::Rewrite(
            Box::new(rewrite_rec_calls(h, recs)),
            Box::new(rewrite_rec_calls(body, recs)),
        ),
        Expr::ByCases(s, t, f) => Expr::ByCases(
            Box::new(rewrite_rec_calls(s, recs)),
            Box::new(rewrite_rec_calls(t, recs)),
            Box::new(rewrite_rec_calls(f, recs)),
        ),
        _ => e.clone(),
    }
}

/// Substitute the surface variable `name` by `repl` throughout `e`, stopping under any
/// binder that re-binds `name` (λ/Π/let and `match` patterns). Used by the pattern
/// Abstract every syntactic occurrence of `target` in `e` into the bound variable of a
/// fresh (outermost) binder: returns the body `M` such that `M[Var(0) := target] = e`. Used
/// to build the `Eq.subst` motive for `rewrite`. `k` counts binders descended past the new
/// one (start at 0); ambient free variables shift up by one to make room for it.
fn abstract_occurrences(e: &Term, target: &Term, k: usize) -> Term {
    if *e == target.lift(k as isize, 0) {
        return Term::Var(k);
    }
    match e {
        Term::Var(i) => {
            if *i >= k {
                Term::Var(i + 1)
            } else {
                Term::Var(*i)
            }
        }
        Term::Sort(_) | Term::Const(..) | Term::Meta(_) => e.clone(),
        Term::App(f, a) => {
            Term::app(abstract_occurrences(f, target, k), abstract_occurrences(a, target, k))
        }
        Term::Lam(d, b) => Term::lam(
            abstract_occurrences(d, target, k),
            abstract_occurrences(b, target, k + 1),
        ),
        Term::Pi(g, d, b) => Term::pi_graded(
            *g,
            abstract_occurrences(d, target, k),
            abstract_occurrences(b, target, k + 1),
        ),
        Term::Let(t, v, b) => Term::let_(
            abstract_occurrences(t, target, k),
            abstract_occurrences(v, target, k),
            abstract_occurrences(b, target, k + 1),
        ),
    }
}

/// compiler to bind a pattern variable to its scrutinee occurrence.
fn subst_var(e: &Expr, name: &str, repl: &Expr) -> Expr {
    use crate::surface::{Binder, MatchArm};
    let go = |x: &Expr| subst_var(x, name, repl);
    let bx = |x: &Expr| Box::new(subst_var(x, name, repl));
    match e {
        // Spans are transparent to substitution (dropped in the rewritten pattern body).
        Expr::Spanned(_, inner) => go(inner),
        Expr::Var(n, lv) if n == name && lv.is_none() => repl.clone(),
        // Keep the induction-hypothesis reference `<var>.rec` aligned when a pattern
        // variable is renamed to a fresh occurrence (so nested patterns compose with
        // name-recursion, which rewrote recursive calls to `<var>.rec` beforehand).
        Expr::Var(n, None)
            if matches!(repl, Expr::Var(_, None)) && *n == format!("{name}.rec") =>
        {
            let Expr::Var(r, _) = repl else { unreachable!() };
            Expr::Var(format!("{r}.rec"), None)
        }
        Expr::Var(..) | Expr::Type(_) | Expr::Prop | Expr::Sort(_) | Expr::Hole | Expr::Decide => {
            e.clone()
        }
        Expr::App(f, a) => Expr::App(bx(f), bx(a)),
        Expr::Rewrite(eq, body) => Expr::Rewrite(bx(eq), bx(body)),
        Expr::ByCases(s2, t, f) => Expr::ByCases(bx(s2), bx(t), bx(f)),
        Expr::EqOp(a, b) => Expr::EqOp(bx(a), bx(b)),
        Expr::Arrow(a, b) => Expr::Arrow(bx(a), bx(b)),
        Expr::Lam(b, body) => {
            let b2 = Binder { names: b.names.clone(), ty: go(&b.ty), implicit: b.implicit };
            let body = if b.names.iter().any(|n| n == name) { (**body).clone() } else { go(body) };
            Expr::Lam(Box::new(b2), Box::new(body))
        }
        Expr::Pi(b, body) => {
            let b2 = Binder { names: b.names.clone(), ty: go(&b.ty), implicit: b.implicit };
            let body = if b.names.iter().any(|n| n == name) { (**body).clone() } else { go(body) };
            Expr::Pi(Box::new(b2), Box::new(body))
        }
        Expr::Let(n, ty, val, body) => {
            let ty2 = ty.as_ref().map(|t| Box::new(go(t)));
            let body = if n == name { (**body).clone() } else { go(body) };
            Expr::Let(n.clone(), ty2, bx(val), Box::new(body))
        }
        Expr::Match(scrut, arms) => Expr::Match(
            bx(scrut),
            arms.iter()
                .map(|a| {
                    let body = if pattern_binds(&a.pat, name) { a.body.clone() } else { go(&a.body) };
                    MatchArm { pat: a.pat.clone(), body }
                })
                .collect(),
        ),
    }
}

/// Does pattern `p` bind the variable `name`?
fn pattern_binds(p: &crate::surface::Pattern, name: &str) -> bool {
    match p {
        crate::surface::Pattern::Var(v) => v == name,
        crate::surface::Pattern::Ctor(_, subs) => subs.iter().any(|s| pattern_binds(s, name)),
    }
}

/// Peel exactly `n` leading `Π`s, returning the remaining body (domains discarded).
fn peel_pis(mut t: Term, n: usize) -> Option<((), Term)> {
    for _ in 0..n {
        match t {
            Term::Pi(_, _, b) => t = (*b).clone(),
            _ => return None,
        }
    }
    Some(((), t))
}

/// Peel all leading `Π`s, returning their domains and the final body.
fn peel_all_pis(mut t: Term) -> (Vec<Term>, Term) {
    let mut doms = Vec::new();
    while let Term::Pi(_, d, b) = t {
        doms.push((*d).clone());
        t = (*b).clone();
    }
    (doms, t)
}

/// Replace every occurrence of `target` in `t` with the de Bruijn variable `k`,
/// descending under binders (so `target` and `k` both shift by one each time). Used to
/// build a `match` motive by abstracting the scrutinee out of the result type (and, by
/// the prover, to abstract a rewritten subterm out of a goal): at the top, `target` is
/// the term being abstracted and `k` is the new binder.
pub(crate) fn replace_with_var(t: &Term, target: &Term, k: usize) -> Term {
    // `target` is given in the term's *top* context; `k` is the de Bruijn index the
    // abstracted binder has there. Going under `depth` binders, the occurrence to match is
    // `target` lifted by `depth` (NOT by `k`), and it is replaced by `Var(k + depth)`.
    // (Folding the match-lift into `k` only happens to be correct when `k == 0`, e.g. for
    // the scrutinee; an index abstraction has `k > 0` and needs the two kept separate.)
    fn go(t: &Term, target: &Term, k: usize, depth: usize) -> Term {
        if *t == target.lift(depth as isize, 0) {
            return Term::Var(k + depth);
        }
        match t {
            Term::Sort(_) | Term::Var(_) | Term::Const(..) | Term::Meta(_) => t.clone(),
            Term::App(f, a) => Term::app(go(f, target, k, depth), go(a, target, k, depth)),
            Term::Lam(d, b) => Term::lam(go(d, target, k, depth), go(b, target, k, depth + 1)),
            Term::Pi(g, d, b) => {
                Term::pi_graded(*g, go(d, target, k, depth), go(b, target, k, depth + 1))
            }
            Term::Let(ty, v, b) => Term::let_(
                go(ty, target, k, depth),
                go(v, target, k, depth),
                go(b, target, k, depth + 1),
            ),
        }
    }
    go(t, target, k, 0)
}

/// Does the constant `n` occur anywhere in `t`? (Used to spot recursive fields.)
fn occurs_const(n: &str, t: &Term) -> bool {
    match t {
        Term::Const(m, _) => &**m == n,
        Term::App(f, a) => occurs_const(n, f) || occurs_const(n, a),
        Term::Lam(d, b) | Term::Pi(_, d, b) => occurs_const(n, d) || occurs_const(n, b),
        Term::Let(x, y, z) => occurs_const(n, x) || occurs_const(n, y) || occurs_const(n, z),
        Term::Sort(_) | Term::Var(_) | Term::Meta(_) => false,
    }
}

/// Collect a curried surface application `((h a) b) …` into `(head, [a, b, …])`. Span
/// wrappers are peeled at every level, so the returned head and args are span-free and the
/// callers' structural matches (e.g. recursion-pattern checks) see the bare shapes.
fn unfold_surface_apps(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut head = e.peel();
    while let Expr::App(f, a) = head {
        args.push(a.peel());
        head = f.peel();
    }
    args.reverse();
    (head, args)
}

/// Parse-free convenience: infer and zonk a surface expression.
pub fn elaborate_infer(env: &Env, e: &Expr) -> Result<Term, String> {
    let mut inf = Infer::new(env);
    let (t, _) = inf.infer(e)?;
    inf.finish(&t)
}

/// Elaborate `e` checked against `expected`, then zonk.
pub fn elaborate_check(env: &Env, e: &Expr, expected: &Term) -> Result<Term, String> {
    let mut inf = Infer::new(env);
    let t = inf.check(e, expected)?;
    inf.finish(&t)
}

/// Flatten a parameter telescope to its implicit mask (one `bool` per binder name).
pub fn params_mask(params: &[crate::surface::Binder]) -> Vec<bool> {
    params.iter().flat_map(|b| vec![b.implicit; b.names.len()]).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Kernel;
    use crate::surface::parse_expr;

    fn nat_kernel() -> Kernel {
        let mut k = Kernel::new();
        k.declare_inductive(crate::generate::nat_spec()).unwrap();
        // id : (A : Type) -> A -> A := fun A x. x
        k.add_definition(
            "id",
            0,
            Term::pi(Term::typ(0), Term::pi(Term::Var(0), Term::Var(1))),
            Term::lam(Term::typ(0), Term::lam(Term::Var(0), Term::Var(0))),
        )
        .unwrap();
        k.add_axiom("n", 0, Term::cnst(name("Nat"), vec![])).unwrap();
        k
    }

    /// The keystone: a hole for the type argument is **inferred** from the value
    /// argument. `id(_, n)` elaborates to `id Nat n`.
    #[test]
    fn infers_type_argument_from_hole() {
        let k = nat_kernel();
        let e = parse_expr("id(_, n)").unwrap();
        let t = elaborate_infer(k.env(), &e).unwrap();
        let expected = Term::apps(Term::cnst(name("id"), vec![]), [
            Term::cnst(name("Nat"), vec![]),
            Term::cnst(name("n"), vec![]),
        ]);
        assert_eq!(t, expected, "the hole should be solved to Nat");
        k.check(&t, &Term::cnst(name("Nat"), vec![])).unwrap();
    }

    /// An un-inferable hole is reported, not silently accepted.
    #[test]
    fn unsolvable_hole_errors() {
        let k = nat_kernel();
        let e = parse_expr("id(_, _)").unwrap();
        assert!(elaborate_infer(k.env(), &e).is_err());
    }

    /// `==` infers its type argument: `n == n` ⇒ `Eq.{1} Nat n n`.
    #[test]
    fn eq_infers_type() {
        let k = nat_kernel();
        let e = parse_expr("n == n").unwrap();
        let t = elaborate_infer(k.env(), &e).unwrap();
        let expected = Term::apps(
            Term::cnst(name("Eq"), vec![Level::of_nat(1)]),
            [Term::cnst(name("Nat"), vec![]), Term::cnst(name("n"), vec![]), Term::cnst(name("n"), vec![])],
        );
        assert_eq!(t, expected);
    }

    /// With `id`'s type argument declared **implicit**, the user writes `id(n)` and the
    /// elaborator auto-inserts the hole for `A`.
    #[test]
    fn implicit_argument_is_auto_inserted() {
        let k = nat_kernel();
        let mut implicits = Implicits::new();
        implicits.insert("id".to_string(), vec![true, false]); // {A} (x)
        let e = parse_expr("id(n)").unwrap();
        let t = {
            let mut inf = Infer::with_implicits(k.env(), &implicits);
            let (t, _) = inf.infer(&e).unwrap();
            inf.finish(&t).unwrap()
        };
        let expected = Term::apps(Term::cnst(name("id"), vec![]), [
            Term::cnst(name("Nat"), vec![]),
            Term::cnst(name("n"), vec![]),
        ]);
        assert_eq!(t, expected, "the implicit A should be auto-inserted and solved to Nat");
        k.check(&t, &Term::cnst(name("Nat"), vec![])).unwrap();
    }
}
