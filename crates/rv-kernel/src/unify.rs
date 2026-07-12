//! Metavariables and (first-order) unification — the engine under elaboration.
//!
//! A [`Metas`] context holds the solutions of [`Term::Meta`] holes. [`unify`] makes two
//! terms definitionally equal by *solving* metas: it normalizes both (with the
//! metacontext, so already-solved holes unfold), then compares structurally; when one
//! side is an unsolved metavariable it is solved to the other (after an occurs check).
//! [`Metas::zonk`] then replaces every solved hole, producing a metavariable-free term
//! fit for the trusted kernel.
//!
//! Scope: first-order unification of term/type metavariables (enough for implicit
//! arguments and type inference from explicit arguments and the expected type), plus
//! **universe-level** metavariables and **higher-order pattern unification** (Miller
//! patterns: a metavariable applied to distinct bound variables, `?m x y =?= rhs`).
//! Non-pattern higher-order problems are undecidable in general and are reported rather
//! than guessed.

use rv_kernel_core::check::{Checker, LocalCtx};
use rv_kernel_core::env::Env;
use rv_kernel_core::level::{self, Level};
use rv_kernel_core::nbe::Nbe;
use rv_kernel_core::term::Term;

/// A metavariable context: solutions for term metas *and* universe-level metas, each
/// indexed by id. Term metas and level metas live in separate id spaces (they are
/// different syntactic categories — [`Term::Meta`] vs [`Level::Meta`]).
#[derive(Default)]
pub struct Metas {
    solutions: Vec<Option<Term>>,
    /// Optional `(creation_depth, expected_type)` for each term meta. When a typed meta
    /// is solved, its expected type is unified with the solution's inferred type — this
    /// is what lets a universe-level meta get solved from the *value* a type-hole takes
    /// (e.g. solving `?A := Nat` then `Sort ?u =?= Type 0` ⇒ `?u := 1`).
    types: Vec<Option<(usize, Term)>>,
    level_solutions: Vec<Option<Level>>,
    /// Monotonic counter bumped on every solve (term or level). Lets the structural
    /// unifier skip re-normalizing a subterm that is still valid because nothing was
    /// solved since it was normalized — turning the per-node re-normalization (an O(N²)
    /// blowup on large terms) into a single normalize plus a structural walk.
    generation: u64,
}

/// A saved metacontext, for speculative solving (see [`Metas::checkpoint`]).
#[derive(Clone)]
pub struct MetasCheckpoint {
    solutions: Vec<Option<Term>>,
    types: Vec<Option<(usize, Term)>>,
    level_solutions: Vec<Option<Level>>,
    generation: u64,
}

impl Metas {
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a fresh, unsolved, untyped term metavariable.
    pub fn fresh(&mut self) -> Term {
        let id = self.solutions.len() as u32;
        self.solutions.push(None);
        self.types.push(None);
        Term::Meta(id)
    }

    /// Allocate a fresh term metavariable carrying its expected type (at binder depth
    /// `depth`), so solving it can propagate to the type — including universe levels.
    pub fn fresh_typed(&mut self, depth: usize, ty: Term) -> Term {
        let id = self.solutions.len() as u32;
        self.solutions.push(None);
        self.types.push(Some((depth, ty)));
        Term::Meta(id)
    }

    fn meta_type(&self, m: u32) -> Option<(usize, Term)> {
        self.types.get(m as usize).cloned().flatten()
    }

    /// Allocate a fresh, unsolved **universe-level** metavariable.
    pub fn fresh_level(&mut self) -> Level {
        let id = self.level_solutions.len() as u32;
        self.level_solutions.push(None);
        Level::Meta(id)
    }

    pub fn is_solved(&self, m: u32) -> bool {
        self.solutions.get(m as usize).is_some_and(|s| s.is_some())
    }

    /// The raw term-solution table, for building a meta-aware reducer.
    pub fn solutions(&self) -> &[Option<Term>] {
        &self.solutions
    }

    /// Every still-unsolved metavariable that carries an expected type, as
    /// `(id, creation_depth, type)`. Used by instance resolution to find the class-typed
    /// holes it must fill.
    pub fn unsolved_typed(&self) -> Vec<(u32, usize, Term)> {
        self.types
            .iter()
            .enumerate()
            .filter(|(i, _)| self.solutions[*i].is_none())
            .filter_map(|(i, slot)| slot.as_ref().map(|(d, ty)| (i as u32, *d, ty.clone())))
            .collect()
    }

    /// Snapshot the whole metacontext, so a speculative solve (e.g. trying a candidate
    /// instance) can be rolled back with [`Self::restore`] if it doesn't pan out.
    pub fn checkpoint(&self) -> MetasCheckpoint {
        MetasCheckpoint {
            solutions: self.solutions.clone(),
            types: self.types.clone(),
            level_solutions: self.level_solutions.clone(),
            generation: self.generation,
        }
    }

    /// Restore a snapshot taken by [`Self::checkpoint`].
    pub fn restore(&mut self, cp: MetasCheckpoint) {
        self.solutions = cp.solutions;
        self.types = cp.types;
        self.level_solutions = cp.level_solutions;
        self.generation = cp.generation;
    }

    /// The current solve generation. Equal across two points iff no meta was solved
    /// between them, so a term normalized at the earlier point is still in normal form.
    fn generation(&self) -> u64 {
        self.generation
    }

    fn solve_raw(&mut self, m: u32, t: Term) {
        self.solutions[m as usize] = Some(t);
        self.generation += 1;
    }

    fn level_sol(&self, m: u32) -> Option<&Level> {
        self.level_solutions.get(m as usize).and_then(|s| s.as_ref())
    }

    fn solve_level_raw(&mut self, m: u32, l: Level) {
        self.level_solutions[m as usize] = Some(l);
        self.generation += 1;
    }

    /// Substitute solved level metas in `l` (recursively), leaving unsolved ones.
    fn resolve_level(&self, l: &Level) -> Level {
        match l {
            Level::Meta(m) => match self.level_sol(*m) {
                Some(sol) => self.resolve_level(sol),
                None => l.clone(),
            },
            Level::Zero | Level::Param(_) => l.clone(),
            Level::Succ(a) => Level::succ(self.resolve_level(a)),
            Level::Max(a, b) => Level::max(self.resolve_level(a), self.resolve_level(b)),
            Level::IMax(a, b) => Level::imax(self.resolve_level(a), self.resolve_level(b)),
        }
    }

    /// Zonk a level: substitute solved metas, error on an unsolved one.
    fn zonk_level(&self, l: &Level) -> Result<Level, String> {
        let r = self.resolve_level(l);
        if r.has_meta() {
            return Err("could not infer a universe level (unsolved level metavariable)".to_string());
        }
        Ok(r)
    }

    /// Replace every solved metavariable in `t` by its solution (recursively) — term
    /// metas *and* the level metas inside `Sort`/`Const` — erroring if an unsolved one
    /// remains. The result is metavariable-free.
    pub fn zonk(&self, t: &Term) -> Result<Term, String> {
        match t {
            Term::Meta(m) => match self.solutions.get(*m as usize).and_then(|s| s.as_ref()) {
                Some(sol) => self.zonk(sol),
                None => Err(format!("could not infer metavariable ?{m}")),
            },
            Term::Var(_) | Term::I | Term::IZero | Term::IOne => Ok(t.clone()),
            Term::Sort(l) => Ok(Term::Sort(self.zonk_level(l)?)),
            Term::Const(n, ls) => {
                let ls = ls.iter().map(|l| self.zonk_level(l)).collect::<Result<_, _>>()?;
                Ok(Term::cnst(n.clone(), ls))
            }
            Term::App(f, a) => Ok(Term::app(self.zonk(f)?, self.zonk(a)?)),
            Term::Lam(d, b) => Ok(Term::lam(self.zonk(d)?, self.zonk(b)?)),
            Term::Pi(g, d, b) => Ok(Term::pi_graded(*g, self.zonk(d)?, self.zonk(b)?)),
            Term::INeg(r) => Ok(Term::ineg(self.zonk(r)?)),
            Term::IMeet(r, s) => Ok(Term::imeet(self.zonk(r)?, self.zonk(s)?)),
            Term::IJoin(r, s) => Ok(Term::ijoin(self.zonk(r)?, self.zonk(s)?)),
            Term::PLam(b) => Ok(Term::plam(self.zonk(b)?)),
            Term::PApp(p, r) => Ok(Term::papp(self.zonk(p)?, self.zonk(r)?)),
            Term::PathP(fam, a0, a1) => {
                Ok(Term::pathp(self.zonk(fam)?, self.zonk(a0)?, self.zonk(a1)?))
            }
            Term::Let(g, ty, v, b) => {
                Ok(Term::let_graded(*g, self.zonk(ty)?, self.zonk(v)?, self.zonk(b)?))
            }
            Term::Sys(branches) => {
                let branches = branches
                    .iter()
                    .map(|(p, t)| Ok((std::rc::Rc::new(self.zonk_cof(p)?), std::rc::Rc::new(self.zonk(t)?))))
                    .collect::<Result<_, String>>()?;
                Ok(Term::Sys(branches))
            }
            Term::Partial(p, a) => {
                Ok(Term::Partial(std::rc::Rc::new(self.zonk_cof(p)?), std::rc::Rc::new(self.zonk(a)?)))
            }
            Term::Transp(fam, p, a) => {
                Ok(Term::transp(self.zonk(fam)?, self.zonk_cof(p)?, self.zonk(a)?))
            }
            Term::HComp(ty, p, u, u0) => {
                Ok(Term::hcomp(self.zonk(ty)?, self.zonk_cof(p)?, self.zonk(u)?, self.zonk(u0)?))
            }
            Term::Glue(a, p, t, e) => Ok(Term::glue_ty(
                self.zonk(a)?,
                self.zonk_cof(p)?,
                self.zonk(t)?,
                self.zonk(e)?,
            )),
        }
    }

    /// [`Self::zonk`]'s analogue for a cofibration's atom subjects.
    fn zonk_cof(&self, phi: &rv_kernel_core::face::Cof) -> Result<rv_kernel_core::face::Cof, String> {
        use rv_kernel_core::face::{Atom, Cof};
        match phi {
            Cof::Bot => Ok(Cof::Bot),
            Cof::Top => Ok(Cof::Top),
            Cof::Atom(Atom::Eq0(t)) => Ok(Cof::eq0(self.zonk(t)?)),
            Cof::Atom(Atom::Eq1(t)) => Ok(Cof::eq1(self.zonk(t)?)),
            Cof::And(a, b) => Ok(Cof::and(self.zonk_cof(a)?, self.zonk_cof(b)?)),
            Cof::Or(a, b) => Ok(Cof::or(self.zonk_cof(a)?, self.zonk_cof(b)?)),
        }
    }
}

/// Unify two universe levels, solving level metavariables. First-order: solves a bare
/// `Meta` against the other side; recurses through `Succ`; otherwise falls back to the
/// sound `equiv`. Enough for `Sort ?u =?= Sort 1` and matching a polymorphic constant's
/// inferred levels against the expected ones.
fn unify_level(metas: &mut Metas, l1: &Level, l2: &Level) -> Result<(), String> {
    let a = metas.resolve_level(l1);
    let b = metas.resolve_level(l2);
    if a == b {
        return Ok(());
    }
    match (&a, &b) {
        (Level::Meta(m), _) => {
            if level_occurs(*m, &b) {
                return Err(format!("occurs check: level ?{m} would be cyclic"));
            }
            metas.solve_level_raw(*m, b);
            Ok(())
        }
        (_, Level::Meta(m)) => {
            if level_occurs(*m, &a) {
                return Err(format!("occurs check: level ?{m} would be cyclic"));
            }
            metas.solve_level_raw(*m, a);
            Ok(())
        }
        (Level::Succ(x), Level::Succ(y)) => unify_level(metas, x, y),
        _ => {
            if level::equiv(&a, &b) {
                Ok(())
            } else {
                Err("universe mismatch".to_string())
            }
        }
    }
}

fn level_occurs(m: u32, l: &Level) -> bool {
    match l {
        Level::Meta(k) => *k == m,
        Level::Zero | Level::Param(_) => false,
        Level::Succ(a) => level_occurs(m, a),
        Level::Max(a, b) | Level::IMax(a, b) => level_occurs(m, a) || level_occurs(m, b),
    }
}

/// Unify `t1` and `t2` in the typing context `ctx`, solving metavariables. The context
/// carries the local binder *types* (not just a depth) so that solving a typed meta can
/// infer the solution's type and propagate it (see [`Metas::fresh_typed`]).
pub fn unify(
    env: &Env,
    metas: &mut Metas,
    ctx: &LocalCtx,
    t1: &Term,
    t2: &Term,
) -> Result<(), String> {
    let depth = ctx.len();
    let (a, b) = {
        let nbe = Nbe::with_metas(env, &metas.solutions);
        (nbe.normalize_open(depth, t1), nbe.normalize_open(depth, t2))
    };
    unify_nf(env, metas, ctx, &a, &b)
}

/// Unify two terms that are **in normal form w.r.t. the metacontext as of generation
/// `gen0`**. Recurses into sibling subterms via [`unify_child`], which re-normalizes a
/// sibling only when a meta has been solved since `gen0` (and so an embedded solved meta
/// could now unfold); otherwise it stays structural. This avoids re-normalizing every
/// subterm at every node — the O(N²) blowup on large reflected proofs.
fn unify_nf(
    env: &Env,
    metas: &mut Metas,
    ctx: &LocalCtx,
    a: &Term,
    b: &Term,
) -> Result<(), String> {
    if a == b {
        return Ok(());
    }
    let gen0 = metas.generation();
    // Flex sides first: a metavariable head, possibly applied to a spine. A bare meta is
    // a first-order solve; a meta applied to a spine is **higher-order**, handled by
    // Miller pattern unification when the spine is a list of distinct bound variables.
    let (ha, spa) = a.unfold_apps();
    if let Term::Meta(m) = ha {
        return if spa.is_empty() {
            solve(env, metas, ctx, m, b)
        } else {
            solve_pattern(metas, m, &spa, b, ctx)
        };
    }
    let (hb, spb) = b.unfold_apps();
    if let Term::Meta(m) = hb {
        return if spb.is_empty() {
            solve(env, metas, ctx, m, a)
        } else {
            solve_pattern(metas, m, &spb, a, ctx)
        };
    }
    match (a, b) {
        (Term::Sort(l1), Term::Sort(l2)) => unify_level(metas, l1, l2),
        (Term::Var(i), Term::Var(j)) if i == j => Ok(()),
        (Term::Const(n1, l1), Term::Const(n2, l2)) => {
            if n1 != n2 || l1.len() != l2.len() {
                return Err(format!("cannot unify '{n1}' with '{n2}'"));
            }
            for (x, y) in l1.iter().zip(l2) {
                unify_level(metas, x, y)?;
            }
            Ok(())
        }
        (Term::Pi(_, d1, b1), Term::Pi(_, d2, b2))
        | (Term::Lam(d1, b1), Term::Lam(d2, b2)) => {
            unify_child(env, metas, ctx, d1, d2, gen0)?;
            let mut c2 = ctx.clone();
            c2.push((**d1).clone());
            unify_child(env, metas, &c2, b1, b2, gen0)
        }
        // The cubical layer: `PathP`'s family lives under one extra (interval)
        // binder — exactly like `Pi`/`Lam`'s codomain/body — so it recurses the
        // same way, plus the two (binder-free) endpoints. `PLam`'s body likewise
        // lives under one extra interval binder. `I` itself has no checkable
        // members other than the two literal endpoints/a bound variable (see
        // `rv_kernel_core::check::Checker::infer`'s `Term::I` arm), so pushing it
        // as a "domain" here (mirroring `Pi`/`Lam`) is just bookkeeping — nothing
        // ever asks for its sort.
        (Term::PathP(f1, a01, a11), Term::PathP(f2, a02, a12)) => {
            let mut c2 = ctx.clone();
            c2.push(rv_kernel_core::term::Term::I);
            unify_child(env, metas, &c2, f1, f2, gen0)?;
            unify_child(env, metas, ctx, a01, a02, gen0)?;
            unify_child(env, metas, ctx, a11, a12, gen0)
        }
        (Term::PLam(b1), Term::PLam(b2)) => {
            let mut c2 = ctx.clone();
            c2.push(rv_kernel_core::term::Term::I);
            unify_child(env, metas, &c2, b1, b2, gen0)
        }
        (Term::PApp(p1, r1), Term::PApp(p2, r2)) => {
            unify_child(env, metas, ctx, p1, p2, gen0)?;
            unify_child(env, metas, ctx, r1, r2, gen0)
        }
        // Interval expressions: compared up to the De Morgan algebra laws (the
        // same routing point `rv_kernel_core::check::Checker::compare`/
        // `rv_kernel_core::reduce::Reducer::is_def_eq` use), not structurally —
        // `i_meet(r,s)` and `i_meet(s,r)` are the same interval point, for
        // instance. None of these ever contain a metavariable in a well-typed
        // term (an interval expression's only free variables are bound interval
        // variables), so this is a plain equality check, no `Metas` solving.
        (Term::I, Term::I) => Ok(()),
        (Term::IZero, Term::IZero) | (Term::IOne, Term::IOne) => Ok(()),
        (a, b) if rv_kernel_core::cubical::is_interval_expr(a) && rv_kernel_core::cubical::is_interval_expr(b) => {
            if rv_kernel_core::cubical::interval_eq(a, b) {
                Ok(())
            } else {
                Err(format!("cannot unify interval expressions\n  {}\nwith\n  {}", a.pretty(), b.pretty()))
            }
        }
        (Term::App(..), Term::App(..)) => {
            // Both heads are now rigid (flex heads were intercepted above).
            let (h1, a1) = a.unfold_apps();
            let (h2, a2) = b.unfold_apps();
            if a1.len() != a2.len() {
                // Distinct application spines — usually two genuinely different terms (e.g.
                // a mis-oriented rewrite), not an "arity" problem per se. Show both.
                return Err(format!(
                    "cannot unify these terms (different application spines):\n  {}\nwith\n  {}",
                    a.pretty(),
                    b.pretty()
                ));
            }
            unify_child(env, metas, ctx, &h1, &h2, gen0)?;
            for (x, y) in a1.iter().zip(&a2) {
                unify_child(env, metas, ctx, x, y, gen0)?;
            }
            Ok(())
        }
        _ => Err(format!("cannot unify\n  {}\nwith\n  {}", a.pretty(), b.pretty())),
    }
}

/// Unify two subterms that were normal as of generation `gen0`. If nothing has been
/// solved since (`generation == gen0`) they are still normal, so compare structurally
/// with [`unify_nf`]; otherwise a freshly-solved meta may lurk inside, so go through
/// [`unify`] to re-normalize first.
fn unify_child(
    env: &Env,
    metas: &mut Metas,
    ctx: &LocalCtx,
    a: &Term,
    b: &Term,
    gen0: u64,
) -> Result<(), String> {
    if metas.generation() == gen0 {
        unify_nf(env, metas, ctx, a, b)
    } else {
        unify(env, metas, ctx, a, b)
    }
}

/// **Miller pattern unification.** Solve a flex-rigid problem `?m s₀ … sₙ₋₁ =?= rhs`
/// where the spine `s` is a *pattern*: each `sᵢ` is a distinct bound variable. The unique
/// solution is `?m := λ x₀ … xₙ₋₁. rhs[sᵢ ↦ xᵢ]`, which exists iff
/// * `rhs` does not contain `?m` (occurs check), and
/// * every free (context) variable of `rhs` is among the pattern variables (scope check).
///
/// When those hold the solution is a **closed** term — exactly what our verbatim-
/// substitution [`Metas::zonk`] requires. Non-pattern spines (a non-variable argument, or
/// a repeated variable) are outside the decidable fragment and reported, not guessed.
fn solve_pattern(
    metas: &mut Metas,
    m: u32,
    spine: &[Term],
    rhs: &Term,
    ctx: &LocalCtx,
) -> Result<(), String> {
    // Pattern check: the spine must be distinct bound variables.
    let mut image = Vec::with_capacity(spine.len());
    for arg in spine {
        match arg {
            Term::Var(i) if !image.contains(i) => image.push(*i),
            Term::Var(_) => {
                return Err("higher-order unification: non-linear pattern (a metavariable \
                            argument repeats)"
                    .to_string())
            }
            _ => {
                return Err("higher-order unification: metavariable applied to a non-variable \
                            (outside the decidable pattern fragment)"
                    .to_string())
            }
        }
    }
    let n = image.len();
    // Body: invert `rhs` so each pattern variable becomes the corresponding λ-binder.
    let body = invert(m, &image, rhs, 0)?;
    // Domains: the type of each pattern variable, inverted over the *earlier* pattern
    // variables (a dependent telescope `Π x₀ … . `).
    let mut doms = Vec::with_capacity(n);
    for i in 0..n {
        let vty = ctx
            .var_type(image[i])
            .ok_or("higher-order unification: a pattern variable is out of scope")?;
        doms.push(invert(m, &image[..i], &vty, 0)?);
    }
    // Wrap: λ x₀ … xₙ₋₁. body  (outermost binder is x₀ / position 0).
    let mut sol = body;
    for d in doms.into_iter().rev() {
        sol = Term::lam(d, sol);
    }
    metas.solve_raw(m, sol);
    Ok(())
}

/// Invert a substitution for pattern unification: rewrite `t` (living in the unification
/// context at inner binder-depth `depth`) into the body of the solution `λ x₀…xₙ₋₁. _`,
/// where pattern variable `image[i]` (a context de Bruijn index) maps to binder `xᵢ`.
/// Fails on an occurrence of `?meta` (occurs check) or a context variable not in `image`
/// (escape/scope check).
fn invert(meta: u32, image: &[usize], t: &Term, depth: usize) -> Result<Term, String> {
    let n = image.len();
    match t {
        Term::Meta(k) => {
            if *k == meta {
                Err(format!("higher-order unification: occurs check (?{meta} is cyclic)"))
            } else {
                Ok(t.clone())
            }
        }
        Term::Var(j) => {
            if *j < depth {
                Ok(Term::Var(*j)) // bound by a binder inside `rhs`
            } else {
                let ctx_idx = *j - depth;
                match image.iter().position(|&b| b == ctx_idx) {
                    // Pattern variable i ⇒ λ-binder xᵢ, at de Bruijn index (n-1-i) shifted
                    // under the `depth` inner binders.
                    Some(i) => Ok(Term::Var((n - 1 - i) + depth)),
                    None => Err("higher-order unification: a variable escapes the \
                                 metavariable's scope (no pattern solution)"
                        .to_string()),
                }
            }
        }
        Term::Sort(_) | Term::Const(..) | Term::I | Term::IZero | Term::IOne => Ok(t.clone()),
        Term::App(f, a) => Ok(Term::app(invert(meta, image, f, depth)?, invert(meta, image, a, depth)?)),
        Term::Lam(d, b) => {
            Ok(Term::lam(invert(meta, image, d, depth)?, invert(meta, image, b, depth + 1)?))
        }
        Term::Pi(g, d, b) => Ok(Term::pi_graded(
            *g,
            invert(meta, image, d, depth)?,
            invert(meta, image, b, depth + 1)?,
        )),
        Term::Let(g, ty, v, b) => Ok(Term::let_graded(
            *g,
            invert(meta, image, ty, depth)?,
            invert(meta, image, v, depth)?,
            invert(meta, image, b, depth + 1)?,
        )),
        Term::INeg(r) => Ok(Term::ineg(invert(meta, image, r, depth)?)),
        Term::IMeet(r, s) => {
            Ok(Term::imeet(invert(meta, image, r, depth)?, invert(meta, image, s, depth)?))
        }
        Term::IJoin(r, s) => {
            Ok(Term::ijoin(invert(meta, image, r, depth)?, invert(meta, image, s, depth)?))
        }
        Term::PLam(b) => Ok(Term::plam(invert(meta, image, b, depth + 1)?)),
        Term::PApp(p, r) => {
            Ok(Term::papp(invert(meta, image, p, depth)?, invert(meta, image, r, depth)?))
        }
        Term::PathP(fam, a0, a1) => Ok(Term::pathp(
            invert(meta, image, fam, depth + 1)?,
            invert(meta, image, a0, depth)?,
            invert(meta, image, a1, depth)?,
        )),
        // No surface syntax produces `Sys`/`Partial` yet (see
        // `rv_kernel_core::face`'s module doc); a cofibration atom's subject is
        // always `IZero`/`IOne`/a bound interval var in practice, so leaving `φ`
        // unchanged (rather than inverting its subjects too) is a conservative
        // placeholder pending that surface syntax.
        Term::Sys(branches) => Ok(Term::Sys(
            branches
                .iter()
                .map(|(p, t)| Ok((p.clone(), std::rc::Rc::new(invert(meta, image, t, depth)?))))
                .collect::<Result<_, String>>()?,
        )),
        Term::Partial(p, a) => {
            Ok(Term::Partial(p.clone(), std::rc::Rc::new(invert(meta, image, a, depth)?)))
        }
        Term::Transp(fam, p, a) => Ok(Term::transp(
            invert(meta, image, fam, depth + 1)?,
            (**p).clone(),
            invert(meta, image, a, depth)?,
        )),
        Term::HComp(ty, p, u, u0) => Ok(Term::hcomp(
            invert(meta, image, ty, depth)?,
            (**p).clone(),
            invert(meta, image, u, depth + 1)?,
            invert(meta, image, u0, depth)?,
        )),
        Term::Glue(a, p, t2, e) => Ok(Term::glue_ty(
            invert(meta, image, a, depth)?,
            (**p).clone(),
            invert(meta, image, t2, depth)?,
            invert(meta, image, e, depth)?,
        )),
    }
}

/// Solve `?m := t` after an occurs check, then propagate the meta's expected type to
/// the solution's inferred type (best effort — this is what lets a universe-level meta
/// be solved from the value a type-hole takes; any failure is ignored, since the kernel
/// re-checks the final zonked term).
fn solve(env: &Env, metas: &mut Metas, ctx: &LocalCtx, m: u32, t: &Term) -> Result<(), String> {
    if occurs(m, t) {
        return Err(format!("occurs check: ?{m} would be cyclic"));
    }
    metas.solve_raw(m, t.clone());
    if let Some((dm, tym)) = metas.meta_type(m) {
        if dm == ctx.len() && !t.has_meta() {
            if let Ok(tt) = Checker::new(env).infer(&mut ctx.clone(), t) {
                let _ = unify(env, metas, ctx, &tym, &tt);
            }
        }
    }
    Ok(())
}

/// Does metavariable `m` occur in `t`?
fn occurs(m: u32, t: &Term) -> bool {
    match t {
        Term::Meta(k) => *k == m,
        Term::Sort(_) | Term::Var(_) | Term::Const(..) | Term::I | Term::IZero | Term::IOne => false,
        Term::App(f, a) => occurs(m, f) || occurs(m, a),
        Term::Lam(d, b) | Term::Pi(_, d, b) => occurs(m, d) || occurs(m, b),
        Term::Let(_, ty, v, b) => occurs(m, ty) || occurs(m, v) || occurs(m, b),
        Term::INeg(r) => occurs(m, r),
        Term::IMeet(r, s) | Term::IJoin(r, s) => occurs(m, r) || occurs(m, s),
        Term::PLam(b) => occurs(m, b),
        Term::PApp(p, r) => occurs(m, p) || occurs(m, r),
        Term::PathP(fam, a0, a1) => occurs(m, fam) || occurs(m, a0) || occurs(m, a1),
        Term::Sys(branches) => branches.iter().any(|(_, t)| occurs(m, t)),
        Term::Partial(_, a) => occurs(m, a),
        Term::Transp(fam, _, a) => occurs(m, fam) || occurs(m, a),
        Term::HComp(ty, _, u, u0) => occurs(m, ty) || occurs(m, u) || occurs(m, u0),
        Term::Glue(a, _, t, e) => occurs(m, a) || occurs(m, t) || occurs(m, e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_kernel_core::term::name;

    fn c(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// A bare metavariable unifies with a term, and zonking substitutes it.
    #[test]
    fn solves_a_metavariable() {
        let env = Env::new();
        let mut metas = Metas::new();
        let m = metas.fresh();
        unify(&env, &mut metas, &LocalCtx::new(), &m, &c("Nat")).unwrap();
        assert_eq!(metas.zonk(&m).unwrap(), c("Nat"));
    }

    /// Unification looks *inside* applications to solve a meta from context.
    #[test]
    fn solves_under_application() {
        let env = Env::new();
        let mut metas = Metas::new();
        let m = metas.fresh();
        // f ?m  =?=  f Bool   ⇒   ?m := Bool
        let lhs = Term::app(c("f"), m.clone());
        let rhs = Term::app(c("f"), c("Bool"));
        unify(&env, &mut metas, &LocalCtx::new(), &lhs, &rhs).unwrap();
        assert_eq!(metas.zonk(&m).unwrap(), c("Bool"));
    }

    /// The occurs check rejects a cyclic solution.
    #[test]
    fn occurs_check_fires() {
        let env = Env::new();
        let mut metas = Metas::new();
        let m = metas.fresh();
        // ?m =?= f ?m
        let rhs = Term::app(c("f"), m.clone());
        assert!(unify(&env, &mut metas, &LocalCtx::new(), &m, &rhs).is_err());
    }

    /// An unsolved metavariable is reported by zonk, not silently accepted.
    #[test]
    fn unsolved_meta_is_an_error() {
        let metas = Metas::new();
        let mut metas = metas;
        let m = metas.fresh();
        assert!(metas.zonk(&m).is_err());
    }

    /// Mismatched rigid heads fail to unify.
    #[test]
    fn rigid_mismatch_fails() {
        let env = Env::new();
        let mut metas = Metas::new();
        assert!(unify(&env, &mut metas, &LocalCtx::new(), &c("Nat"), &c("Bool")).is_err());
    }

    /// A context with one binder of type `A` (a `Var(0)` in scope).
    fn ctx1() -> LocalCtx {
        let mut ctx = LocalCtx::new();
        ctx.push(c("A"));
        ctx
    }

    /// **Higher-order pattern unification.** `?m x =?= f x` (x the bound variable) solves
    /// `?m := λ (_ : A). f #0` — applying it back to `x` recovers `f x`.
    #[test]
    fn pattern_unification_solves_a_function() {
        let env = Env::new();
        let mut metas = Metas::new();
        let m = metas.fresh();
        let ctx = ctx1();
        // ?m #0  =?=  f #0
        let lhs = Term::app(m.clone(), Term::Var(0));
        let rhs = Term::app(c("f"), Term::Var(0));
        unify(&env, &mut metas, &ctx, &lhs, &rhs).unwrap();
        let expected = Term::lam(c("A"), Term::app(c("f"), Term::Var(0)));
        assert_eq!(metas.zonk(&m).unwrap(), expected);
    }

    /// A pattern solution must *abstract* the variable: `?m x =?= f y` where `y` is a
    /// different in-scope variable that is **not** in the spine has no pattern solution
    /// (the free `y` would escape `?m`'s scope) — reported, not mis-solved.
    #[test]
    fn pattern_unification_rejects_escaping_variable() {
        let env = Env::new();
        let mut metas = Metas::new();
        let m = metas.fresh();
        let mut ctx = LocalCtx::new();
        ctx.push(c("A")); // y = Var(1) after the next push
        ctx.push(c("A")); // x = Var(0)
        // ?m #0  =?=  f #1   — #1 (y) is not in the spine.
        let lhs = Term::app(m.clone(), Term::Var(0));
        let rhs = Term::app(c("f"), Term::Var(1));
        assert!(unify(&env, &mut metas, &ctx, &lhs, &rhs).is_err());
    }

    /// The occurs check fires for higher-order problems too: `?m x =?= f (?m x)`.
    #[test]
    fn pattern_unification_occurs_check() {
        let env = Env::new();
        let mut metas = Metas::new();
        let m = metas.fresh();
        let ctx = ctx1();
        let mx = Term::app(m.clone(), Term::Var(0));
        let rhs = Term::app(c("f"), mx.clone());
        assert!(unify(&env, &mut metas, &ctx, &mx, &rhs).is_err());
    }

    /// A non-pattern spine (a metavariable applied to a *non-variable*) is outside the
    /// decidable fragment and is reported rather than guessed.
    #[test]
    fn non_pattern_spine_is_reported() {
        let env = Env::new();
        let mut metas = Metas::new();
        let m = metas.fresh();
        let ctx = ctx1();
        // ?m (f #0)  =?=  #0   — argument is not a bare variable.
        let lhs = Term::app(m.clone(), Term::app(c("f"), Term::Var(0)));
        let err = unify(&env, &mut metas, &ctx, &lhs, &Term::Var(0)).unwrap_err();
        assert!(err.contains("higher-order"), "got: {err}");
    }

    /// A two-argument pattern with the spine variables in *swapped* order: `?m x y =?=
    /// g y x` solves `?m := λ x y. g y x` (the inversion maps each variable to its
    /// binder), so applying it to `x, y` recovers `g y x`.
    #[test]
    fn pattern_unification_permutes_arguments() {
        let env = Env::new();
        let mut metas = Metas::new();
        let m = metas.fresh();
        let mut ctx = LocalCtx::new();
        ctx.push(c("A")); // x = Var(1)
        ctx.push(c("A")); // y = Var(0)
        // ?m x y  =?=  g y x      (x = #1, y = #0)
        let lhs = Term::apps(m.clone(), [Term::Var(1), Term::Var(0)]);
        let rhs = Term::apps(c("g"), [Term::Var(0), Term::Var(1)]);
        unify(&env, &mut metas, &ctx, &lhs, &rhs).unwrap();
        // Solution λ x y. g y x : inside, x = #1, y = #0, so body = g #0 #1.
        let expected = Term::lam(c("A"), Term::lam(c("A"), Term::apps(c("g"), [Term::Var(0), Term::Var(1)])));
        assert_eq!(metas.zonk(&m).unwrap(), expected);
        // And it really reconstructs the original under β: (λxy. g y x) x y ≡ g y x.
        let applied = Term::apps(metas.zonk(&m).unwrap(), [Term::Var(1), Term::Var(0)]);
        let nbe = Nbe::new(&env);
        assert_eq!(nbe.normalize_open(2, &applied), nbe.normalize_open(2, &rhs));
    }
}
