//! Coinductive ("codata") types — greatest fixpoints, the dual of `rv_kernel::generate`.
//!
//! ## What this delivers
//!
//! A sound, kernel-checked **destructor/coiteration** presentation of coinductive
//! types, generalized to **indexed** families (`S : Π params. Π indices. Sort u`).
//! Where an inductive is given by its *constructors* and eliminated by a *recursor*, a
//! coinductive `S` is given by its **destructors** (observations) and *introduced* by
//! a **corecursor** `S.corec` (the `unfold`/coiteration primitive). They are precise
//! categorical duals: an inductive is the **initial algebra** of its signature
//! functor, a coinductive is the **final coalgebra** of its destructor functor.
//!
//! ### Example: `Stream A` (non-indexed)
//!
//! ```text
//!   codata Stream (A : Type) where
//!     Stream.head : Stream A → A          -- a plain observation
//!     Stream.tail : Stream A → Stream A   -- a corecursive observation
//! ```
//!
//! yields
//!
//! ```text
//!   Stream.corec.{v} : Π (A : Type) (X : Sort v)
//!       (h : X → A) (t : X → X) (seed : X), Stream A
//! ```
//!
//! with two ν-rules (see [`crate::reduce::Reducer`]):
//!
//! ```text
//!   Stream.head A (Stream.corec A X h t s)  ↦  h s
//!   Stream.tail A (Stream.corec A X h t s)  ↦  Stream.corec A X h t (t s)
//! ```
//!
//! ### Example: `Bisim A (s t : Stream A) : Prop` (indexed)
//!
//! ```text
//!   codata Bisim (A : Type) (s t : Stream A) : Prop where
//!     Bisim.head_eq     : Bisim A s t → head s = head t             -- plain, index-dependent
//!     Bisim.tail_bisim  : Bisim A s t → Bisim A (tail s) (tail t)   -- corecursive, index-*transforming*
//! ```
//!
//! Here the corecursive destructor's result is `Bisim A (tail s) (tail t)` — the
//! coinductive applied to **transformed** indices, not the scrutinee's own `s, t`. This
//! is exactly the generalization over the non-indexed case (there, the transform is
//! the identity). See "Supported form" below for the precise shape and restriction.
//!
//! ## Why this is SOUND, and how productivity is guaranteed
//!
//! The **only** way to build an inhabitant of a coinductive is `S.corec`. There is no
//! surface syntax for a free-form "corecursive definition" whose body could loop
//! unproductively, so **there is no guardedness check to run over user code** — the one
//! primitive is guarded *by construction*:
//!
//! * every ν-reduction exposes **exactly one** observation layer;
//! * a corecursive observation places the recursive occurrence back **under** a fresh
//!   corecursor (i.e. under a fresh destructor), so nothing unfolds until the *next*
//!   observation demands it. This is the productivity/guardedness invariant — the dual
//!   of an inductive recursor's structural descent — and it holds for `S.corec` no
//!   matter what step functions the user supplies. A "step" is an ordinary total
//!   function `Π indices. X → R`; it cannot itself observe the coinductive it is
//!   building (it only sees the carrier `X` and the *current* indices, both mere
//!   data), so it can never force an unbounded chain of unfoldings. The *new* indices
//!   of the next layer are computed **statically**, at declaration time, as a fixed
//!   term over `[params, indices]` (the index-transform) — never by running
//!   user-supplied code — so they add no new way to loop.
//!
//! Because `S.corec` always terminates after producing one head layer, the ν-rules are
//! **weakly normalizing on observations**: `whnf` of any finite composition of
//! observations halts. Non-productive loops (the adversarial case) are *inexpressible*,
//! not merely rejected — see the crate tests.
//!
//! ## Supported form (the exact restriction)
//!
//! * A coinductive `S : Π params. Π indices. Sort s` with **uniform parameters**
//!   (shared, unchanged across all destructors and observations, exactly as before)
//!   plus an optional **index telescope** (`num_indices` may be `0`, recovering the
//!   original non-indexed form exactly).
//! * Each destructor has type `Π params. Π indices. S params indices → R` where `R`
//!   (under `[params, indices, scrutinee]`) is **either**
//!     - a **plain** result: it mentions neither `S` nor the scrutinee variable — a
//!       fixed observation type expressed in `[params, indices]` (it *may* depend on
//!       the indices: `Bisim.head_eq`'s result `head s = head t` is plain and mentions
//!       `s, t`), **or**
//!     - a **corecursive** result: `S params indices'` where `indices'` is an
//!       **arbitrary** term over `[params, indices]` (not mentioning `S` or the
//!       scrutinee) — the *index-transform*. `Stream.tail`'s transform is the
//!       identity (`indices' = indices`, vacuously, `n = 0`); `Bisim.tail_bisim`'s
//!       transform is `(tail s, tail t)`.
//!   Anything else (a nested/functional/`S`-mentioning result other than `S params
//!   indices'`) is **rejected** — conservative, keeping the corecursor's coalgebra
//!   signature first-order and the ν-rules sound.
//! * **The restriction**: the corecursor's carrier is an **indexed family**
//!   `X : Π indices. Sort v` (not just a bare `Sort v`) — a state `x : X i` carries,
//!   via its type, a certificate tying it to the index `i` it inhabits. Each step is
//!   correspondingly **index-polymorphic** and **carrier-indexed**:
//!   `step_d : Π indices (x : X indices). R_d[indices]` (a corecursive step's
//!   codomain is `X indices'` — the carrier at the *transformed* indices, so the
//!   *next* state is tied to the *next* index by construction, with no separate
//!   coherence proof obligation: it's just an ordinary dependent function type). This
//!   is what makes `Bisim` expressible: the step only has to behave correctly *at the
//!   indices it is actually invoked with* (as certified by the state it's handed),
//!   never universally over every possible index — `Bisim.head_eq`'s step type
//!   `Π s t (x : X s t). Eq A (head s) (head t)` would be *false* if it had to hold
//!   for arbitrary `s t`, but is provable once `x : X s t` supplies (or witnesses)
//!   the invariant relating them. The restriction that remains is only that the
//!   index-transform itself is a **fixed term over `[params, indices]`** — it cannot
//!   consult the state being unfolded (see "index-transform depends on the observed
//!   value" in the tests) — which is exactly what keeps productivity syntactic
//!   (no user code runs to determine "what index are we at").
//! * A coinductive must have **≥1 destructor** (otherwise nothing is observable, and the
//!   type is a useless unit; we reject the degenerate empty case).

use crate::check::Checker;
use crate::env::{Coinductive, CorecRule, Corecursor, Decl, Destructor, Env};
use crate::level::Level;
use crate::term::{Name, Term};
use crate::util::{fold_pis, mk_var, occurs, peel_all_pis, peel_pis};
use std::collections::HashMap;
use std::rc::Rc;

/// A destructor in a high-level coinductive specification.
pub struct DtorSpec {
    pub name: Name,
    /// The destructor's type: `Π params. Π indices. S params indices → R`.
    pub ty: Term,
}

/// A high-level coinductive specification handed to [`declare_coinductive`].
pub struct CoindSpec {
    pub name: Name,
    /// Universe parameters of the coinductive itself (the corecursor's carrier
    /// universe is added separately by the elaborator).
    pub num_levels: u32,
    /// The type former's type: `Π params. Π indices. Sort s`.
    pub ty: Term,
    pub num_params: usize,
    pub dtors: Vec<DtorSpec>,
    /// Name to give the generated corecursor (e.g. `"Stream.corec"`).
    pub corec_name: Name,
}

/// The classified result type of a destructor.
enum ResultKind {
    /// A fixed observation type `R` (mentions neither `S` nor the scrutinee); carried in
    /// the *param+index* context `[params, indices]` (scrutinee binder already removed
    /// as unused).
    Plain(Term),
    /// A corecursive observation: the result is `S params indices'`. `indices'` (`n`
    /// terms, possibly empty) is the index-transform, in context `[params, indices]`.
    Corecursive(Vec<Term>),
}

/// Elaborate and install a coinductive family. See the module docs for the exact
/// supported form and the soundness/productivity argument.
pub fn declare_coinductive(env: &mut Env, spec: CoindSpec) -> Result<(), String> {
    let CoindSpec { name, num_levels, ty, num_params, dtors, corec_name } = spec;
    let k = num_params;
    let ind_levels: Vec<Level> = (0..num_levels).map(Level::param).collect();

    if dtors.is_empty() {
        return Err(format!("coinductive '{name}' must have at least one destructor"));
    }

    // 1. Type-check the former and split into params / indices / result sort.
    {
        let chk = Checker::new(env);
        chk.infer_closed(&ty).map_err(|e| format!("type former '{name}': {e}"))?;
    }
    let (param_doms, after_params) =
        peel_pis(ty.clone(), k).ok_or_else(|| format!("'{name}' has fewer than {k} parameters"))?;
    let (index_doms, result_sort) = peel_all_pis(after_params);
    let n = index_doms.len();
    match &result_sort {
        Term::Sort(_) => {}
        other => {
            return Err(format!(
                "coinductive '{name}' must be `Π params. Π indices. Sort _`, \
                 found trailing {other:?}"
            ))
        }
    }

    // Install the former up front so destructors may reference it.
    let dtor_names: Vec<Name> = dtors.iter().map(|d| d.name.clone()).collect();
    env.insert(
        name.clone(),
        Decl::Coinductive(Rc::new(Coinductive {
            num_levels,
            ty: ty.clone(),
            num_params: k,
            num_indices: n,
            dtors: dtor_names.clone(),
            corecursor: corec_name.clone(),
        })),
    )?;

    // 2. Check every destructor and classify its result.
    //    Destructor type must be `Π params. Π indices. (S params indices) → R`.
    let mut results: Vec<ResultKind> = Vec::with_capacity(dtors.len());
    for d in &dtors {
        {
            let chk = Checker::new(env);
            chk.infer_closed(&d.ty).map_err(|e| format!("destructor '{}': {e}", d.name))?;
        }
        let (dparams, rest) = peel_pis(d.ty.clone(), k + n).ok_or_else(|| {
            format!("destructor '{}' has fewer than {} params+indices", d.name, k + n)
        })?;
        let _ = dparams;
        // rest must be `S params indices → R` : a single Π whose domain is
        // `S params indices`.
        let (scrut_dom, result) = match rest {
            Term::Pi(_, dom, cod) => ((*dom).clone(), (*cod).clone()),
            other => {
                return Err(format!(
                    "destructor '{}' must be `Π params. Π indices. {name} params indices → R`, \
                     found {other:?}",
                    d.name
                ))
            }
        };
        // The scrutinee domain must be exactly `S params indices` (canonical, matching
        // the destructor's own bound params/indices — no transform on the scrutinee
        // side, only in a corecursive *result*).
        match coind_app_head(&name, k, n, &scrut_dom, 0) {
            Some(idx_args) if idx_args.iter().enumerate().all(|(i, a)| is_canonical_index(a, n, i)) => {}
            _ => {
                return Err(format!(
                    "destructor '{}' must take `{name} params indices` as its scrutinee",
                    d.name
                ))
            }
        }
        // Classify the result, which lives under `[params, indices, scrutinee]`
        // (scrutinee = Var(0)).
        match coind_app_head(&name, k, n, &result, 1) {
            Some(idx_args) => {
                // Corecursive: params matched exactly (checked inside
                // `coind_app_head`); the index args are the transform, provided they
                // don't mention the scrutinee (checked already isn't enough — verify
                // explicitly) or `S` itself (kept first-order/acyclic).
                for a in &idx_args {
                    if occurs(&name, a) {
                        return Err(format!(
                            "destructor '{}' corecursive result's index-transform \
                             mentions '{name}' — unsupported",
                            d.name
                        ));
                    }
                    if mentions_var(a, 0) {
                        return Err(format!(
                            "destructor '{}' corecursive result's index-transform \
                             depends on the observed value; only params/indices may be used",
                            d.name
                        ));
                    }
                }
                // Drop the (unused) scrutinee binder from each transform term.
                let transform: Vec<Term> = idx_args.iter().map(|a| a.lift(-1, 1)).collect();
                results.push(ResultKind::Corecursive(transform));
            }
            None => {
                // Plain: must mention neither S nor the scrutinee variable Var(0).
                if occurs(&name, &result) {
                    return Err(format!(
                        "destructor '{}' result mentions '{name}' in an unsupported position \
                         (only a bare `{name} params indices'` corecursive result is allowed)",
                        d.name
                    ));
                }
                if mentions_var(&result, 0) {
                    return Err(format!(
                        "destructor '{}' result depends on the observed value; only fixed \
                         (param/index-expressed) observation types are supported",
                        d.name
                    ));
                }
                // Drop the (unused) scrutinee binder: re-express `R` in the
                // param+index-only context.
                let plain = result.lift(-1, 1);
                results.push(ResultKind::Plain(plain));
            }
        }
    }

    // 3. Install the destructors.
    for (i, d) in dtors.iter().enumerate() {
        env.insert(
            d.name.clone(),
            Decl::Destructor(Rc::new(Destructor {
                num_levels,
                ty: d.ty.clone(),
                coind: name.clone(),
                index: i,
                corecursive: matches!(results[i], ResultKind::Corecursive(_)),
            })),
        )?;
    }

    // 4. Synthesize the corecursor type:
    //      S.corec.{levels, v} : Π params. Π (X : Π indices. Sort v).
    //          Π (step_d : Π indices (x : X indices). R_d[X indices' for S]) …
    //          Π indices (seed : X indices). S params indices
    //    Universe: the carrier `X : Π indices. Sort v` gets a fresh universe parameter
    //    `v` at index `num_levels` (so `S.corec` has `num_levels + 1` level params).
    //    The carrier *is* indexed (an `[indices]`-family, not a single `Sort v`) —
    //    this is what makes indexed corecursion sound: a state `x : X i` carries
    //    (via its type) a certificate tying it to the index `i` it inhabits, so a
    //    step is only obliged to behave correctly *at the indices it is actually
    //    invoked with*, never universally over every possible index (which would be
    //    too strong — e.g. "the heads of *any* two streams are equal" is false; "the
    //    heads of two streams *certified bisimilar so far* are equal" is provable).
    //    Each step is still index-polymorphic (quantifies its own fresh copy of
    //    `indices`, dualizing how an indexed recursor's minor premise quantifies its
    //    own copy of the indices — see `rv_kernel::mutual`) but now also takes the
    //    *carrier at those indices* as its state argument.
    let carrier_u = Level::param(num_levels);
    let corec_levels = num_levels + 1;
    let m = dtors.len();

    // `S params current_indices` at context depth `depth`, where params sit at
    // absolute levels `0..k` and the *outer* "current indices" sit at absolute levels
    // `k+1+m .. k+1+m+n`.
    let ind_app = |depth: usize| -> Term {
        let mut t = Term::cnst(name.clone(), ind_levels.clone());
        for j in 0..k {
            t = Term::app(t, mk_var(depth, j));
        }
        for i in 0..n {
            t = Term::app(t, mk_var(depth, k + 1 + m + i));
        }
        t
    };

    // `X` (the carrier, bound at absolute level `k`) applied to `n` index terms
    // (already expressed at context depth `depth`).
    let apply_x = |depth: usize, idx: &[Term]| -> Term {
        let mut t = mk_var(depth, k);
        for a in idx {
            t = Term::app(t, a.clone());
        }
        t
    };

    // Step domains. The carrier `X` sits at absolute level `k` (right after params).
    // Step `d` sits at absolute level `k + 1 + d`, and is itself a small Π-telescope:
    // `Π (local indices) (x : X local_indices). R_d'` — the step's *own* fresh copy
    // of the index binders (not the corecursor's outer "current indices", which are
    // bound later and only fix the initial/threaded state — see the module doc).
    let mut step_doms: Vec<Term> = Vec::with_capacity(m);
    for (d, res) in results.iter().enumerate() {
        // Depth just before the step-d binder: params(k) + X(1) + prior steps(d).
        let d0 = k + 1 + d;
        // Re-lift this step's local index domains (extracted from the type former's
        // own index telescope, originally in context `[params]`) to sit right here:
        // insert `d0 - k` new binders below cutoff `i` (params keep levels 0..k-1, no
        // change in *value*, but they're now `d0 - k` binders further away).
        let local_index_doms: Vec<Term> = index_doms
            .iter()
            .enumerate()
            .map(|(i, dom)| dom.lift((d0 - k) as isize, i))
            .collect();
        // Depth right after the local indices (before the `x` binder) — where `X`'s
        // application to the local indices (the `x` domain) is expressed.
        let d_before_x = d0 + n;
        let local_index_vars: Vec<Term> = (0..n).map(|i| mk_var(d_before_x, d0 + i)).collect();
        let dom_x = apply_x(d_before_x, &local_index_vars);
        // Depth at the point right after the local indices + `x:X local_indices` binder.
        let d_cod = d_before_x + 1;
        // Images re-expressing a term originally in context `[params, indices]` (as
        // stored: Var(0) = last/innermost index, …, Var(n-1) = first index, Var(n) =
        // last param, …, Var(n+k-1) = first param) in terms of *this step's* local
        // index copies (bound at absolute levels d0..d0+n-1) and the (unchanged)
        // outer params, at depth `d_cod`.
        let images = {
            let mut v = Vec::with_capacity(k + n);
            for i in (0..n).rev() {
                v.push(mk_var(d_cod, d0 + i));
            }
            for j in (0..k).rev() {
                v.push(mk_var(d_cod, j));
            }
            v
        };
        let cod = match res {
            ResultKind::Corecursive(transform) => {
                // `X` applied to the *transformed* local indices — the next state's
                // type, tied to the index it will actually inhabit.
                let transformed: Vec<Term> = transform.iter().map(|t| t.subst_ctx(&images)).collect();
                apply_x(d_cod, &transformed)
            }
            ResultKind::Plain(r) => r.subst_ctx(&images),
        };
        let mut step = Term::pi(dom_x, cod);
        for dom in local_index_doms.into_iter().rev() {
            step = Term::pi(dom, step);
        }
        step_doms.push(step);
    }

    // Outer "current indices" domains: re-lift the index telescope (originally in
    // context `[params]`) to sit after `X` and the `m` steps (insert `1+m` new
    // binders below cutoff `i`).
    let outer_index_doms: Vec<Term> =
        index_doms.iter().enumerate().map(|(i, dom)| dom.lift((1 + m) as isize, i)).collect();

    // seed domain: `X` applied to the outer current indices, at depth k + 1 + m + n.
    let d_seed = k + 1 + m + n;
    let outer_index_vars: Vec<Term> = (0..n).map(|i| mk_var(d_seed, k + 1 + m + i)).collect();
    let seed_dom = apply_x(d_seed, &outer_index_vars);

    // conclusion: `S params current_indices`, at depth k + 1 + m + n + 1.
    let d_concl = d_seed + 1;
    let concl = ind_app(d_concl);

    // Assemble: params, X, steps…, indices…, seed ⟶ S params indices.
    // `X`'s own type `Π indices. Sort v` reuses `index_doms` unchanged — they're
    // already expressed in context `[params]`, exactly where `X` sits (level `k`).
    let mut all_doms = param_doms.clone();
    all_doms.push(fold_pis(&index_doms, Term::Sort(carrier_u))); // X : Π indices. Sort v
    all_doms.extend(step_doms);
    all_doms.extend(outer_index_doms);
    all_doms.push(seed_dom);
    let corec_ty = fold_pis(&all_doms, concl);

    // 5. ν-rules: one per destructor. step_d is at spine position k + 1 + d.
    let mut rules: HashMap<Name, CorecRule> = HashMap::new();
    for (d, dspec) in dtors.iter().enumerate() {
        let (corecursive, index_transform) = match &results[d] {
            ResultKind::Corecursive(t) => (true, t.clone()),
            ResultKind::Plain(_) => (false, Vec::new()),
        };
        rules.insert(
            dspec.name.clone(),
            CorecRule { dtor: dspec.name.clone(), step_index: k + 1 + d, corecursive, index_transform },
        );
    }

    env.insert(
        corec_name.clone(),
        Decl::Corecursor(Rc::new(Corecursor {
            num_levels: corec_levels,
            ty: corec_ty,
            coind: name.clone(),
            num_params: k,
            num_dtors: m,
            num_indices: n,
            rules,
        })),
    )?;

    Ok(())
}

/// Is `t` (in a context of `depth` extra binders above `[params, indices]`) exactly
/// the coinductive `name` applied to `k + n` arguments whose first `k` are the
/// uniform parameters `Var(depth+k+n-1) … Var(depth+n)`? If so, returns the trailing
/// `n` arguments (the *index* arguments — arbitrary terms, not further checked here).
fn coind_app_head(name: &str, k: usize, n: usize, t: &Term, depth: usize) -> Option<Vec<Term>> {
    let (head, args) = t.unfold_apps();
    match head {
        Term::Const(h, _) if &*h == name => {
            if args.len() != k + n {
                return None;
            }
            let params_ok = args[..k]
                .iter()
                .enumerate()
                .all(|(j, a)| matches!(a, Term::Var(i) if *i == depth + k + n - 1 - j));
            if !params_ok {
                return None;
            }
            Some(args[k..].to_vec())
        }
        _ => None,
    }
}

/// Is `a` exactly the `i`-th (0-indexed) canonical index variable in a context of `n`
/// indices (with `Var(0)` the last/innermost index)? I.e. `a == Var(n-1-i)`.
fn is_canonical_index(a: &Term, n: usize, i: usize) -> bool {
    matches!(a, Term::Var(v) if *v == n - 1 - i)
}

/// Does `t` mention the bound variable at de Bruijn index `k`? (Local copy of the
/// predicate in [`crate::term`], which is private there.)
fn mentions_var(t: &Term, k: usize) -> bool {
    match t {
        Term::Var(i) => *i == k,
        Term::App(f, a) => mentions_var(f, k) || mentions_var(a, k),
        Term::Lam(d, b) | Term::Pi(_, d, b) => mentions_var(d, k) || mentions_var(b, k + 1),
        Term::Let(_, t, v, b) => {
            mentions_var(t, k) || mentions_var(v, k) || mentions_var(b, k + 1)
        }
        Term::PLam(b) => mentions_var(b, k + 1),
        Term::PApp(p, r) => mentions_var(p, k) || mentions_var(r, k),
        Term::PathP(fam, a0, a1) => {
            mentions_var(fam, k + 1) || mentions_var(a0, k) || mentions_var(a1, k)
        }
        Term::Sort(_) | Term::Const(..) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => false,
        Term::Sys(branches) => {
            branches.iter().any(|(p, t)| crate::face::mentions_var(p, k) || mentions_var(t, k))
        }
        Term::Partial(p, a) => crate::face::mentions_var(p, k) || mentions_var(a, k),
    }
}

// ---------------------------------------------------------------------------
// Convenience spec builders (also used by tests).
// ---------------------------------------------------------------------------

use crate::term::name;

/// `Stream.{u} : Type u → Type u` with `head : Stream A → A`, `tail : Stream A → Stream A`.
pub fn stream_spec() -> CoindSpec {
    let u = Level::param(0);
    let stream_a = |a: Term| Term::app(Term::cnst(name("Stream"), vec![u.clone()]), a);
    CoindSpec {
        name: name("Stream"),
        num_levels: 1,
        // Stream : Sort u → Sort u   (A lives in Sort u, Stream A in Sort u)
        ty: Term::pi(Term::Sort(u.clone()), Term::Sort(u.clone())),
        num_params: 1,
        dtors: vec![
            // head : Π (A : Sort u). Stream A → A
            DtorSpec {
                name: name("Stream.head"),
                ty: Term::pi(Term::Sort(u.clone()), Term::pi(stream_a(Term::Var(0)), Term::Var(1))),
            },
            // tail : Π (A : Sort u). Stream A → Stream A
            DtorSpec {
                name: name("Stream.tail"),
                ty: Term::pi(
                    Term::Sort(u.clone()),
                    Term::pi(stream_a(Term::Var(0)), stream_a(Term::Var(1))),
                ),
            },
        ],
        corec_name: name("Stream.corec"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inductive::declare_nat;
    use crate::reduce::Reducer;

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }
    fn lit(n: u32) -> Term {
        let mut t = cn("Nat.zero");
        for _ in 0..n {
            t = Term::app(cn("Nat.succ"), t);
        }
        t
    }

    /// The generated `Stream` corecursor type is well-formed.
    #[test]
    fn stream_corec_type_wellformed() {
        let mut env = Env::new();
        declare_coinductive(&mut env, stream_spec()).unwrap();
        let chk = Checker::new(&env);
        chk.infer_closed(env.get("Stream.corec").unwrap().ty()).unwrap();
    }

    /// `repeat n = Stream.corec Nat Nat (λx.x) (λx.x) n`; observations compute:
    /// `head (repeat 7) ↦ 7`, `head (tail (tail (repeat 7))) ↦ 7`.
    #[test]
    fn repeat_stream_observations_compute() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_coinductive(&mut env, stream_spec()).unwrap();
        let r = Reducer::new(&env);

        // repeat n : Stream Nat
        let repeat = |n: Term| {
            Term::apps(
                Term::cnst(name("Stream.corec"), vec![Level::of_nat(1), Level::of_nat(1)]),
                [
                    cn("Nat"),                                   // A
                    cn("Nat"),                                   // X (carrier)
                    Term::lam(cn("Nat"), Term::Var(0)),          // head-step : X → A
                    Term::lam(cn("Nat"), Term::Var(0)),          // tail-step : X → X
                    n,                                           // seed
                ],
            )
        };
        let head = |s: Term| Term::apps(Term::cnst(name("Stream.head"), vec![Level::of_nat(1)]), [cn("Nat"), s]);
        let tail = |s: Term| Term::apps(Term::cnst(name("Stream.tail"), vec![Level::of_nat(1)]), [cn("Nat"), s]);

        assert!(r.is_def_eq(&head(repeat(lit(7))), &lit(7)), "head (repeat 7) = 7");
        assert!(
            r.is_def_eq(&head(tail(tail(repeat(lit(7))))), &lit(7)),
            "head (tail (tail (repeat 7))) = 7"
        );
    }

    /// `nats = corec Nat Nat (λx.x) (λx. succ x) 0`; the stream `0,1,2,…` observed.
    #[test]
    fn nats_stream_counts_up() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_coinductive(&mut env, stream_spec()).unwrap();
        let r = Reducer::new(&env);

        let nats = Term::apps(
            Term::cnst(name("Stream.corec"), vec![Level::of_nat(1), Level::of_nat(1)]),
            [
                cn("Nat"),
                cn("Nat"),
                Term::lam(cn("Nat"), Term::Var(0)),                        // head = current
                Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0))), // tail-step = succ
                lit(0),
            ],
        );
        let head = |s: Term| Term::apps(Term::cnst(name("Stream.head"), vec![Level::of_nat(1)]), [cn("Nat"), s]);
        let tail = |s: Term| Term::apps(Term::cnst(name("Stream.tail"), vec![Level::of_nat(1)]), [cn("Nat"), s]);

        assert!(r.is_def_eq(&head(nats.clone()), &lit(0)), "nats[0] = 0");
        assert!(r.is_def_eq(&head(tail(nats.clone())), &lit(1)), "nats[1] = 1");
        assert!(r.is_def_eq(&head(tail(tail(nats.clone()))), &lit(2)), "nats[2] = 2");
    }

    /// Differential check: NbE (the checker's conversion path) agrees with the trusted
    /// reducer on ν-reduction, so adopting the fast path cannot equate distinct streams.
    #[test]
    fn nbe_agrees_with_reducer_on_nu() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_coinductive(&mut env, stream_spec()).unwrap();
        let r = Reducer::new(&env);
        let nbe = crate::nbe::Nbe::new(&env);

        let nats = Term::apps(
            Term::cnst(name("Stream.corec"), vec![Level::of_nat(1), Level::of_nat(1)]),
            [
                cn("Nat"),
                cn("Nat"),
                Term::lam(cn("Nat"), Term::Var(0)),
                Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0))),
                lit(0),
            ],
        );
        let head = |s: Term| {
            Term::apps(Term::cnst(name("Stream.head"), vec![Level::of_nat(1)]), [cn("Nat"), s])
        };
        let tail = |s: Term| {
            Term::apps(Term::cnst(name("Stream.tail"), vec![Level::of_nat(1)]), [cn("Nat"), s])
        };
        for i in 0..5u32 {
            let mut s = nats.clone();
            for _ in 0..i {
                s = tail(s);
            }
            let obs = head(s);
            // NbE normal form must be `lit(i)`, and must be def-eq under the reducer.
            assert_eq!(nbe.normalize(&obs), lit(i), "nbe: nats[{i}] = {i}");
            assert!(r.is_def_eq(&obs, &lit(i)), "reducer: nats[{i}] = {i}");
        }
    }

    /// ADVERSARIAL: an empty coinductive (no destructors) is rejected — otherwise it
    /// would be an unobservable unit with a vacuous corecursor.
    #[test]
    fn empty_coinductive_rejected() {
        let mut env = Env::new();
        let spec = CoindSpec {
            name: name("Void"),
            num_levels: 0,
            ty: Term::typ(0),
            num_params: 0,
            dtors: vec![],
            corec_name: name("Void.corec"),
        };
        let err = declare_coinductive(&mut env, spec).unwrap_err();
        assert!(err.contains("at least one destructor"), "got: {err}");
    }

    /// ADVERSARIAL: a destructor with a non-`S params`, `S`-mentioning result (here a
    /// function-typed observation `Stream A → Stream A → Stream A`-ish) is rejected —
    /// keeping the coalgebra signature first-order and the ν-rules sound.
    #[test]
    fn nested_destructor_result_rejected() {
        let mut env = Env::new();
        let u = Level::param(0);
        let stream_a = |a: Term| Term::app(Term::cnst(name("S"), vec![u.clone()]), a);
        let spec = CoindSpec {
            name: name("S"),
            num_levels: 1,
            ty: Term::pi(Term::Sort(u.clone()), Term::Sort(u.clone())),
            num_params: 1,
            dtors: vec![DtorSpec {
                name: name("S.bad"),
                // S.bad : Π (A:Sort u). S A → (S A → S A)   -- result mentions S nontrivially
                ty: Term::pi(
                    Term::Sort(u.clone()),
                    Term::pi(
                        stream_a(Term::Var(0)),
                        // result: S A → S A  (mentions S nontrivially, not a bare `S A`)
                        Term::pi(stream_a(Term::Var(1)), stream_a(Term::Var(2))),
                    ),
                ),
            }],
            corec_name: name("S.corec"),
        };
        let err = declare_coinductive(&mut env, spec).unwrap_err();
        assert!(err.contains("unsupported"), "got: {err}");
    }

    // -----------------------------------------------------------------
    // Indexed coinductive tests.
    // -----------------------------------------------------------------

    /// `Bisim.{u} : Π (A:Sort u) (s t : Stream A). Prop` — a propositional
    /// bisimulation on `Stream A`, coinductively defined by:
    ///   `Bisim.head_eq    : Bisim A s t → Eq A (head s) (head t)`      (plain, index-dependent)
    ///   `Bisim.tail_bisim : Bisim A s t → Bisim A (tail s) (tail t)`   (corecursive, index-transforming)
    fn bisim_spec() -> CoindSpec {
        let u = Level::param(0);
        let stream_a = |a: Term| Term::app(Term::cnst(name("Stream"), vec![u.clone()]), a);
        let head = |a: Term, s: Term| Term::apps(Term::cnst(name("Stream.head"), vec![u.clone()]), [a, s]);
        let tail = |a: Term, s: Term| Term::apps(Term::cnst(name("Stream.tail"), vec![u.clone()]), [a, s]);
        let eq = |a: Term, x: Term, y: Term| {
            Term::apps(Term::cnst(name("Eq"), vec![u.clone()]), [a, x, y])
        };
        let bisim_app = |a: Term, s: Term, t: Term| {
            Term::apps(Term::cnst(name("Bisim"), vec![u.clone()]), [a, s, t])
        };
        CoindSpec {
            name: name("Bisim"),
            num_levels: 1,
            // Bisim : Π (A:Sort u) (s t : Stream A). Prop
            ty: Term::pi(
                Term::Sort(u.clone()),
                Term::pi(stream_a(Term::Var(0)), Term::pi(stream_a(Term::Var(1)), Term::prop())),
            ),
            num_params: 1,
            dtors: vec![
                DtorSpec {
                    name: name("Bisim.head_eq"),
                    // Π A s t. Bisim A s t → Eq A (head s) (head t)
                    // Context at the result: [A=Var3, s=Var2, t=Var1, scrutinee=Var0].
                    ty: Term::pi(
                        Term::Sort(u.clone()),
                        Term::pi(
                            stream_a(Term::Var(0)),
                            Term::pi(
                                stream_a(Term::Var(1)),
                                Term::pi(
                                    bisim_app(Term::Var(2), Term::Var(1), Term::Var(0)),
                                    eq(
                                        Term::Var(3),
                                        head(Term::Var(3), Term::Var(2)),
                                        head(Term::Var(3), Term::Var(1)),
                                    ),
                                ),
                            ),
                        ),
                    ),
                },
                DtorSpec {
                    name: name("Bisim.tail_bisim"),
                    // Π A s t. Bisim A s t → Bisim A (tail s) (tail t)
                    // Context at the result: [A=Var3, s=Var2, t=Var1, scrutinee=Var0].
                    ty: Term::pi(
                        Term::Sort(u.clone()),
                        Term::pi(
                            stream_a(Term::Var(0)),
                            Term::pi(
                                stream_a(Term::Var(1)),
                                Term::pi(
                                    bisim_app(Term::Var(2), Term::Var(1), Term::Var(0)),
                                    bisim_app(
                                        Term::Var(3),
                                        tail(Term::Var(3), Term::Var(2)),
                                        tail(Term::Var(3), Term::Var(1)),
                                    ),
                                ),
                            ),
                        ),
                    ),
                },
            ],
            corec_name: name("Bisim.corec"),
        }
    }

    fn setup_bisim_env() -> Env {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_coinductive(&mut env, stream_spec()).unwrap();
        crate::inductive::declare_eq(&mut env).unwrap();
        declare_coinductive(&mut env, bisim_spec()).unwrap();
        env
    }

    /// The generated indexed `Bisim.corec` type is well-formed.
    #[test]
    fn bisim_corec_type_wellformed() {
        let env = setup_bisim_env();
        let chk = Checker::new(&env);
        chk.infer_closed(env.get("Bisim.corec").unwrap().ty()).unwrap();
    }

    /// A corecursive proof of `Bisim A s s` (reflexivity), for `s = nats` (the
    /// infinite `0,1,2,…` stream): carrier `X = Nat` (any inhabited type works —
    /// the proof never inspects it), `head_eq` step is `Eq.refl`, `tail_bisim` step
    /// returns a fixed witness. This exercises the ν-rule on an *indexed*
    /// corecursor: each `Bisim.tail_bisim` observation must advance the *pair* of
    /// indices `(s, s) ↦ (tail s, tail s)` together.
    #[test]
    fn bisim_reflexivity_corecursive_proof() {
        let env = setup_bisim_env();
        let r = Reducer::new(&env);

        let nats = Term::apps(
            Term::cnst(name("Stream.corec"), vec![Level::of_nat(1), Level::of_nat(1)]),
            [
                cn("Nat"),
                cn("Nat"),
                Term::lam(cn("Nat"), Term::Var(0)),
                Term::lam(cn("Nat"), Term::app(cn("Nat.succ"), Term::Var(0))),
                lit(0),
            ],
        );
        let head = |s: Term| Term::apps(Term::cnst(name("Stream.head"), vec![Level::of_nat(1)]), [cn("Nat"), s]);
        let tail = |s: Term| Term::apps(Term::cnst(name("Stream.tail"), vec![Level::of_nat(1)]), [cn("Nat"), s]);

        // Bisim.corec.{Nat-level, Prop-level} Nat
        //   X := λ s t. Eq (Stream Nat) s t          -- carrier: an *indexed* family,
        //                                                the witness IS the invariant.
        //   head_eq_step := λ s t (x : Eq (Stream Nat) s t). <congrArg head x>
        //   tail_step     := λ s t (x : Eq (Stream Nat) s t). <congrArg tail x>
        //   s0 t0 := nats nats ;  seed := Eq.refl (Stream Nat) nats
        //
        // This exercises the *indexed carrier*: the step only has to prove `head s =
        // head t` for `s, t` it is handed a *bisimilarity witness* for — never for
        // arbitrary `s, t` (which would be unprovable) — because `X s t` is exactly
        // `Eq (Stream Nat) s t`, not an uninformative `Unit`.
        let stream_nat =
            Term::app(Term::cnst(name("Stream"), vec![Level::of_nat(1)]), cn("Nat"));
        let eq_stream = |a: Term, b: Term| {
            Term::apps(
                Term::cnst(name("Eq"), vec![Level::of_nat(1)]),
                [stream_nat.clone(), a, b],
            )
        };
        // `congrArg f a b h : Eq codom (f a) (f b)`, for `h : Eq (Stream Nat) a b` and
        // `f` a (meta-level) Nat-family-preserving function on stream terms, built via
        // `Eq.rec`'s standard transport-based congruence proof. `codom` is the type of
        // `f`'s results (`Nat` for `head`, `Stream Nat` for `tail`); `codom_lvl` is its
        // sort level (both `Level::of_nat(1)` here). All of `a, b, h` are expressed at
        // the *call site's* de Bruijn depth (no internal binders of their own).
        let congr_arg = |f: &dyn Fn(Term) -> Term,
                          codom: Term,
                          codom_lvl: Level,
                          a: Term,
                          b: Term,
                          h: Term| {
            // motive := λ (b':Stream Nat) (h':Eq (Stream Nat) a b'). Eq codom (f a) (f b')
            // `a` (from the call site) must be lifted by 2 to sit under the two new
            // binders (b', h'); `b'` is Var(1), `h'` is Var(0) inside the body.
            let a_deep = a.lift(2, 0);
            let motive_dom_h = eq_stream(a.lift(1, 0), Term::Var(0)); // under just b'
            let motive_body = Term::apps(
                Term::cnst(name("Eq"), vec![codom_lvl.clone()]),
                [codom.clone(), f(a_deep), f(Term::Var(1))],
            );
            let motive = Term::lam(stream_nat.clone(), Term::lam(motive_dom_h, motive_body));
            let refl_case = Term::apps(
                Term::cnst(name("Eq.refl"), vec![codom_lvl]),
                [codom, f(a.clone())],
            );
            Term::apps(
                Term::cnst(name("Eq.rec"), vec![Level::of_nat(1), Level::Zero]),
                [stream_nat.clone(), a, motive, refl_case, b, h],
            )
        };
        let carrier_ty = Term::lam(stream_nat.clone(), Term::lam(stream_nat.clone(), eq_stream(Term::Var(1), Term::Var(0))));
        // Under [s, t, x]: s = Var(2), t = Var(1), x = Var(0).
        let head_eq_step = Term::lam(
            stream_nat.clone(),
            Term::lam(
                stream_nat.clone(),
                Term::lam(
                    eq_stream(Term::Var(1), Term::Var(0)),
                    congr_arg(&head, cn("Nat"), Level::of_nat(1), Term::Var(2), Term::Var(1), Term::Var(0)),
                ),
            ),
        );
        let tail_step = Term::lam(
            stream_nat.clone(),
            Term::lam(
                stream_nat.clone(),
                Term::lam(
                    eq_stream(Term::Var(1), Term::Var(0)),
                    congr_arg(&tail, stream_nat.clone(), Level::of_nat(1), Term::Var(2), Term::Var(1), Term::Var(0)),
                ),
            ),
        );
        let seed = Term::apps(
            Term::cnst(name("Eq.refl"), vec![Level::of_nat(1)]),
            [stream_nat.clone(), nats.clone()],
        );
        let proof = Term::apps(
            Term::cnst(name("Bisim.corec"), vec![Level::of_nat(1), Level::Zero]),
            [
                cn("Nat"),
                carrier_ty.clone(),
                head_eq_step,
                tail_step,
                nats.clone(),
                nats.clone(),
                seed,
            ],
        );

        // Type-check: `proof : Bisim Nat nats nats`.
        let chk = Checker::new(&env);
        let ty = chk.infer_closed(&proof).expect("bisim corecursive proof type-checks");
        let expected = Term::apps(
            Term::cnst(name("Bisim"), vec![Level::of_nat(1)]),
            [cn("Nat"), nats.clone(), nats.clone()],
        );
        assert!(r.is_def_eq(&ty, &expected), "proof : Bisim Nat nats nats, got {ty:?}");

        // Observe head_eq at the top: `Bisim.head_eq Nat nats nats proof : Eq Nat (head nats) (head nats)`.
        let head_eq_obs = Term::apps(
            Term::cnst(name("Bisim.head_eq"), vec![Level::of_nat(1)]),
            [cn("Nat"), nats.clone(), nats.clone(), proof.clone()],
        );
        let obs_ty = chk.infer_closed(&head_eq_obs).expect("head_eq observation type-checks");
        let expected_eq =
            Term::apps(Term::cnst(name("Eq"), vec![Level::of_nat(1)]), [cn("Nat"), head(nats.clone()), head(nats.clone())]);
        assert!(r.is_def_eq(&obs_ty, &expected_eq));

        // Observe through several `tail_bisim`s, then `head_eq`: must still type-check
        // at the *transformed* indices `Bisim Nat (tail^i nats) (tail^i nats)`, proving
        // the index-transform ν-rule advances both index slots together.
        let mut p = proof.clone();
        let mut s = nats.clone();
        for i in 0..4u32 {
            let obs = Term::apps(
                Term::cnst(name("Bisim.head_eq"), vec![Level::of_nat(1)]),
                [cn("Nat"), s.clone(), s.clone(), p.clone()],
            );
            let obs_ty = chk.infer_closed(&obs).unwrap_or_else(|e| panic!("layer {i}: {e}"));
            let expected =
                Term::apps(Term::cnst(name("Eq"), vec![Level::of_nat(1)]), [cn("Nat"), head(s.clone()), head(s.clone())]);
            assert!(r.is_def_eq(&obs_ty, &expected), "layer {i}: head_eq type");
            p = Term::apps(
                Term::cnst(name("Bisim.tail_bisim"), vec![Level::of_nat(1)]),
                [cn("Nat"), s.clone(), s.clone(), p],
            );
            s = tail(s);
        }
    }

    /// ADVERSARIAL: an indexed destructor whose scrutinee domain doesn't match the
    /// canonical (untransformed) indices is rejected.
    #[test]
    fn indexed_scrutinee_mismatch_rejected() {
        let mut env = Env::new();
        declare_nat(&mut env).unwrap();
        declare_coinductive(&mut env, stream_spec()).unwrap();
        let u = Level::param(0);
        let stream_a = |a: Term| Term::app(Term::cnst(name("Stream"), vec![u.clone()]), a);
        // Bad : Π A (s t : Stream A). Prop, with a destructor whose scrutinee domain
        // swaps s and t (`Bad A t s` instead of `Bad A s t`).
        let spec = CoindSpec {
            name: name("Bad"),
            num_levels: 1,
            ty: Term::pi(
                Term::Sort(u.clone()),
                Term::pi(stream_a(Term::Var(0)), Term::pi(stream_a(Term::Var(1)), Term::prop())),
            ),
            num_params: 1,
            dtors: vec![DtorSpec {
                name: name("Bad.obs"),
                ty: Term::pi(
                    Term::Sort(u.clone()),
                    Term::pi(
                        stream_a(Term::Var(0)),
                        Term::pi(
                            stream_a(Term::Var(1)),
                            Term::pi(
                                // scrutinee domain: `Bad A t s` (swapped) — wrong.
                                Term::apps(
                                    Term::cnst(name("Bad"), vec![u.clone()]),
                                    [Term::Var(2), Term::Var(0), Term::Var(1)],
                                ),
                                Term::prop(),
                            ),
                        ),
                    ),
                ),
            }],
            corec_name: name("Bad.corec"),
        };
        let err = declare_coinductive(&mut env, spec).unwrap_err();
        assert!(err.contains("scrutinee"), "got: {err}");
    }

    /// NOTE on the "index-transform depends on the scrutinee" check
    /// (`mentions_var(a, 0)` in `declare_coinductive`): it is *structurally*
    /// unreachable by any well-typed destructor, not merely rejected at runtime. An
    /// index domain is type-checked (via the type former's `ty`) *before* the
    /// coinductive is inserted into the environment, so no index domain can ever be
    /// (or unify with) the coinductive being declared; the scrutinee's type is
    /// exactly that under-construction application, so it can never definitionally
    /// inhabit an index slot. The check remains as defense-in-depth (belt-and-braces
    /// against a future relaxation of that elaboration order), exercised indirectly
    /// by every destructor test above (each already relies on `mentions_var` to
    /// reject scrutinee-dependent *plain* results, the same helper).
    ///
    /// ADVERSARIAL: a corecursive result whose index-transform mentions the
    /// coinductive **itself** (here, a self-describing `Weird : Sort u → Sort u`
    /// indexed by a *type*, whose destructor tries to transform the index to `Weird
    /// T` — nesting the coinductive inside its own index) is rejected. This keeps
    /// the corecursor's index-transform acyclic/first-order, matching the
    /// (already-enforced) restriction on plain results.
    #[test]
    fn index_transform_mentions_coinductive_rejected() {
        let mut env = Env::new();
        let u = Level::param(0);
        // Weird : Π (T : Sort u). Sort u   (num_params = 0, num_indices = 1: `T`).
        let spec = CoindSpec {
            name: name("Weird"),
            num_levels: 1,
            ty: Term::pi(Term::Sort(u.clone()), Term::Sort(u.clone())),
            num_params: 0,
            dtors: vec![DtorSpec {
                name: name("Weird.bad"),
                // Weird.bad : Π T. Weird T → Weird (Weird T)
                //   — the index-transform `Weird T` mentions `Weird` itself.
                ty: Term::pi(
                    Term::Sort(u.clone()),
                    Term::pi(
                        Term::app(Term::cnst(name("Weird"), vec![u.clone()]), Term::Var(0)),
                        Term::app(
                            Term::cnst(name("Weird"), vec![u.clone()]),
                            Term::app(Term::cnst(name("Weird"), vec![u.clone()]), Term::Var(1)),
                        ),
                    ),
                ),
            }],
            corec_name: name("Weird.corec"),
        };
        let err = declare_coinductive(&mut env, spec).unwrap_err();
        assert!(err.contains("mentions"), "got: {err}");
    }
}
