//! Coinductive ("codata") types — greatest fixpoints, the dual of [`crate::generate`].
//!
//! ## What this delivers
//!
//! A sound, kernel-checked **destructor/coiteration** presentation of coinductive
//! types. Where an inductive is given by its *constructors* and eliminated by a
//! *recursor*, a coinductive `S` is given by its **destructors** (observations) and
//! *introduced* by a **corecursor** `S.corec` (the `unfold`/coiteration primitive).
//! They are precise categorical duals: an inductive is the **initial algebra** of its
//! signature functor, a coinductive is the **final coalgebra** of its destructor
//! functor.
//!
//! ### Example: `Stream A`
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
//!   function `X → R`; it cannot itself observe the coinductive it is building (it only
//!   sees the carrier `X`), so it can never force an unbounded chain of unfoldings.
//!
//! Because `S.corec` always terminates after producing one head layer, the ν-rules are
//! **weakly normalizing on observations**: `whnf` of any finite composition of
//! observations halts. Non-productive loops (the adversarial case) are *inexpressible*,
//! not merely rejected — see the crate tests.
//!
//! ## Supported form (the exact restriction)
//!
//! * **Non-indexed** coinductives with **uniform parameters** only (`Stream A`,
//!   `Colist A`, `Conat`, a bisimulation-friendly `Machine`, …). No index telescope.
//! * The former's type is `Π params. Sort s`.
//! * Each destructor has type `Π params. S params → R` where `R` (under `[params,
//!   scrutinee]`) is **either**
//!     - a **plain** result: it mentions neither `S` nor the scrutinee variable — a fixed
//!       observation type expressed in the parameters (`Stream.head : … → A`), **or**
//!     - a **corecursive** result: exactly `S params` (`Stream.tail : … → Stream A`).
//!   Anything else (a nested/functional/`S`-mentioning result other than `S params`) is
//!   **rejected** — conservative, keeping the corecursor's coalgebra signature first-order
//!   and the ν-rules sound.
//! * A coinductive must have **≥1 destructor** (otherwise nothing is observable, and the
//!   type is a useless unit; we reject the degenerate empty case).

use crate::check::Checker;
use crate::env::{Coinductive, CorecRule, Corecursor, Decl, Destructor, Env};
use crate::generate::{fold_pis, mk_var, occurs, peel_pis};
use crate::level::Level;
use crate::term::{Name, Term};
use std::collections::HashMap;
use std::rc::Rc;

/// A destructor in a high-level coinductive specification.
pub struct DtorSpec {
    pub name: Name,
    /// The destructor's type: `Π params. S params → R`.
    pub ty: Term,
}

/// A high-level coinductive specification handed to [`declare_coinductive`].
pub struct CoindSpec {
    pub name: Name,
    /// Universe parameters of the coinductive itself (the corecursor's carrier
    /// universe is added separately by the elaborator).
    pub num_levels: u32,
    /// The type former's type: `Π params. Sort s`.
    pub ty: Term,
    pub num_params: usize,
    pub dtors: Vec<DtorSpec>,
    /// Name to give the generated corecursor (e.g. `"Stream.corec"`).
    pub corec_name: Name,
}

/// The classified result type of a destructor.
enum ResultKind {
    /// A fixed observation type `R` (mentions neither `S` nor the scrutinee); carried in
    /// the *param-only* context `[params]` (scrutinee binder already removed as unused).
    Plain(Term),
    /// A corecursive observation: the result is exactly `S params`.
    Corecursive,
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

    // 1. Type-check the former and split into params / result sort. No indices allowed.
    {
        let chk = Checker::new(env);
        chk.infer_closed(&ty).map_err(|e| format!("type former '{name}': {e}"))?;
    }
    let (param_doms, after_params) =
        peel_pis(ty.clone(), k).ok_or_else(|| format!("'{name}' has fewer than {k} parameters"))?;
    match &after_params {
        Term::Sort(_) => {}
        other => {
            return Err(format!(
                "coinductive '{name}' must be `Π params. Sort _` (no indices supported), \
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
            dtors: dtor_names.clone(),
            corecursor: corec_name.clone(),
        })),
    )?;

    // 2. Check every destructor and classify its result.
    //    Destructor type must be `Π params. (S params) → R`.
    let mut results: Vec<ResultKind> = Vec::with_capacity(dtors.len());
    for d in &dtors {
        {
            let chk = Checker::new(env);
            chk.infer_closed(&d.ty).map_err(|e| format!("destructor '{}': {e}", d.name))?;
        }
        let (dparams, rest) = peel_pis(d.ty.clone(), k)
            .ok_or_else(|| format!("destructor '{}' has fewer than {k} parameters", d.name))?;
        let _ = dparams;
        // rest must be `S params → R` : a single Π whose domain is `S params`.
        let (scrut_dom, result) = match rest {
            Term::Pi(_, dom, cod) => ((*dom).clone(), (*cod).clone()),
            other => {
                return Err(format!(
                    "destructor '{}' must be `Π params. {name} params → R`, found {other:?}",
                    d.name
                ))
            }
        };
        // The scrutinee domain must be exactly `S params` (params = Var(k-1)…Var(0)).
        if !is_ind_params(&name, k, &scrut_dom, 0) {
            return Err(format!(
                "destructor '{}' must take `{name} params` as its scrutinee",
                d.name
            ));
        }
        // Classify the result, which lives under `[params, scrutinee]` (scrutinee = Var(0)).
        if is_ind_params(&name, k, &result, 1) {
            results.push(ResultKind::Corecursive);
        } else {
            // Plain: must mention neither S nor the scrutinee variable Var(0).
            if occurs(&name, &result) {
                return Err(format!(
                    "destructor '{}' result mentions '{name}' in an unsupported position \
                     (only a bare `{name} params` corecursive result is allowed)",
                    d.name
                ));
            }
            if mentions_var(&result, 0) {
                return Err(format!(
                    "destructor '{}' result depends on the observed value; only fixed \
                     (parameter-expressed) observation types are supported",
                    d.name
                ));
            }
            // Drop the (unused) scrutinee binder: re-express `R` in the param-only context.
            let plain = result.lift(-1, 1);
            results.push(ResultKind::Plain(plain));
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
                corecursive: matches!(results[i], ResultKind::Corecursive),
            })),
        )?;
    }

    // 4. Synthesize the corecursor type:
    //      S.corec.{levels, v} : Π params. Π (X : Sort v).
    //          Π (step_d : Π (x:X). R_d[X/S]) …  Π (seed : X). S params
    //    Universe: the carrier `X : Sort v` gets a fresh universe parameter `v` at
    //    index `num_levels` (so `S.corec` has `num_levels + 1` level params).
    let carrier_u = Level::param(num_levels);
    let corec_levels = num_levels + 1;

    // `S params` at context depth `depth`, with params at absolute levels `0..k`.
    let ind_app = |depth: usize| -> Term {
        let mut t = Term::cnst(name.clone(), ind_levels.clone());
        for j in 0..k {
            t = Term::app(t, mk_var(depth, j));
        }
        t
    };

    // Step domains. The carrier `X` sits at absolute level `k` (right after params).
    // Step `d` sits at absolute level `k + 1 + d`. Each step is `Π (x:X). R_d'`:
    //   - Plain(R): `R` lives in `[params]`; here params are still at levels 0..k, and we
    //     add the `x:X` binder, so lift R past (the X binder + the d preceding steps +
    //     one for x). Concretely at the point of R's body the depth is k+1+d+1.
    //   - Corecursive: `X`, i.e. a reference to the carrier at level k.
    let mut step_doms: Vec<Term> = Vec::with_capacity(dtors.len());
    for (d, res) in results.iter().enumerate() {
        // Depth just before the step-d binder: params(k) + X(1) + prior steps(d).
        let d0 = k + 1 + d;
        // `X` as the step's domain (the carrier variable at level k).
        let dom_x = mk_var(d0, k);
        // Under `x:X`, depth is d0+1; the carrier is still at level k.
        let cod = match res {
            ResultKind::Corecursive => mk_var(d0 + 1, k), // next state : X
            ResultKind::Plain(r) => {
                // `r` is in context `[params]`, so its only free variables are the params
                // at de Bruijn indices `0..k`. Re-expressing it under the `1 + d + 1` new
                // binders inserted *above* the params (X, the d prior steps, and x) shifts
                // every free variable up by that amount — a lift with cutoff 0.
                r.lift((1 + d + 1) as isize, 0)
            }
        };
        step_doms.push(Term::pi(dom_x, cod));
    }

    // seed domain: `X` (carrier at level k), at depth k + 1 + num_dtors.
    let d_seed = k + 1 + dtors.len();
    let seed_dom = mk_var(d_seed, k);

    // conclusion: `S params`, at depth k + 1 + num_dtors + 1.
    let d_concl = d_seed + 1;
    let concl = ind_app(d_concl);

    // Assemble: params, X, steps…, seed ⟶ S params.
    let mut all_doms = param_doms.clone();
    all_doms.push(Term::Sort(carrier_u)); // X : Sort v
    all_doms.extend(step_doms);
    all_doms.push(seed_dom);
    let corec_ty = fold_pis(&all_doms, concl);

    // 5. ν-rules: one per destructor. step_d is at spine position k + 1 + d.
    let mut rules: HashMap<Name, CorecRule> = HashMap::new();
    for (d, dspec) in dtors.iter().enumerate() {
        rules.insert(
            dspec.name.clone(),
            CorecRule {
                dtor: dspec.name.clone(),
                step_index: k + 1 + d,
                corecursive: matches!(results[d], ResultKind::Corecursive),
            },
        );
    }

    env.insert(
        corec_name.clone(),
        Decl::Corecursor(Rc::new(Corecursor {
            num_levels: corec_levels,
            ty: corec_ty,
            coind: name.clone(),
            num_params: k,
            num_dtors: dtors.len(),
            rules,
        })),
    )?;

    Ok(())
}

/// Is `t` (in a context of `depth` extra binders above the params) exactly the
/// coinductive `name` applied to the `k` uniform parameters `Var(depth+k-1) … Var(depth)`?
fn is_ind_params(name: &str, k: usize, t: &Term, depth: usize) -> bool {
    let (head, args) = t.unfold_apps();
    match head {
        Term::Const(h, _) if &*h == name => {
            if args.len() != k {
                return false;
            }
            // args[j] must be Var(depth + k - 1 - j): the j-th param, seen `depth` binders in.
            args.iter()
                .enumerate()
                .all(|(j, a)| matches!(a, Term::Var(i) if *i == depth + k - 1 - j))
        }
        _ => false,
    }
}

/// Does `t` mention the bound variable at de Bruijn index `k`? (Local copy of the
/// predicate in [`crate::term`], which is private there.)
fn mentions_var(t: &Term, k: usize) -> bool {
    match t {
        Term::Var(i) => *i == k,
        Term::App(f, a) => mentions_var(f, k) || mentions_var(a, k),
        Term::Lam(d, b) | Term::Pi(_, d, b) => mentions_var(d, k) || mentions_var(b, k + 1),
        Term::Let(t, v, b) => {
            mentions_var(t, k) || mentions_var(v, k) || mentions_var(b, k + 1)
        }
        Term::Sort(_) | Term::Const(..) | Term::Meta(_) => false,
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
    use crate::generate::{declare_inductive, nat_spec};
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
        declare_inductive(&mut env, nat_spec()).unwrap();
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
        declare_inductive(&mut env, nat_spec()).unwrap();
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
        declare_inductive(&mut env, nat_spec()).unwrap();
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
}
