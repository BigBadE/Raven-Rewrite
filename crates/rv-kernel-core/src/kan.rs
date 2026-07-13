//! **Phase 3** of the cubical build: the Kan operations — `transp` (transport along
//! a line of types) and `hcomp` (homogeneous composition, filling an open box).
//! Read `crate::cubical` (the interval `I`, `Path`/`PathP`, Phase 1) and
//! `crate::face` (cofibrations, `Sys`/`Partial`, Phase 2) first.
//!
//! # This phase ships a deliberately MINIMAL sound core
//!
//! This is the soundness-critical phase: the Kan operations define how types
//! *compute* under composition, and a wrong computation rule silently makes the
//! checker inconsistent (a derivable `Empty`/`False`). Real cubical type theory
//! (Cohen–Coquand–Huber–Mörtberg, "Cubical Type Theory: a constructive
//! interpretation of the univalence axiom") defines `transp`/`comp` by structural
//! recursion on the type former (`Π`, `Σ`, `PathP`, `Glue`, inductives, …), and the
//! `Π` case is **contravariant**: transporting a function's *argument* backwards
//! requires reversing the direction of the interval line (in CCHM this is the `~`
//! De Morgan connective; Cartesian systems without connections instead need a
//! *generalized* `coe`, parameterized by two arbitrary interval endpoints `r → r'`,
//! not just the fixed `i0 → i1` this task specifies).
//!
//! **This kernel's Phase 1 deliberately chose a Cartesian interval with no
//! De Morgan connectives** (see `crate::cubical`'s module doc, "Which interval").
//! That was the right call for Phase 1 (no Kan operations needed them yet), but it
//! means the textbook `Π`/`PathP` transport rules **cannot be written down here
//! without either (a) adding De Morgan reversal — a nontrivial, its-own-soundness-
//! burden extension explicitly out of scope for this pass, or (b) generalizing
//! `transp` to two arbitrary endpoints — a substantially larger redesign than "add
//! transp/hcomp to the existing i0→i1-only `Term::Transp`/`Term::HComp`". Neither is
//! achievable *and independently, adversarially soundness-checked* in this pass.
//!
//! Per the task's own instruction — "if the composition rules cannot be made
//! demonstrably sound within this pass, implement the largest sound subset (or
//! nothing), and report honestly" — this phase ships exactly the subset that
//! **is** demonstrably sound, and defers the rest. Concretely:
//!
//! * **`transp`** ([`crate::term::Term::Transp`]): only the **regularity rule** —
//!   transport along a family that is *structurally* independent of the interval
//!   variable is the identity. **No** per-type-former (Π/Σ/PathP) filling rule is
//!   implemented; a `transp` along a genuinely-varying family simply stays stuck
//!   (valid, inert data — like a neutral variable), rather than being given a
//!   wrong or partial computation rule.
//! * **`hcomp`** ([`crate::term::Term::HComp`]): only the **trivial-system rule** —
//!   when the guard `φ` is *decided* `⊤`, the composite is the system's value at
//!   `i1`. `hcomp`'s type argument is a single **fixed** type (not a family), so
//!   there is no Π/Σ/PathP-composition case to speak of here either — real cubical
//!   `hcomp` doesn't need one for a non-varying type; that structural recursion is
//!   only needed once `hcomp` is generalized to compose along a varying family
//!   (`comp`), which is explicitly deferred (see below).
//! * **`J`/derived `transport`/`subst`-based rewriting are NOT implemented** in
//!   this pass. The standard connection-free constructions of `J` from
//!   `transp`+`hcomp` (e.g. via contractibility of the based path space, built
//!   using an `hcomp`-filled square) are themselves delicate cubical arguments
//!   that this crate's own tests would need to adversarially re-derive to trust —
//!   attempting that construction on top of an admittedly-partial `transp` (no
//!   Π/PathP case) is exactly the kind of "ship something you can't stand behind"
//!   this task explicitly warns against. **Deferred, not shipped.**
//!
//! This is a real, if narrow, payoff: the regularity rule alone already gives
//! `Path`'s `refl`/`funext`/`ap` (Phase 1) a genuine (if restricted) computational
//! transport — `transp (λ_. A) φ a` is the identity, checked and adversarially
//! tested below — and every well-formedness/erasure/unification pass in the
//! untrusted elaborator (`rv-kernel`) now knows how to structurally traverse the
//! two new term formers, so a later pass can extend the *reduction* rules (in
//! `reduce.rs`/`nbe.rs` only) without another crate-wide plumbing pass.
//!
//! # A soundness bug caught and fixed *during* this pass
//!
//! An earlier draft of this phase additionally fired `transp`'s identity rule
//! whenever `φ` was *decided* `⊤` (mirroring `hcomp`'s trivial rule, and a literal
//! reading of the task's phrasing "whenever φ = ⊤, transp is the identity"). **This
//! is unsound** and was reverted before landing: `φ` is bookkeeping metadata
//! checked only for well-formedness (`Checker::infer`'s `Term::Transp` arm calls
//! `check_cof_wellformed`, nothing else) — it is never required to actually
//! *entail* that `family` is constant. Concretely, given an (entirely legal, if
//! perhaps individually inconsistent — no different from any other axiom) axiom
//! `p : Path (Sort n) A B` for two distinct closed types `A`/`B`, the family
//! `family := p @ Var(0)` genuinely varies (`family[i:=i0] ≡ A`, `family[i:=i1] ≡
//! B`, by the Phase-1 `path_boundary` rule) yet is a perfectly well-typed line of
//! types. `transp family ⊤ a` for `a : A` would then — under the *now-reverted*
//! rule — reduce straight to `a`, while `Checker::infer` independently reports its
//! type as `family[i:=i1] ≡ B`: a value of (real, checked) type `A` masquerading,
//! by a wrong reduction rule, as a value of type `B`. That is precisely the kind
//! of silent inconsistency this task's priorities rank above all else. The fix:
//! **the reduction rule never consults `φ`** — only the purely structural
//! `!mentions_var(family, 0)` check fires the identity rule (see the adversarial
//! test [`kernel_tests::transp_along_a_type_level_path_axiom_does_not_smuggle_a_type_change`]
//! below, which pins exactly this scenario down as "stays stuck", not "wrongly
//! reduces"). `hcomp`'s `φ = ⊤` rule has **no** analogous problem and was kept
//! as-is — see the soundness argument below for why.
//!
//! # Soundness argument
//!
//! ## `transp`'s regularity rule is sound
//!
//! `Checker::infer`'s `Term::Transp(family, φ, a)` arm requires `a : family[i:=i0]`
//! and reports the result type as `family[i:=i1]`. The **only** reduction rule
//! (`reduce::Reducer::whnf`/`nbe::Nbe::eval`, differentially tested) fires when
//! `family` does not mention the bound interval variable at all
//! (`!mentions_var(family, 0)`, a purely syntactic check on the *raw*, unevaluated
//! term). [`Term::subst`]'s own definition makes this airtight: substituting *any*
//! replacement for `Var(0)` in a term that contains no free `Var(0)` occurrence
//! never actually touches the replacement value — every other free variable is
//! simply shifted down by one, identically regardless of what's being substituted
//! in. So when the rule fires, `family[i:=i0]` and `family[i:=i1]` are not merely
//! *convertible* — they are the **literal same term** (both equal "`family` with
//! its free variables shifted down by one"). Consequently `a`'s checked type
//! (`family[i:=i0]`) and the `Transp` node's inferred type (`family[i:=i1]`) are
//! syntactically identical whenever the rule can fire, so reducing to `a` never
//! changes what type the result is considered to have. When `family` *does*
//! mention the interval variable, the term simply never reduces (stays stuck, a
//! valid normal form, exactly like an unresolved `Sys`) — this cannot manufacture
//! any new equation, for the same reason Phase 2's stuck `Sys` can't (see
//! `crate::face`'s soundness argument, point 3).
//!
//! ## `hcomp`'s trivial-system rule is sound
//!
//! `Checker::infer`'s `Term::HComp(ty, φ, u, u0)` arm type-checks `u` (under an
//! interval binder) against `Partial φ ty` **with `ty` held fixed** — this
//! minimal `hcomp` is *homogeneous* in the strongest sense: it does not even
//! accept a *family* of types, only one fixed `ty`, so there is no `A(i0)` vs
//! `A(i1)` mismatch to worry about in the first place (contrast `transp`, which
//! risked exactly that and is why its `φ=⊤` shortcut was unsound). It additionally
//! requires the cap agreement `u[i:=i0] ≡ u0` **unconditionally** (not only when
//! `φ` holds — a strictly *stronger*, and hence still-sound, requirement than the
//! textbook rule, at the cost of accepting fewer programs). The one reduction
//! rule fires only when `φ` is *decided* `⊤` (`crate::face::is_true`, the same
//! decision procedure Phase 2's `Sys` reduction already trusts), producing
//! `u[i:=i1]`. By the admissible substitution property of a checked derivation
//! (if `Γ, i:I ⊢ u : Partial φ ty` then `Γ ⊢ u[i:=r] : Partial φ[i:=r] ty` for any
//! well-typed `r : I` — an ordinary substitution lemma, not something this phase
//! introduces) `u[i:=i1]` is exactly as well-typed as `u` was; and since `ty`
//! never varies, there is no former-specific filling needed to land back at `ty`.
//! Every attempt to construct a counterexample (see the adversarial tests below,
//! in particular routing an *opaque* `Partial`-typed axiom through `u`) is blocked
//! by the *combination* of the independent `check(u0, ty)` and
//! `is_def_eq(u[i:=i0], u0)` obligations, both already-sound primitives.
//!
//! ## Neither rule adds a new source of equations between unrelated closed terms
//!
//! The structural `compare`/`is_def_eq`/`conv` cases added for `Transp`/`HComp`
//! (in `check.rs`/`reduce.rs`/`nbe.rs`) are exactly as conservative as Phase 1/2's
//! (component-wise structural equality, `φ` up to `crate::face::cof_equiv`) — they
//! can only equate two `Transp`/`HComp` nodes that already agree on every
//! component, never a `Transp`/`HComp` with an unrelated term.
//!
//! # What's deferred (explicitly, and why)
//!
//! * **Per-type-former `Π`/`Σ`/`PathP` transport/composition.** Blocked by the
//!   Cartesian-interval design (see above) for `Π` specifically; `Σ`/`PathP` are
//!   in principle derivable without reversal (covariant), but implementing *only*
//!   those without `Π` would produce an asymmetric, easy-to-misuse partial
//!   feature (transport works through half your type formers and silently
//!   doesn't through the other half) for a single-pass addition that couldn't
//!   also get the adversarial scrutiny this task demands — deferred as a unit.
//! * **`comp`** (composition along a *varying* family) — needs the same
//!   per-former recursion as `transp`'s general case, so inherits the same block.
//! * **`J`, derived `transport : Path Type A B -> A -> B`, `subst`-based
//!   rewriting.** All standard derivations route through either the general
//!   `Π`/`PathP` Kan rules or an hcomp-filled square whose own well-typedness
//!   argument this crate would need to re-derive from scratch — deferred rather
//!   than risking an under-scrutinized "payoff" construction.
//! * **`Glue`/univalence, De Morgan connections, Kan ops for user inductives/HITs**
//!   — out of scope for this task already, unaffected by this phase.
//!
//! None of this is wired to look complete: `Term::pretty` renders `transp`/`hcomp`
//! plainly, erasure (`rv_kernel::erase`) explicitly *errors* rather than silently
//! treating them as opaque (see `erase.rs`'s `Term::Transp | Term::HComp` arm),
//! and this module's doc is the single place documenting exactly how far the
//! implementation goes.

// ============================================================================
// Phase 3.6: the `Π`-case `transp` filling rule.
// ============================================================================
//
// Phase 3 (above) shipped only `transp`'s **regularity** rule — a real, but narrow,
// payoff. Phase 3.5 (`crate::cubical`) then added the De Morgan interval
// (`~`/`∧`/`∨`, with `normalize_interval` deciding the free De Morgan algebra
// definitionally). That connective structure is exactly the missing piece the
// module doc above flagged as blocking the `Π` rule: with `~`/`∧`/`∨` in hand, a
// **generalized coercion** `coe^{i.A}_{r→r'}` — CCHM's own device for expressing
// "transport along an *arbitrary* pair of interval endpoints" — becomes expressible
// *without* adding a new primitive, purely as a De Morgan reparametrization of the
// **existing**, fixed-direction (`i0→i1`) [`crate::term::Term::Transp`]:
//
// ```text
//   coe^{i.A}_{r→r'}(a) := transp (λ k. A[i := (r ∧ ~k) ∨ (r' ∧ k)]) φ a
// ```
//
// Check the two boundaries (using the bounded-lattice laws `crate::cubical` already
// proves definitional): at `k=i0`, `(r∧~i0)∨(r'∧i0) = (r∧i1)∨(r'∧i0) = r∨i0 = r`;
// at `k=i1`, `(r∧~i1)∨(r'∧i1) = (r∧i0)∨(r'∧i1) = i0∨r' = r'`. So the reparametrized
// family's `i0`/`i1` boundaries are exactly `A[i:=r]`/`A[i:=r']` — precisely what
// the *existing*, unmodified `transp` primitive (fixed at `i0→i1`) needs to
// transport `a : A[i:=r]` to a value of `A[i:=r']`. `φ` is passed as `⊤`
// (`Cof::top()`): per this crate's own — already adversarially established —
// convention (see the module doc above, "a soundness bug caught and fixed during
// this pass"), the `Transp` reduction rule **never consults `φ`**, so its value is
// irrelevant to what the term computes to; `⊤` is simply always a well-formed
// cofibration, so it's the natural placeholder.
//
// [`coe`] implements exactly this (as a *term-building* helper, not a value/eval
// one — see below for why that's the right layer). The one piece of bookkeeping it
// needs beyond ordinary substitution is [`crate::term::Term::subst_ctx_keep_frame`]:
// building `A[i := (r∧~k)∨(r'∧k)]` swaps `A`'s own interval binder `i` for a fresh
// one `k` of the *same* De-Bruijn "width" (both are exactly one `I`-classified
// binder around the same ambient context) — an ordinary [`Term::instantiate`] would
// instead *eliminate* the binder outright (shrinking every other free variable's
// index by one), which is wrong here: `k` needs to stay bound, not be eliminated.
// See that method's doc comment for the full index bookkeeping argument.
//
// # The `Π` computation rule
//
// Given `transp (λ i. Π(g:A i). B i x) φ f0` — `A` living under the transp's own
// interval binder (`Var(0) = i`), `B` living under that *and* the `Π`'s domain
// binder (`Var(0) = x`, `Var(1) = i`) — CCHM's rule is:
//
// ```text
//   transp (λi. Πx:A(i). B i x) φ f0
//     ↦ λ (x1 : A i1).
//         let x̄ := λ j. coe^{i.A}_{i1→j}(x1)     -- backward (contravariant) transport
//                                                    of the argument: from i1 down to
//                                                    any j, so x̄(i0) is the argument at
//                                                    the *source* side f0 expects.
//         in coe^{i. B i (x̄ i)}_{0→1}( f0 (x̄ i0) )  -- forward transport of the result.
// ```
//
// Two observations simplify the implementation:
//
// 1. The **inner** `coe` (building `x̄`) has an *arbitrary* target endpoint (`i1→j`
//    for varying `j`), so it genuinely needs the general reparametrization above.
// 2. The **outer** `coe` transports `0→1` — **exactly** the primitive `Transp`'s own
//    fixed direction — so it needs *no* reparametrization at all; it is literally
//    `Term::transp(λi. B i (x̄ i), ⊤, f0 (x̄ i0))`, built directly.
//
// [`transp_pi_rule`] builds exactly this term (a `Lam` wrapping one nested
// `Transp`), and is called from both [`crate::reduce::Reducer::whnf`] and
// [`crate::nbe::Nbe::eval`]'s `Term::Transp` arms (after the existing regularity
// check, when the family's head is *syntactically* — no `whnf` — a literal
// [`crate::term::Term::Pi`]; see those call sites' doc comments for why syntactic
// matching, matching the existing regularity rule's convention, is the deliberately
// conservative choice here). Being a pure `Term → Term` builder (not
// `Value`-specific) lets `nbe::Nbe::eval` simply hand the built term to `self.eval`
// under the *same* `venv` the stuck computation would have used — the construction
// introduces no new *free* variable (every fresh binder it creates, `x1`/`i2`/`k`,
// is bound *within* the term it builds), so this is exactly as sound as evaluating
// any other freshly-substituted subterm.
//
// # Soundness
//
// This rule adds **no new axiom or primitive** — it is a derived rewriting of
// `Transp` into more `Transp`/`Lam`/`App` nodes, each of which is independently
// re-typechecked by this crate's existing, unmodified `Checker::infer` (the
// `Term::Transp` arm requires `a : family[i:=i0]` and reports `family[i:=i1]`,
// exactly as before — this phase adds no new *checking* rule at all, only a new
// *reduction*). Three things must hold for that to be safe:
//
// 1. **The reduction is type-preserving.** The built `Lam(A(i1), body)` must have
//    type `family[i:=i1] = Πx:A(i1). B(i1,x)`, matching the *unmodified* `infer`
//    result for the original `Transp` node (`Checker::infer` never even looks at
//    which *reduction* rule fired — subject reduction is what must hold). `body`,
//    under `x1 : A(i1)`, must have type `B(i1, x1)`.
//    - `f0 (x̄ i0)` — `f0 = a0 : A(i0) → B(i0,·)` (the *original* checked premise,
//      `a0 : family[i:=i0]`), applied to `x̄ i0 = coe^{i.A}_{i1→i0}(x1) : A(i0)`
//      (`coe`'s own boundary computation above gives exactly this, with `r=i1`,
//      `r'=i0`) — has type `B(i0, x̄ i0)`.
//    - The outer `Transp(λi. B i (x̄ i), ⊤, f0(x̄ i0))` then transports that
//      `B(i0, x̄ i0)`-typed term along `family := λi. B i (x̄ i)` — whose `i0`
//      boundary is *exactly* `B(i0, x̄ i0)` (by construction: substituting `i:=i0`
//      into `B i (x̄ i)` gives `B(i0, x̄(i0))` verbatim) — landing at `family[i:=i1]
//      = B(i1, x̄ i1)`. And `x̄ i1 = coe^{i.A}_{i1→i1}(x1)`, whose own `i0`/`i1`
//      boundaries (by the *same* boundary computation, now with `r=r'=i1`) are both
//      `A(i1)` — i.e. `x̄ i1` is (up to conversion, `family[i:=i1]` unfolding the
//      same way regardless of `r=r'`'s common value) exactly `x1`'s type, so
//      `B(i1, x̄ i1) ≡ B(i1, x1)`, the target. This is the textbook CCHM argument,
//      re-derived structurally here rather than assumed.
// 2. **Every produced subterm independently re-typechecks** — this is not merely
//    argued, it is *tested*: [`kernel_tests::transp_pi_rule_transports_a_concrete_function`]
//    below builds a concrete instance, reduces it, and re-runs `Checker::infer` on
//    the reduced normal form from scratch (the same "independent recheck" discipline
//    this crate uses everywhere else), confirming the built term's *inferred* type
//    (not just the *original* `Transp` node's) matches `family[i:=i1]`.
// 3. **No new equation between unrelated closed terms is introduced.** The rule
//    only ever *rewrites* one term into another via ordinary substitution
//    (`subst_ctx_keep_frame`/`instantiate`/`lift`, all pre-existing, independently
//    tested primitives) and re-wraps the pieces in `Transp`/`Lam`/`App` — it never
//    invents a value or asserts a boundary that isn't *computed* from the family
//    and argument already supplied. In particular the regularity rule (checked
//    *first*, unconditionally — see the call sites) still governs the *constant*
//    case, so this rule can only ever fire in addition to, never instead of, that
//    already-proven-sound path; [`kernel_tests::transp_pi_rule_agrees_with_regularity_on_a_constant_pi_family`]
//    pins this consistency down directly. The anti-`False` attack from the module
//    doc above (a type-level path axiom smuggling a type change) is re-run through
//    the `Π` case specifically in
//    [`kernel_tests::transp_pi_rule_does_not_smuggle_a_type_change_through_a_function`].

use crate::env::{Decl, Env};
use crate::face::Cof;
use crate::term::{mentions_var, Term};

/// `coe^{i.dom}_{r→r'}(a)` (see the module doc's "Construction" section): transport
/// `a` (of type `dom[i:=r]`) along the line `dom` (living under one interval
/// binder, `Var(0) = i`, over some ambient context) from `r` to `r'` (both living in
/// that *ambient* context — no `i` in scope), producing a term of `dom[i:=r']`.
/// Built as a reparametrized instance of the existing, fixed-direction
/// [`Term::transp`] via the De Morgan connections `∧`/`∨`/`~` — see the module doc
/// for the boundary computation that makes this valid.
pub(crate) fn coe(dom: &Term, r: &Term, r_prime: &Term, a: &Term) -> Term {
    // `conn`, living under a *fresh* interval binder `k` over the same ambient
    // context as `r`/`r'` (hence `r`/`r'` are lifted by one to sit under it):
    // `(r ∧ ~k) ∨ (r' ∧ k)`.
    let conn = Term::ijoin(
        Term::imeet(r.lift(1, 0), Term::ineg(Term::Var(0))),
        Term::imeet(r_prime.lift(1, 0), Term::Var(0)),
    );
    // Swap `dom`'s own interval binder for `k`, substituting `conn` for every
    // occurrence — `subst_ctx_keep_frame` (not `instantiate`) because this must
    // *keep* one interval binder in place (now meaning `k`, not `i`), not eliminate
    // it (see that method's doc comment).
    let reparam = dom.subst_ctx_keep_frame(&[conn]);
    Term::transp(reparam, Cof::top(), a.clone())
}

// ============================================================================
// Normalization-aware regularity: closing the `refl`-computation completeness gap.
// ============================================================================
//
// The regularity rule above (`!mentions_var(fam, 0)`, checked at the call sites in
// `crate::reduce::Reducer::whnf` and `crate::nbe::Nbe::eval`) is *purely syntactic*:
// it inspects the family's raw, un-reduced structure. This misses the extremely
// common case where the family is only *definitionally*, not *syntactically*,
// independent of the interval variable — most importantly `transport (refl A) a`,
// `subst`/`J` at `refl` (see `crate::cubical`'s documented "Completeness gap" for the
// full account of why: e.g. `transport (refl A) a`'s family is `λi. (refl A) @ i =
// λi. PApp(PLam(A↑), Var(0))`, which *does* mention `Var(0)` syntactically — as the
// `PApp`'s argument — even though the family is, up to one β-step, the constant `A`.
//
// [`family_is_constant`] closes this gap the *sound* way: instead of trusting only
// the family's raw syntax, it fully **computes** the family (via `crate::nbe::Nbe`'s
// already-proven-sound evaluator/quoter — the same machinery `Checker::compare`/
// `Reducer::is_def_eq` trust for every other definitional-equality question in this
// kernel) under a *fresh, wholly opaque* neutral standing in for the interval
// variable, then re-runs the exact same structural `mentions_var` check on the
// **result**. This is a strictly larger, still fully sound, class than the original
// check:
//
// * **Soundness.** `mentions_var(normalize(fam), 0) == false` means the interval
//   variable's *fully computed, canonical* normal form contains no occurrence of the
//   fresh neutral standing in for it — i.e. `fam` evaluates to the *same* normal form
//   no matter what (well-typed) interval term is substituted for `Var(0)` (NbE's
//   normal forms are canonical: two terms differ only if they're not definitionally
//   equal). That is exactly "the family is constant, definitionally" — precisely the
//   hypothesis the original regularity rule's soundness argument (`crate::cubical`'s
//   and this module's own docs above) already rests on, just established by
//   computation instead of by inspecting raw syntax. No new axiom, no consultation of
//   `φ` (the probe never looks at it), no shortcut: firing this rule can only ever
//   collapse a `Transp` to its input `a` when the two really are related by an
//   honest, verifiable, computed identity of the whole line of types/values.
// * **The critical non-example still stays stuck.** For the `φ=⊤`/type-path-axiom
//   smuggle attack (`transp` along a *genuinely varying* `p : Path Type A B` axiom,
//   family `λi. p @ i` with `p` an opaque `Const`/`Var`, not a literal `PLam`): the
//   fresh neutral substituted for `Var(0)` propagates straight through the *opaque*
//   `PApp(p, ·)` head (nothing reduces it away — `p` has no `PLam`/`ι`-rule to fire,
//   it's neutral) and survives, unchanged, all the way into the quoted normal form —
//   so `mentions_var` on the result is still `true`, and the probe correctly refuses
//   to fire. See `kernel_tests::normalization_aware_regularity_does_not_smuggle_a_
//   type_change_through_an_axiomatized_path` below, which pins this down directly
//   (extending, not just re-running, the module's standing anti-`False` attack).
// * **Sizing, not a soundness knob.** `crate::term::free_var_bound(fam)` computes how
//   many free variables (beyond the interval binder itself) `fam` mentions, purely so
//   `Nbe::normalize_open` can hand each of them a distinct fresh neutral instead of
//   panicking on an out-of-range index — an over-generous bound is harmless (extra
//   unused fresh neutrals change nothing), it exists only to avoid a panic, and it
//   never influences *which* terms this function judges constant.
pub(crate) fn family_is_constant(env: &Env, fam: &Term) -> bool {
    // Fast path: the original, purely syntactic check — avoids paying for a full
    // evaluation/quote round-trip in the overwhelmingly common case (an already
    // syntactically-constant family, or a family that's obviously non-constant at
    // its very head, e.g. `Pi`/an inductive being transported pointwise).
    if !mentions_var(fam, 0) {
        return true;
    }
    // `fam` sits under one (not-yet-introduced) interval binder plus however many
    // ambient free variables it itself references (`Var(1)`, `Var(2)`, … beyond the
    // interval variable at `Var(0)`) — `free_var_bound` sizes the fresh-neutral
    // context so every one of them gets a binding.
    let depth = crate::term::free_var_bound(fam).max(1);
    let normalized = crate::nbe::Nbe::new(env).normalize_open(depth, fam);
    !mentions_var(&normalized, 0)
}

/// The `Π`-case `transp` filling rule (see the module doc's "The `Π` computation
/// rule"). `dom`/`cod` are the two components of the family's `Π` head (`dom` under
/// one interval binder, `cod` under that *and* the `Π`'s own domain binder — exactly
/// [`Term::Pi`]'s own binder convention, just nested one level deeper for the
/// transp's interval variable); `a0` is the transp's checked argument (of type
/// `family[i:=i0]`), living in the ambient context (no interval/`Π` binder). Returns
/// the reduced `Lam` term (one whnf step) — never partially applies/evaluates the
/// pieces beyond the substitutions the rule itself calls for.
pub(crate) fn transp_pi_rule(dom: &Term, cod: &Term, a0: &Term) -> Term {
    // The result's domain: `A(i1)`, in the ambient context (no binders at all).
    let dom_i1 = dom.instantiate(&Term::IOne);

    // `dom`, reindexed to live under the body's own frame `[x1, Γ]` (insert one
    // fresh slot for `x1` between `dom`'s own interval binder and the rest of its
    // ambient context `Γ`) — used to build `x̄`'s two concrete/instantiated uses.
    let dom_for_body = dom.lift(1, 1);
    // `x̄(i0) = coe^{i.A}_{i1→i0}(x1)`, living in `[x1, Γ]` (`x1 = Var(0)` there).
    let xbar_i0 = coe(&dom_for_body, &Term::IOne, &Term::IZero, &Term::Var(0));

    // `f0 (x̄ i0)`: `a0` (== `f0`) lifted into `[x1, Γ]`, applied to `x̄(i0)`.
    let f0_applied = Term::app(a0.lift(1, 0), xbar_i0);

    // `dom`, reindexed to live under the *second* transp's frame `[i2, x1, Γ]`
    // (insert two fresh slots, for `i2` and `x1`, between `dom`'s own interval
    // binder and `Γ`) — used to build `x̄(i2)`, the line `B i (x̄ i)` needs.
    let dom_for_newfam = dom.lift(2, 1);
    // `x̄(i2) = coe^{i.A}_{i1→i2}(x1)`, living in `[i2, x1, Γ]` (`i2 = Var(0)`,
    // `x1 = Var(1)` there).
    let xbar_i2 = coe(&dom_for_newfam, &Term::IOne, &Term::Var(0), &Term::Var(1));
    // `B i2 (x̄ i2)`: substitute `cod`'s own two binders (`x`, then `i`) with
    // `x̄(i2)` and `i2` respectively, *keeping* the frame (the result stays under
    // exactly one interval binder, `i2`, over `[x1, Γ]` — matching `Transp`'s own
    // `fam` convention) rather than eliminating them.
    let newfam = cod.subst_ctx_keep_frame(&[xbar_i2, Term::Var(0)]);

    // `coe^{i. B i (x̄ i)}_{0→1}(f0 (x̄ i0))` — the *outer* transport is already in
    // the primitive's own fixed `i0→i1` direction, so no reparametrization is
    // needed: build the `Transp` node directly.
    let body = Term::transp(newfam, Cof::top(), f0_applied);

    Term::lam(dom_i1, body)
}

// ============================================================================
// Phase 3.7: the `Π`-case `hcomp` filling rule.
// ============================================================================
//
// Per the module doc above, `hcomp`'s type argument is a single **fixed** type `A`
// (never a family), so there is no `A(i0)`-vs-`A(i1)` mismatch to reconcile the way
// `transp`'s `Π` case had to (no `coe`/De Morgan reparametrization needed at all
// here). CCHM's `Π`-case `hcomp` rule (Cohen–Coquand–Huber–Mörtberg §4.2) is simply
// "push the composition into the codomain pointwise":
//
// ```text
//   hcomp (Πx:A. B x) φ u u0
//     ↦ λ (x : A). hcomp (B x) φ (λ i. (u i) @ x) (u0 x)
// ```
//
// `A`/`B` are the (fixed, non-varying) domain/codomain of the fixed `Π` — no interval
// dependence anywhere in the type former itself, so there's no filling *of the type*
// to do; only the *system* `u` and the cap `u0` need to be pointwise-applied to the
// fresh domain variable `x`, and a fresh `hcomp` built at the (fixed) codomain `B x`.
//
// # Why the naive term `App(u_at_i, x)` doesn't typecheck here — and the fix
//
// `u`'s own checked type is `Partial φ (Πx:A.B x)` (`Checker::infer`'s `Term::HComp`
// arm: `check(u, Partial(φ,ty).lift(1,0))` under the interval binder) — `Partial` is
// a **distinct, non-reducible** type former in this kernel (see `crate::face`: unlike
// CCHM's own metatheory, where `Partial φ A`'s elements *are* ordinary elements of
// `A` merely "restricted" to `φ`, here `Partial` never β/ι-reduces to `A`, and the
// *only* way `Checker::check` accepts a term at a `Partial ψ A` type is (a) via the
// dedicated [`crate::check::Checker::check_sys`] path, when the term is *syntactically*
// a literal [`Term::Sys`], or (b) via the generic `infer`-and-compare fallback, which
// requires the term to *already infer* to `Partial ψ A` outright). So a bare
// `Term::App(u_at_i, x)` cannot be built as ordinary application: `Checker::infer`'s
// `Term::App` arm demands its function position `infer` to a literal `Π`, and nothing
// in this kernel makes a `Partial`-classified term whnf to one — there is no
// `Partial`-elimination/application primitive.
//
// The fix mirrors exactly the `Π`-case `transp` rule's own guiding discipline
// ("syntactic, conservative — match the concrete shape you can push through, else
// stay stuck"): **push the application through `u`'s branches directly**, which only
// makes sense — and only needs to be sound for — the one syntactic shape that
// actually inhabits a `Partial` type structurally: a literal [`Term::Sys`]. For
// `u = Sys [ψ_1 ↦ t_1, …, ψ_n ↦ t_n]` (each `t_k : Πx:A.B x`, an *ordinary*, fully
// fibrant `Π`-typed term — `Partial`'s "restriction" lives only in the guard, not in
// each branch's own type), pushing `@x` into every branch,
// `Sys [ψ_1 ↦ t_1 x, …, ψ_n ↦ t_n x]`, is **ordinary, unconditionally sound**
// application of each already-Π-typed branch — no new primitive, no new axiom, just
// `n` ordinary `App` nodes wrapped back in a `Sys` with the very same guards (whose
// coverage/compatibility obligations `crate::check::Checker::check_sys` re-derives
// from scratch on the *rebuilt* system, exactly as it would for any other `Sys`).
//
// [`hcomp_pi_rule`] therefore returns `Option<Term>`: `Some` only when `u` is
// *syntactically* (no `whnf`) a literal `Sys` — mirroring `transp_pi_rule`'s call
// sites, which only fire on a syntactically literal `Π` family — and `None`
// otherwise (e.g. `u` is a free/opaque `Partial`-typed neutral, or a `Sys` hidden
// behind a `Let`/`Const`). When `None`, the caller ([`crate::reduce::Reducer::whnf`]
// and [`crate::nbe::Nbe::eval`]) leaves the `hcomp` **stuck** — a real, but narrow and
// honestly-documented, incompleteness (not unsoundness): exactly the same posture
// `transp_pi_rule` already takes for a family that only *reduces* (rather than being
// syntactically) `Π`-headed.
//
// # Construction and index bookkeeping
//
// Given `dom`/`cod` (the fixed `Π`'s two components, in the *same* binder convention
// [`Term::Pi`] itself uses: `cod` under one extra binder for `Π`'s own domain variable
// `x`), `phi` (the outer guard, living in the ambient context `Γ`, no binders — the
// same frame `ty`/`u0` live in), and `u`'s branches `(ψ_k, t_k)` (each living in frame
// `[i, Γ]`, one interval binder — the same frame `u` itself lives in, per `Term::HComp`'s
// own convention):
//
// * **New guards** `ψ_k.lift(1,1)`: reindex from `[i,Γ]` to `[i,x,Γ]` (insert `x`
//   *under* `i`, i.e. at cutoff 1, so `i = Var(0)` stays put and everything from `Γ`
//   shifts up by one) — the same "insert a binder below an existing one" bookkeeping
//   [`transp_pi_rule`] uses for `dom.lift(1,1)` (see that function's doc).
// * **New branch bodies** `App(t_k.lift(1,1), Var(1))`: `t_k` reindexed the same way
//   (`[i,Γ] → [i,x,Γ]`), then applied to the fresh `x = Var(1)` in that frame.
// * **New line** `u' := Sys [ψ_1.lift(1,1) ↦ t_1.lift(1,1) x, …]`, living in frame
//   `[i,x,Γ]` — exactly `Term::HComp`'s own convention for its `u` field (one interval
//   binder over the *ambient* context, now `[x,Γ]`), so it slots directly into the
//   inner `hcomp` with no further wrapping.
// * **New guard** `phi.lift(1,0)`: `phi` has no binder of its own (frame `Γ`), so a
//   plain `lift(1,0)` reindexes it into `[x,Γ]`.
// * **New cap** `App(u0.lift(1,0), Var(0))`: `u0` (frame `Γ`) lifted into `[x,Γ]`,
//   applied to the fresh `x = Var(0)` there.
// * **Body**: `hcomp cod phi.lift(1,0) u' (u0.lift(1,0) x)`, living in frame `[x,Γ]` —
//   exactly the frame a `Lam(dom, body)`'s body is expected in.
//
// [`hcomp_pi_rule`] builds exactly this (one `Lam` wrapping one nested `HComp`, whose
// `u` field is the rebuilt `Sys`), analogous in shape to [`transp_pi_rule`]'s one `Lam`
// wrapping one nested `Transp`.
//
// # Soundness
//
// This rule adds **no new axiom or primitive** — like [`transp_pi_rule`], it is a
// pure rewriting of one `HComp` node into more `HComp`/`Sys`/`Lam`/`App` nodes, each
// independently re-typechecked by the existing, unmodified `Checker::infer`/`check_sys`
// (this phase adds no new *checking* rule at all, only a new *reduction*). The
// argument:
//
// 1. **Type preservation.** The original `HComp(Π x:A.B x, φ, u, u0)` node's checked
//    type is `Πx:A.B x` (`Checker::infer`'s `Term::HComp` arm always reports `ty`
//    unchanged, *regardless* of which reduction rule — if any — later fires; subject
//    reduction is what must hold, exactly as for `transp_pi_rule`). The built
//    `Lam(A, body)` has, by `Checker::infer`'s `Term::Lam` arm, type `Πx:A. (type of
//    body)`; `body = HComp(B x, φ', u', u0' x)` under `x:A` infers to `B x` by the
//    *very same*, unmodified `Term::HComp` arm — **provided** its three obligations
//    hold:
//    - `check_cof_wellformed(φ')`: `φ' = φ.lift(1,0)`, a purely structural reindexing
//      of an already-well-formed `φ` (every atom subject that was `: I` in `Γ` is
//      still `: I` after uniformly lifting past one new binder — an ordinary
//      weakening lemma, the same one every other binder-crossing rule in this file
//      already relies on, e.g. `transp_pi_rule`'s `dom.lift`/`cod.lift` uses).
//    - `check(u', Partial(φ',B x).lift(1,0))`: `u'` is *by construction* a literal
//      `Sys` of exactly the branches `check_sys` needs — coverage
//      (`entails(φ', ψ_1.lift(1,1) ∨ … ∨ ψ_n.lift(1,1))`) follows from the *original*
//      coverage (`entails(φ, ψ_1 ∨ … ∨ ψ_n)`, required by the original `HComp`'s own
//      `check(u, Partial(φ,ty).lift(1,0))` obligation) by the same structural
//      weakening lemma — lifting is a language-level renaming, so it commutes with
//      `∨`/`entails` exactly (`Cof::lift` is defined homomorphically over `And`/`Or`,
//      see `crate::face::Cof::lift`); each branch typechecks
//      (`App(t_k.lift(1,1), Var(1)) : B x`) because `t_k : Πx':A.B x'` (from the
//      *original* system's own `check(t_k, ty)` obligation, `ty = Πx:A.Bx`) applied to
//      `x` — ordinary, unconditional `Π`-application, giving `B x` by the standard
//      substitution lemma; and compatibility (branches agreeing on overlaps) follows
//      because `App(-, x)` is a *congruence* — if `t_i ≡ t_j` (the original
//      compatibility obligation) then `t_i x ≡ t_j x` (definitional equality is a
//      congruence for application, an existing, unmodified property of
//      `Checker::is_def_eq`/`compare`).
//    - Cap agreement `u'[i:=i0] ≡ u0'` (`u0' = App(u0.lift(1,0),Var(0))`): substituting
//      `i:=i0` into `u'` distributes over the rebuilt `Sys`'s branches (substitution is
//      structural on `Sys`), landing at `Sys[ψ_k.lift(1,1)[i:=i0] ↦ t_k.lift(1,1)[i:=i0]
//      x]`; since the *original* cap agreement (`u[i:=i0] ≡ u0`, an already-checked
//      obligation of the source `HComp`) forces `u[i:=i0]` and `u0` to be
//      definitionally equal *as terms of type* `ty = Πx:A.Bx`, applying the same
//      congruence (`App(-, x)` respects `≡`) gives `u[i:=i0] x ≡ u0 x`, i.e. exactly
//      `u'[i:=i0] ≡ u0'` after the frame reindexing (lift/subst commute in the
//      standard way — the same bookkeeping [`Term::subst_ctx_keep_frame`]'s own doc
//      derives for the analogous `Π`-case `transp` rule).
// 2. **Every produced subterm independently re-typechecks** — not merely argued:
//    [`kernel_tests::hcomp_pi_rule_transports_a_concrete_partial_function`] below
//    builds a concrete instance, reduces it, and re-runs `Checker::infer` on the
//    reduced normal form from scratch.
// 3. **Agreement with the trivial `⊤` rule.** Both [`crate::reduce::Reducer::whnf`]
//    and [`crate::nbe::Nbe::eval`] check `is_true(phi)` (the trivial rule) **first**,
//    unconditionally, before ever consulting `hcomp_pi_rule` — so the two rules never
//    *both* fire on the same term (no possible disagreement by construction, exactly
//    mirroring how `transp`'s regularity check is likewise always tried first). A
//    dedicated differential test
//    ([`kernel_tests::hcomp_pi_rule_agrees_with_the_trivial_rule_when_phi_is_top`])
//    confirms the *values* still agree (up to conversion, after applying both to a
//    concrete argument) even though only one rule's *reduction step* ever literally
//    fires.
// 4. **No new equation between unrelated closed terms.** The rule only ever rewrites
//    one term into another via ordinary substitution/reindexing and re-wraps the
//    pieces in `HComp`/`Sys`/`Lam`/`App` — it never invents a value or asserts an
//    equation not already forced by the source system's own (already-checked)
//    obligations. The anti-`False` attacks from the module doc above are re-run
//    through the `Π` case specifically in
//    [`kernel_tests::hcomp_pi_rule_cannot_conjure_an_inhabitant_of_an_unrelated_axiom`]
//    and [`kernel_tests::hcomp_pi_rule_does_not_conflate_branches_at_different_arguments`].

// ============================================================================
// Phase 3.8: the `PathP`-case `hcomp` filling rule — INVESTIGATED AND DECLINED.
// ============================================================================
//
// This section documents a rule that was **designed, precisely constructed, and
// then declined** after an adversarial re-typecheck showed it fails this crate's
// own soundness bar — per the standing instruction ("if you cannot make it
// demonstrably sound this pass, implement the largest sound subset (or nothing),
// and report honestly"). Nothing from this section is wired into
// `reduce.rs`/`nbe.rs`; `hcomp` at a `PathP` type stays stuck, exactly as before
// this pass (an honest incompleteness, not a silently-missing feature — see below
// for why "stuck" is the *only* sound option available right now).
//
// # The rule, as CCHM states it
//
// ```text
//   hcomp (PathP C a b) φ u u0
//     ↦  ⟨j⟩ hcomp (C j)
//                 ( φ ∨ (j=0) ∨ (j=1) )
//                 [ φ      ↦ (u i) @ j
//                 , (j=0)  ↦ a
//                 , (j=1)  ↦ b ]
//                 (u0 @ j)
// ```
//
// Mirroring [`hcomp_pi_rule`]'s own construction discipline (only fire on a
// *syntactically* literal `u : Term::Sys`, so its branches `t_k` are concrete and
// can be pushed through `@ j`), the natural translation into this crate's terms
// is: for `u = Sys [(ψ_1,t_1), …, (ψ_n,t_n)]` (each `t_k : PathP C a b`, frame
// `[i,Γ]`, `C` the fixed family living in frame `[j,Γ]` — exactly `PathP`'s own
// binder convention, matching a fresh `⟨j⟩` one-for-one), build:
//
// ```text
//   new_u  := Sys [ (ψ_1.lift(1,1), PApp(t_1.lift(1,1), Var(1))), …    -- tube, pushed through @j
//                 , (j=0,           a.lift(2,0))                       -- left endpoint face
//                 , (j=1,           b.lift(2,0)) ]                     -- right endpoint face
//   result := PLam( HComp(C, φ.lift(1,0) ∨ (j=0) ∨ (j=1), new_u, PApp(u0.lift(1,0), Var(0))) )
// ```
//
// (index bookkeeping — `lift(1,1)` inserting the fresh `j` binder below the new
// inner `hcomp`'s own interval binder, `lift(2,0)` inserting *both* fresh binders
// above the ambient context — mirrors [`hcomp_pi_rule`]'s own `lift(1,1)`/`lift(1,0)`
// conventions exactly, just with one extra binder since `PathP`'s `PLam` wraps
// *outside* the new `hcomp`'s own interval binder, unlike `Π`'s domain variable
// which sits *outside* the whole term).
//
// # Why this fails an independent re-typecheck — the compatibility gap
//
// The critical difference from the `Π` case: `Π` has **no boundary constraint** —
// `hcomp_pi_rule`'s rebuilt `Sys` only ever has the *original* `n` (reindexed)
// branches, so its compatibility obligations are exactly the *original* system's
// (already checked, `App(-,x)` being a congruence — see that rule's soundness
// argument, point 1). `PathP`, by contrast, injects **two brand-new branches**
// (`j=0 ↦ a`, `j=1 ↦ b`) that structurally **overlap** every tube branch
// (`ψ_k.lift(1,1) ∧ (j=0)` is essentially never `⊥` — `j` is a fresh variable
// unconstrained by any `ψ_k`, which never mentions it). [`crate::check::Checker::check_sys`]
// (see `check.rs`) requires every such overlap to satisfy **unconditional**
// `is_def_eq(t_i, t_j)` — a *purely structural/`whnf` comparison of the two raw
// branch terms *as they stand*, with no notion of "assuming the cofibration holds,
// substitute and then compare" (contrast the textbook cubical metatheory, where
// this compatibility is *semantic*, checked only "under" the face — i.e. after
// substituting the pinned interval variable). Concretely, that means the tube
// branch `PApp(t_k.lift(1,1), Var(1))` — a term that **genuinely, syntactically
// mentions the fresh, still-abstract path coordinate `j = Var(1)`** — would need to
// be `is_def_eq` to the *j-independent* endpoint term `a.lift(2,0)` **without ever
// substituting a concrete value for `j`**. The one existing mechanism that could
// help here, [`crate::check::Checker::path_boundary`] (see `check.rs`), is
// deliberately narrow: it only recognizes `p @ i0`/`p @ i1` for a **literal**
// `Term::IZero`/`Term::IOne` argument (see `crate::cubical`'s module doc, "the
// boundary equation also holds for neutral p") — it does *not*, and structurally
// *cannot*, fire for `p @ Var(1))` where `Var(1)` is an ordinary bound variable
// that merely *happens* to be pinned to `i0`/`i1` by an enclosing cofibration guard
// the compatibility check never consults.
//
// This is not a corner case avoidable by more careful construction — it is
// **structural**: the only way `PApp(t_k.lift(1,1), Var(1))` could be
// unconditionally `is_def_eq` to a `j`-independent term is if `t_k` is *itself*
// (syntactically, after whnf) a `PLam` whose body doesn't depend on its own bound
// variable at all (the `Π`-case rule's "regularity"-style degenerate case) — i.e.
// this would only ever fire for constant/`refl`-like paths, which is a useless
// subset of `PathP` (real cubical programs' `hcomp` fillers are essentially always
// non-constant paths — that's the entire point of composing them). For any
// **opaque** `PathP`-typed value (a free variable, an axiom, an unresolved
// application) — the overwhelmingly common case — the construction is rejected
// outright.
//
// **UPDATE (later pass):** this blocker has since been fixed at its root —
// `crate::check::Checker::check_sys`'s compatibility condition is now
// **restriction-aware** (see `crate::face::restrict_clause_term`'s doc): two
// overlapping branches need only agree *after* substituting the interval
// endpoints their overlap's DNF clauses force, exactly cubical type theory's
// "compatible system" condition, rather than the unconditional (symbolic)
// equality this section originally diagnosed as the blocker. The enlarged system
// this section describes now passes `check_sys` — see
// [`kernel_tests::hcomp_pathp_rule_enlarged_system_now_passes_restriction_aware_check_sys`]
// (the former `..._declined_naive_cchm_construction_fails_check_sys_compatibility`,
// repurposed to confirm acceptance). The rest of this section is kept as the
// historical diagnosis of *why* the old, unconditional check rejected it — still
// accurate as an account of the old rule — but the "declined, not shipped"
// conclusion below no longer describes the compatibility condition itself, only
// the fact that the `PathP`-case *reduction* rule (wiring this into
// `reduce.rs`/`nbe.rs`) is still a separate, not-yet-taken step.
//
// Builds exactly the assembled term the rule above would produce, for an ordinary
// axiom `p : Path A a0 a1` (opaque — no special structure to exploit); under the
// *old* unconditional `check_sys`, `Checker::infer` rejected it with precisely
// `check_sys`'s "branches disagree on their overlap" error, because
// `PApp(t_k.lift(1,1), Var(1))` — a term that **genuinely, syntactically mentions
// the fresh, still-abstract path coordinate `j = Var(1)`** — could not be shown
// unconditionally `is_def_eq` to the *j-independent* endpoint term `a0`/`a1`
// without substituting a concrete value for `j`. Restriction-aware `check_sys`
// closes exactly this gap: on the `(j=0)` overlap clause, restricting the tube
// branch substitutes `j := i0`, giving `p @ i0`, which the pre-existing
// `path_boundary` equation already knows is `≡ a0` for *any* `p : PathP …` —
// opaque axioms included. Symmetrically for `(j=1)`/`a1`.
//
// Were the *reduction* rule wired into `reduce.rs`/`nbe.rs` without this fix, it
// would have silently broken **subject reduction**: a well-typed
// `HComp(PathP …, φ, u, u0)` term (checked once, via the *original* `n`-branch
// system, which never needed this compatibility) would `whnf`-reduce to a form
// that the very same checker, run again from scratch, rejected — exactly the
// class of bug this crate's "independently re-typechecks" testing discipline
// exists to catch (see [`transp_pi_rule`]'s and [`hcomp_pi_rule`]'s own soundness
// arguments, point 2). That risk is now retired for the *typing* side; the
// reduction rule itself is still not wired in (a separate, smaller step:
// generalize `hcomp_pi_rule`'s construction discipline to the `PathP` case and
// add differential reducer/NbE tests), and `J`, HIT composition, and `Glue`
// remain deferred as before (see the top-level module doc).

/// The `Π`-case `hcomp` filling rule (see the module doc's "Phase 3.7" section).
/// `dom`/`cod` are the fixed `Π`'s two components (same binder convention as
/// [`Term::Pi`]); `phi`/`u0` live in the ambient context; `u` is the checked line
/// (frame `[i, Γ]`, one interval binder). Returns `None` — the rule doesn't fire,
/// `hcomp` stays stuck — unless `u` is *syntactically* a literal [`Term::Sys`] (see
/// the module doc for why only that shape can be pushed through `@x` soundly).
pub(crate) fn hcomp_pi_rule(
    dom: &Term,
    cod: &Term,
    phi: &Cof,
    u: &Term,
    u0: &Term,
) -> Option<Term> {
    let Term::Sys(branches) = u else {
        return None;
    };
    // Push `@x` (the fresh `Π`-domain variable, `Var(1)` in the new frame `[i,x,Γ]`)
    // into every branch — see the module doc's "Construction" section.
    let new_branches: Vec<(Cof, Term)> = branches
        .iter()
        .map(|(psi_k, t_k)| (psi_k.lift(1, 1), Term::app(t_k.lift(1, 1), Term::Var(1))))
        .collect();
    let new_u = Term::sys(new_branches);
    let new_phi = phi.lift(1, 0);
    let new_u0 = Term::app(u0.lift(1, 0), Term::Var(0));
    let body = Term::hcomp(cod.clone(), new_phi, new_u, new_u0);
    Some(Term::lam(dom.clone(), body))
}

// ============================================================================
// Phase 3.9: the `PathP`-case `hcomp` filling rule — NOW WIRED IN.
// ============================================================================
//
// Phase 3.8 (above) designed the CCHM `PathP`-case `hcomp` rule, diagnosed that the
// *then-current* (unconditional) `check_sys` compatibility condition rejected the
// enlarged system it builds, and — per the standing "ship only what's demonstrably
// sound" instruction — declined to wire in the reduction, leaving `hcomp` at a
// `PathP` type permanently stuck. A later pass fixed the diagnosed root cause
// (`check_sys`'s compatibility condition is now **restriction-aware**, see
// `crate::face::restrict_clause_term`'s doc) and confirmed — in
// [`kernel_tests::hcomp_pathp_rule_enlarged_system_now_passes_restriction_aware_check_sys`]
// — that the very enlarged system Phase 3.8 designed now passes `check_sys` from
// scratch. This phase takes the one remaining step: lift that construction into a
// shared builder ([`hcomp_pathp_rule`], mirroring [`hcomp_pi_rule`]'s own shape) and
// wire it into both `reduce.rs`'s `whnf` and `nbe.rs`'s `eval`.
//
// # The rule
//
// ```text
//   hcomp (PathP C a b) φ u u0
//     ↦ ⟨j⟩ hcomp (C @ j) ( φ ∨ (j=0) ∨ (j=1) )
//                        [ φ ↦ (u i) @ j , (j=0) ↦ a , (j=1) ↦ b ]
//                        (u0 @ j)
// ```
//
// Fires only when `u` is *syntactically* (no `whnf`) a literal [`Term::Sys`] —
// exactly [`hcomp_pi_rule`]'s own discipline, and for exactly the same reason: only
// a literal `Sys`'s branches are concrete enough to push `@j` through soundly (see
// that function's doc, and Phase 3.8's diagnosis above, for why an opaque
// `Partial`-typed neutral has no such elimination).
//
// # Construction and index bookkeeping
//
// Given `fam` (`PathP`'s own family, frame `[j, Γ]` — `PathP`'s binder convention,
// matching a fresh `⟨j⟩` one-for-one), `a0`/`a1` (the fixed endpoints, ambient
// context `Γ`), `phi`/`u0` (ambient `Γ`), and `u`'s branches `(ψ_k, t_k)` (each
// living in frame `[i, Γ]`, `t_k : PathP fam a0 a1` — the same frame `u` itself
// lives in, per `Term::HComp`'s own convention):
//
// * **New guards** `ψ_k.lift(1,1)`: reindex from `[i,Γ]` to `[i,j,Γ]` (insert `j`
//   *under* `i`, at cutoff 1) — identical bookkeeping to [`hcomp_pi_rule`]'s
//   `psi_k.lift(1,1)`.
// * **Tube branches** `PApp(t_k.lift(1,1), Var(1))`: `t_k` reindexed the same way,
//   applied (`@`, not ordinary `App` — `t_k : PathP …`, a path, not a function) to
//   the fresh `j = Var(1)` in that frame.
// * **Endpoint branches** `(j=0) ↦ a0.lift(2,0)`, `(j=1) ↦ a1.lift(2,0)`: `a0`/`a1`
//   have no binder of their own (frame `Γ`), so lifting by *two* (inserting both the
//   new `hcomp`'s own interval binder `i'` *and* `j` above `Γ`) reindexes them into
//   the new system's frame `[i',j,Γ]` directly — mirroring
//   [`kernel_tests::hcomp_pathp_rule_enlarged_system_now_passes_restriction_aware_check_sys`]'s
//   own `e0`/`e1` construction verbatim.
// * **New line** `u' := Sys [ ψ_1.lift(1,1) ↦ tube_1, …, (j=0) ↦ a0.lift(2,0),
//   (j=1) ↦ a1.lift(2,0) ]`, living in frame `[i',j,Γ]` — exactly `Term::HComp`'s
//   own convention for its `u` field (one interval binder over the ambient context,
//   now `[j,Γ]`).
// * **New guard** `phi.lift(1,0) ∨ (j=0) ∨ (j=1)`: `phi` (frame `Γ`) lifted by one
//   into `[j,Γ]`, joined with the two boundary faces of the fresh `j`.
// * **New cap** `PApp(u0.lift(1,0), Var(0))`: `u0` (frame `Γ`) lifted into `[j,Γ]`,
//   path-applied to the fresh `j = Var(0)` there.
// * **Body**: `hcomp fam new_phi u' new_u0`, living in frame `[j,Γ]` — exactly the
//   frame a `PLam(body)`'s body is expected in.
//
// [`hcomp_pathp_rule`] builds exactly this (one `PLam` wrapping one nested `HComp`,
// whose `u` field is the rebuilt, enlarged `Sys`) — one extra binder (`PLam`'s own
// `j`, sitting *outside* the inner `hcomp`'s interval binder) compared to
// [`hcomp_pi_rule`]'s single `Lam`, matching Phase 3.8's own bookkeeping note.
//
// # Soundness
//
// This rule adds **no new axiom or primitive** — like [`hcomp_pi_rule`], it is a
// pure rewriting of one `HComp` node into more `HComp`/`Sys`/`PLam`/`PApp` nodes,
// each independently re-typechecked by the existing, unmodified
// `Checker::infer`/`check_sys`. The argument:
//
// 1. **Type preservation.** The original `HComp(PathP fam a0 a1, φ, u, u0)` node's
//    checked type is `PathP fam a0 a1` (`Checker::infer`'s `Term::HComp` arm always
//    reports `ty` unchanged, regardless of which reduction rule fires — subject
//    reduction is what must hold, exactly as for `hcomp_pi_rule`). The built
//    `PLam(body)` has, by `Checker::infer`'s `Term::PLam` arm — which independently
//    *re-derives* the enclosing `PathP`'s boundary from `body`'s own `i0`/`i1`
//    instances, it does not merely trust a claimed type (see `crate::cubical`'s
//    `Term::PLam` checking rule) — type `PathP fam (body[j:=i0]) (body[j:=i1])`.
//    `body = HComp(fam, new_phi, new_u, new_u0)` under one `j` binder infers, by the
//    *very same* unmodified `Term::HComp` arm, to `fam` (held fixed, exactly as
//    `hcomp_pi_rule`'s inner `HComp(cod, …)` does) — **provided** its own three
//    obligations hold, exactly mirroring `hcomp_pi_rule`'s soundness argument
//    point 1:
//    - `check_cof_wellformed(new_phi)`: `phi.lift(1,0)` is a structural reindexing of
//      an already-well-formed `phi` (ordinary weakening, as before), joined with the
//      two literal boundary atoms `(j=0)`/`(j=1)` on the fresh `j:I` binder itself —
//      trivially well-formed.
//    - `check(new_u, Partial(new_phi, fam).lift(1,0))`: `new_u` is *by construction*
//      a literal `Sys`. **Coverage**: `new_phi = φ.lift(1,0) ∨ (j=0) ∨ (j=1)` is
//      *exactly* the disjunction of `new_u`'s own guards
//      (`ψ_1.lift(1,1) ∨ … ∨ ψ_n.lift(1,1) ∨ (j=0) ∨ (j=1)`) up to the *original*
//      coverage obligation (`entails(φ, ψ_1∨…∨ψ_n)`, already required by the source
//      `HComp`'s own `check(u, Partial(φ,ty).lift(1,0))`) lifted by the same
//      structural weakening lemma `hcomp_pi_rule` already relies on — so `new_phi`
//      entails it by construction, with the two extra endpoint disjuncts trivially
//      self-covering. **Each branch typechecks**: a tube branch
//      `PApp(t_k.lift(1,1), Var(1)) : fam[j:=Var(1)]` because `t_k : PathP fam a0 a1`
//      (the *original* system's own `check(t_k, ty)` obligation, `ty = PathP fam a0
//      a1`) path-applied to `j` — ordinary, unconditional `PathP`-application via
//      `crate::check::Checker::path_boundary`'s generic (non-endpoint) case, giving
//      `fam[j:=Var(1)]` by the standard substitution lemma; an endpoint branch
//      `a0.lift(2,0) : fam[j:=i0]` / `a1.lift(2,0) : fam[j:=i1]` holds *exactly* by
//      the source `PathP fam a0 a1`'s own well-formedness (`a0`/`a1` were already
//      required to check at `fam[j:=i0]`/`fam[j:=i1]` respectively when the `PathP`
//      type itself was formed — see `crate::cubical`'s `Term::PathP` checking rule —
//      and lifting by two into `[i',j,Γ]` is the identical reindexing). **Compatibility**
//      (the previously-blocking obligation, now restriction-aware): a tube/tube
//      overlap is a congruence of the original system's own (already-checked)
//      tube/tube compatibility, exactly as `hcomp_pi_rule`'s point 1 argues for
//      `App(-,x)`, now for the congruence `PApp(-, Var(1))`; a tube/endpoint overlap
//      (`ψ_k.lift(1,1) ∧ (j=0)`, say) restricts, on its every DNF clause, `j := i0`
//      (forced by the `(j=0)` conjunct in every such clause — `restrict_clause_term`
//      substitutes exactly the endpoints a clause pins), turning the tube branch into
//      `PApp(t_k.lift(1,1)[j:=i0], i0) ≡ t_k[j:=i0]-frame @ i0`, which
//      `crate::check::Checker::path_boundary`'s **literal-`i0`** case (the one this
//      module's Phase 3.8 doc explicitly flagged as *not* firing for a bound
//      variable — but here, after restriction, the argument genuinely *is* the
//      literal `Term::IZero`) equates to `a0` — `t_k`'s own checked `PathP fam a0 a1`
//      typing forces exactly this boundary, for *any* `t_k`, opaque axioms included.
//      This is the *precise* mechanism `check_sys`'s restriction-awareness exists
//      for, re-derived here structurally (not merely cited) for the endpoint-overlap
//      case specifically; symmetrically for `(j=1)`/`a1`. An endpoint/endpoint
//      overlap (`(j=0)∧(j=1)`) is `⊥` (a fresh `j` cannot be pinned to both literal
//      endpoints at once — `crate::face`'s own overlap decision procedure already
//      handles this as an existing, unmodified case), so it is vacuously compatible.
//    - **Cap agreement** `new_u[i':=i0] ≡ new_u0`: substituting `i':=i0` distributes
//      over `new_u`'s branches (structural on `Sys`); the tube branches become
//      `PApp(t_k[i:=i0], j)` (using the *original* cap agreement `u[i:=i0] ≡ u0`,
//      already checked, and the congruence `PApp(-,j)` respects `≡`) `≡ PApp(u0, j)`
//      — exactly `new_u0` after the frame reindexing (identical bookkeeping to
//      `hcomp_pi_rule`'s own cap-agreement argument); the endpoint branches don't
//      mention `i'` at all, so substituting `i':=i0` is the identity on them, and
//      they are exactly the boundary values `check_sys`'s compatibility argument
//      above already used to justify the *tube* branches' agreement at `j=0`/`j=1`
//      — so no new obligation is introduced there either.
// 2. **Every produced subterm independently re-typechecks** — not merely argued:
//    [`kernel_tests::hcomp_pathp_rule_reduces_and_reinfers_the_pathp_type`] below
//    builds a concrete instance, reduces it (confirming the rule genuinely *fires*,
//    producing a literal `PLam`), and re-runs `Checker::infer` on the reduced normal
//    form from scratch, additionally checking its `j=i0`/`j=i1` boundaries
//    (`PApp(result, IZero)`/`PApp(result, IOne)`) definitionally equal to the
//    original `a`/`b` — the enlarged system's endpoint branches force exactly this,
//    but it is independently *re-derived* here rather than merely assumed from the
//    construction.
// 3. **Reducer/NbE agreement**:
//    [`kernel_tests::hcomp_pathp_rule_agrees_between_reducer_and_nbe`] confirms both
//    engines land on the same (up-to-conversion) value.
// 4. **Agreement with the trivial `⊤` rule**: as with `hcomp_pi_rule`, both call
//    sites check `is_true(phi)` first, unconditionally, so the two rules never both
//    fire on the same term — no possible disagreement by construction. A dedicated
//    test, [`kernel_tests::hcomp_pathp_rule_agrees_with_the_trivial_rule_when_phi_is_top`],
//    confirms the *values* still agree (applied at a concrete boundary) even though
//    only one rule's reduction step literally fires.
// 5. **No new equation between unrelated closed terms; anti-`False`.** The rule only
//    ever rewrites via ordinary substitution/reindexing and re-wraps in
//    `HComp`/`Sys`/`PLam`/`PApp` — it never invents a value or asserts an equation
//    not already forced by the source system's own (already-checked) obligations.
//    [`kernel_tests::hcomp_pathp_rule_cannot_conjure_a_path_between_unrelated_axioms`]
//    and [`kernel_tests::no_closed_path_nat_0_1_via_hcomp_pathp_rule`] re-run the
//    module doc's anti-`False` attacks through this specific rule.
pub(crate) fn hcomp_pathp_rule(
    fam: &Term,
    a0: &Term,
    a1: &Term,
    phi: &Cof,
    u: &Term,
    u0: &Term,
) -> Option<Term> {
    let Term::Sys(branches) = u else {
        return None;
    };
    // Push `@j` (the fresh path coordinate, `Var(1)` in the new frame `[i',j,Γ]`)
    // into every tube branch — see the module doc's "Construction" section.
    let mut new_branches: Vec<(Cof, Term)> = branches
        .iter()
        .map(|(psi_k, t_k)| (psi_k.lift(1, 1), Term::papp(t_k.lift(1, 1), Term::Var(1))))
        .collect();
    // The two new endpoint faces: `(j=0) ↦ a0`, `(j=1) ↦ a1`, reindexed from the
    // ambient `Γ` into `[i',j,Γ]` (insert both fresh binders above `Γ`). `j` is
    // `Var(1)` in this frame (`i'`, the new hcomp's own interval binder, is
    // `Var(0)`) — these guards must pin the *outer* `PLam` coordinate `j`, not the
    // freshly-introduced inner `hcomp` binder.
    new_branches.push((Cof::eq0(Term::Var(1)), a0.lift(2, 0)));
    new_branches.push((Cof::eq1(Term::Var(1)), a1.lift(2, 0)));
    let new_u = Term::sys(new_branches);
    // `φ ∨ (j=0) ∨ (j=1)`, reindexed into the new hcomp's ambient frame `[j,Γ]`.
    let new_phi = Cof::or(Cof::or(phi.lift(1, 0), Cof::eq0(Term::Var(0))), Cof::eq1(Term::Var(0)));
    let new_u0 = Term::papp(u0.lift(1, 0), Term::Var(0));
    let body = Term::hcomp(fam.clone(), new_phi, new_u, new_u0);
    Some(Term::plam(body))
}

// ============================================================================
// Phase 3.10: `transp` for type-parameter-varying user inductives.
// ============================================================================
//
// Every rule shipped so far handles a *type former* (`Π`, `PathP`) built into the
// term grammar itself. This phase extends `transp` one more step: through a
// **user-declared, non-indexed inductive with uniform type parameters** (`List A`,
// `Option A`, `Pair A B`, …), transported along a path *in one of those
// parameters*. This is CCHM's own "data transport" rule (Cohen–Coquand–
// Huber–Mörtberg §6.1 / the `hcomp`/`transp`-for-data-types construction present
// in every subsequent cubical implementation, e.g. cubicaltt/redtt): transport
// pushes structurally into each constructor's fields, transporting each field
// along the line induced by its own (sub)type.
//
// ```text
//   transp (λ i. D (P_1 i) … (P_n i)) φ (c a_1 … a_k)
//     ↦ c (P_1 i1) … (P_n i1)                              -- the new parameters
//         (transp^{field_1} …) … (transp^{field_k} …)        -- transported fields
// ```
//
// # Scope (what this rule fires on, precisely)
//
// * `D` a user inductive (`env.get(D) = Some(Decl::Inductive(ind))`) with
//   **`ind.num_indices == 0`** — no indices, only uniform parameters (the
//   "non-indexed" restriction the task calls for; indexed families need the
//   harder index-transport rule and are explicitly out of scope here).
// * The family's head is, *syntactically* (no `whnf` — the same conservative,
//   structural-only convention every rule in this file already uses, see
//   [`transp_pi_rule`]/[`hcomp_pi_rule`]'s own doc comments), `D` applied to
//   *exactly* `ind.num_params` arguments (`fam.unfold_apps()`), each living under
//   the transp's own interval binder. **Exactly one** of those arguments may
//   mention the bound interval variable (`mentions_var(_, 0)`) — the "the
//   varying parameter" the task's paradigm case describes; the rest must be
//   interval-constant (this is what makes the surrounding parameters' own
//   `transp`s below unconditionally the identity, rather than requiring the full
//   generality of *every* parameter varying at once, a strictly harder rule this
//   pass does not attempt).
// * The argument `a` is, *syntactically* (again no `whnf` — matching this file's
//   standing discipline, and directly analogous to [`hcomp_pi_rule`]/
//   [`hcomp_pathp_rule`] only firing on a literal `Sys`), a fully-applied
//   constructor: `a.unfold_apps() = (Const(ctor, ls), args)` with `ctor` a
//   constructor of `D` (`env.get(ctor) = Some(Decl::Constructor(c)), c.ind == D`)
//   and `args.len() == ind.num_params + c.num_fields`.
// * Each field's declared type (read off the constructor's own checked `Π`-
//   telescope type, `Constructor::ty`) must be **non-dependent on earlier
//   fields** — it may only mention the type parameters, never a previously-bound
//   field variable (true of every "ordinary" data constructor: `List`/`Option`/
//   `Pair`/`Vec`-with-a-separate-length-index/…; ruled out are constructors like
//   `Σ`'s own dependent pair where a later field's *type* depends on an earlier
//   field's *value* — a genuinely harder rule, deferred). This is checked
//   structurally (`mentions_var` on each earlier field index) before any field is
//   classified, so the rule *declines* (returns `None`, transp stays stuck) on
//   any constructor shaped this way rather than mis-firing.
// * Each (non-dependent, parameter-only) field type is then classified into
//   exactly one of three structural shapes — see [`FieldKind`] — and any field
//   whose type doesn't match one of the three is *also* a decline (`None`),
//   consistent with this whole file's "stay stuck rather than guess" posture.
//
// # The three field kinds
//
// Reading a field's domain type in the *pure-parameter* context (after
// confirming it mentions no earlier field, `Term::lift(-(j), 0)` safely drops the
// `j` field binders already peeled — sound exactly because `Term::lift`'s own doc
// requires no in-range free variable, which the non-dependence check just
// established):
//
// * [`FieldKind::Param`] — the field's type *is* (up to syntactic equality) the
//   varying parameter itself (`Var(pidx)` in the reduced context, e.g. `List A`'s
//   head field `A`). Transported by `transp`-ing along the very sub-line
//   `fam`'s own varying argument already supplies — this is [`coe`]'s use case
//   one level up: literally `Term::transp(P_pidx, ⊤, field)` where `P_pidx` is
//   the family's `pidx`-th argument (itself a term under one interval binder,
//   living in exactly the frame `Transp`'s own `family` field expects).
// * [`FieldKind::Recursive`] — the field's type is `D` applied to *exactly* the
//   parameters in order (e.g. `List A`'s tail field, `List A` again). Transported
//   by recursing: `Term::transp(fam.clone(), ⊤, field)` — the *same* family,
//   producing another (possibly further-reducible, lazily) `Transp` node. This is
//   what makes the rule walk an entire list/tree/whatever structurally, one
//   constructor layer per `whnf` step, exactly mirroring how ι-reduction peels
//   one constructor layer per step rather than eagerly normalizing a whole
//   recursive value.
// * [`FieldKind::Const`] — the field's type mentions **no** parameter at all
//   (e.g. a `Nat`-typed "length" auxiliary field that happens not to depend on
//   the type parameter). Transported by regularity: the field is returned
//   **unchanged** — the CCHM/this-file's existing regularity principle, now
//   applied per-field rather than to the whole `transp`.
//
// Any field type that is none of the three (e.g. `Option A`, `Pair A A`, a
// *different* inductive applied to the parameter, or the varying parameter
// wrapped in some other former) is **not** attempted — the whole rule declines,
// and the parent `transp` stays stuck, honestly incomplete rather than silently
// wrong. Extending to more field shapes (nested applications of *other*
// parametrized inductives, e.g. `List (List A)`) is the natural generalization
// path but needs its own field-kind case and its own soundness argument; not
// attempted this pass.
//
// # Soundness
//
// Exactly the same posture as every other rule in this file: **no new axiom or
// primitive**, purely a rewriting of one `Transp` node into a constructor
// application whose arguments are themselves (possibly further-reducible)
// `Transp`/original-field terms, each independently re-typechecked by the
// existing, unmodified `Checker::infer`.
//
// 1. **Type preservation.** The source `Transp(fam, φ, a)` node's checked type is
//    `fam[i:=i1] = D (P_1 i1) … (P_n i1)` (`Checker::infer`'s `Term::Transp` arm,
//    unmodified by this phase). The built term is
//    `ctor (P_1 i1) … (P_n i1) field'_1 … field'_k` — by `Checker::infer`'s
//    `Term::Const`/`Term::App` arms (also unmodified), this infers to `D (P_1 i1)
//    … (P_n i1)` **provided** `ctor`'s own checked `Π`-telescope type accepts
//    `field'_j` at the type `c`'s telescope predicts once the parameters are
//    instantiated to `(P_1 i1) … (P_n i1)` — i.e. `field'_j : FieldTy_j[params :=
//    P_• i1]`. This holds per field kind:
//    - `Param`: `field'_j = Term::transp(P_pidx, ⊤, field_j)`. The *original*
//      constructor application `a`'s own checked typing (an independent, already
//      -verified premise: `a : fam[i:=i0]`, forcing `a`'s spine to check against
//      `ctor`'s telescope with parameters `(P_1 i0)…(P_n i0)`) gives
//      `field_j : P_pidx[i:=i0]` — exactly the source type `Transp`'s own
//      `Term::Transp` checking rule requires for its family `P_pidx` and argument
//      `field_j`. `Checker::infer`'s (unmodified) `Term::Transp` arm then reports
//      `field'_j : P_pidx[i:=i1]` — precisely `FieldTy_j[params := P_• i1]` for
//      this field kind (`FieldTy_j = Var(pidx)`, i.e. literally the `pidx`-th
//      parameter).
//    - `Recursive`: `field'_j = Term::transp(fam.clone(), ⊤, field_j)`. Same
//      argument: `field_j : fam[i:=i0]` (from `a`'s own already-checked typing,
//      this field kind being `FieldTy_j = D(Var(n-1))…(Var(0))`, i.e. exactly `D`
//      applied to the parameters, which after substituting `params := P_• i0` is
//      exactly `fam[i:=i0]`), so `Term::Transp`'s own unmodified checking rule
//      gives `field'_j : fam[i:=i1] = D(P_• i1)` — exactly `FieldTy_j[params :=
//      P_• i1]` for this kind.
//    - `Const`: `field'_j = field_j` unchanged. `field_j`'s already-checked type
//      (from `a`'s own typing) is `FieldTy_j[params := P_• i0]`; since `FieldTy_j`
//      by this kind's own defining property mentions **no** parameter variable at
//      all, `FieldTy_j[params := P_• i0]` and `FieldTy_j[params := P_• i1]` are
//      the identical term (substituting into a term with no free occurrence of
//      the substituted variables is the identity — the same argument this
//      module's top-level regularity rule already relies on, re-used per-field
//      here) — so `field_j`'s existing type already **is** the target type,
//      unchanged.
// 2. **Every produced subterm independently re-typechecks** — not merely argued:
//    [`kernel_tests::transp_list_rule_transports_a_concrete_list`] and
//    [`kernel_tests::transp_list_rule_type_preservation_from_scratch`] below build
//    a concrete `List`-like inductive, reduce a `transp` through a multi-element
//    list, and re-run `Checker::infer` on the fully-reduced normal form.
// 3. **Regularity agreement.** [`kernel_tests::transp_list_rule_agrees_with_regularity_on_a_constant_parameter`]
//    transports a list along `refl` (a constant parameter family, so the
//    top-level regularity rule — checked *first*, unconditionally, exactly as
//    every other rule in this file defers to it — fires instead, and this rule
//    never even runs) and confirms the two notions of "unchanged" coincide.
// 4. **Reducer/NbE agreement**:
//    [`kernel_tests::transp_list_rule_agrees_between_reducer_and_nbe`] confirms
//    both engines land on the same (up-to-conversion) value.
// 5. **Anti-`False`.** [`kernel_tests::transp_list_rule_cannot_smuggle_a_type_change`]
//    re-runs this module's standing "opaque type-level path axiom" attack through
//    the list case specifically: transporting a list of `A`s along an opaque
//    `p : Path Type A B` produces a list of `B`s whose elements are `transport
//    p`-images — checked from scratch — and is **not** confused with the
//    original `A`-typed list.
//
// # What this does *not* handle (deferred, honestly)
//
// * **Indexed** inductives (`Vec` with a length *index*, `Fin`, …) — needs
//   transporting the indices too, a strictly harder rule.
// * **Multiple simultaneously-varying parameters** (e.g. transporting `Pair A B`
//   along paths in *both* `A` and `B` at once) — this pass requires exactly one
//   varying parameter; a family with two or more varying parameters simply
//   doesn't match this rule's guard and stays stuck (still sound, just less
//   complete).
// * **Fields whose type nests another parametrized inductive** around the
//   varying parameter (`List (List A)`, `Option (List A)`) — falls through
//   `FieldKind`'s classification (`None` of the three shapes match) and declines.
// * **Dependent fields** (a field's type depending on an earlier field's value,
//   e.g. `Σ`-like constructors) — declines via the non-dependence check.
// * `hcomp` for inductives, HITs, `Glue` — untouched by this phase (see the
//   top-level module doc's "What's deferred").

/// How a non-indexed inductive constructor's field's declared type relates to
/// the (single) varying type parameter — see the module doc's "The three field
/// kinds" section for the full soundness argument per case.
enum FieldKind {
    /// The field's type *is* the varying parameter itself (`List A`'s head).
    Param,
    /// The field's type is the inductive applied to exactly the parameters, in
    /// order (`List A`'s tail).
    Recursive,
    /// The field's type mentions no parameter at all — regularity applies.
    Const,
}

/// Classify constructor `ind_name`'s field domain `dom` (already confirmed to
/// mention no earlier field — see the caller) as one of [`FieldKind`]'s three
/// shapes, in the *pure-parameter* context (`Var(num_params-1) = param_0, …,
/// Var(0) = param_{num_params-1}`, the standard `Π`-telescope convention — see
/// the module doc). `pidx` is the (0-indexed, left-to-right) position of the
/// varying parameter. Returns `None` if `dom` matches none of the three shapes
/// (the caller then declines the whole rule).
fn classify_field(dom: &Term, ind_name: &str, num_params: usize, pidx: usize) -> Option<FieldKind> {
    let varying_var = num_params - 1 - pidx;
    if *dom == Term::Var(varying_var) {
        return Some(FieldKind::Param);
    }
    let (head, args) = dom.unfold_apps();
    if let Term::Const(n, _) = &head {
        if n.as_ref() == ind_name
            && args.len() == num_params
            && args.iter().enumerate().all(|(i, a)| *a == Term::Var(num_params - 1 - i))
        {
            return Some(FieldKind::Recursive);
        }
    }
    if (0..num_params).all(|k| !mentions_var(dom, k)) {
        return Some(FieldKind::Const);
    }
    None
}

/// The `transp`-for-parametrized-inductives filling rule (see the module doc's
/// "Phase 3.10" section). `env` supplies the inductive/constructor declarations;
/// `fam` is the transp's family (one interval binder, `Var(0) = i`, over the
/// ambient context); `a` is the transp's checked argument (ambient context, no
/// interval binder). Returns `None` — the rule doesn't fire, `transp` stays
/// stuck — unless every structural precondition in the module doc holds; never
/// panics on a malformed/unexpected shape.
pub(crate) fn transp_inductive_rule(env: &Env, fam: &Term, a: &Term) -> Option<Term> {
    // The family's head must be, syntactically, a user inductive applied to
    // exactly its uniform parameters (no indices — see the module doc's scope).
    let (fam_head, fam_args) = fam.unfold_apps();
    let Term::Const(d_name, _d_ls) = &fam_head else { return None };
    let Some(Decl::Inductive(ind)) = env.get(d_name) else { return None };
    if ind.num_indices != 0 || fam_args.len() != ind.num_params {
        return None;
    }
    // Exactly one parameter may vary.
    let mut pidx = None;
    for (i, p) in fam_args.iter().enumerate() {
        if mentions_var(p, 0) {
            if pidx.is_some() {
                return None; // more than one varying parameter — out of scope
            }
            pidx = Some(i);
        }
    }
    let pidx = pidx?;

    // The argument must be, syntactically, a fully-applied constructor of `D`.
    let (a_head, a_args) = a.unfold_apps();
    let Term::Const(ctor_name, ctor_ls) = &a_head else { return None };
    let Some(Decl::Constructor(ctor)) = env.get(ctor_name) else { return None };
    if ctor.ind.as_ref() != d_name.as_ref() || a_args.len() != ind.num_params + ctor.num_fields {
        return None;
    }

    // Peel `ctor`'s own checked `Π`-telescope: `num_params` parameter binders,
    // then `ctor.num_fields` field binders, collecting each field's raw domain
    // (in the accumulating context — see the module doc's index bookkeeping).
    let mut cur = &ctor.ty;
    for _ in 0..ind.num_params {
        match cur {
            Term::Pi(_, _, cod) => cur = cod,
            _ => return None,
        }
    }
    let mut field_kinds = Vec::with_capacity(ctor.num_fields);
    for j in 0..ctor.num_fields {
        let Term::Pi(_, dom, cod) = cur else { return None };
        // Non-dependence: the field's type must not mention any earlier field.
        if (0..j).any(|k| mentions_var(dom, k)) {
            return None;
        }
        // Safe: `dom` mentions no `Var` in `0..j` (just confirmed), so shifting
        // those `j` binders away is exactly `Term::lift`'s documented negative-
        // amount case.
        let dom_reduced = dom.lift(-(j as isize), 0);
        let kind = classify_field(&dom_reduced, d_name, ind.num_params, pidx)?;
        field_kinds.push(kind);
        cur = cod;
    }

    // Build the transported fields (see the module doc's "The three field
    // kinds").
    let fields = &a_args[ind.num_params..];
    let mut new_fields = Vec::with_capacity(ctor.num_fields);
    for (j, kind) in field_kinds.into_iter().enumerate() {
        let field = &fields[j];
        let new_field = match kind {
            FieldKind::Param => Term::transp(fam_args[pidx].clone(), Cof::top(), field.clone()),
            FieldKind::Recursive => Term::transp(fam.clone(), Cof::top(), field.clone()),
            FieldKind::Const => field.clone(),
        };
        new_fields.push(new_field);
    }

    // The new parameters: `fam`'s own arguments instantiated at `i1`.
    let new_params: Vec<Term> = fam_args.iter().map(|p| p.instantiate(&Term::IOne)).collect();

    Some(Term::apps(
        Term::cnst(ctor_name.clone(), ctor_ls.clone()),
        new_params.into_iter().chain(new_fields),
    ))
}

// ============================================================================
// Phase 3.11: the constructor-compatible `hcomp` filling rule for user
// inductive types (CCHM `data`/inductive `hcomp`, non-indexed, same-constructor
// case only — see below for exactly what is/isn't in scope).
// ============================================================================
//
// `hcomp`'s type argument (unlike `transp`'s family) is a single **fixed**
// type — Phase 3 deliberately kept `hcomp` homogeneous in the strongest sense
// (see the module doc's opening section). So the CCHM data-type `hcomp` rule
// specializes here to something *simpler* than [`transp_inductive_rule`]'s own
// three-way `Param`/`Recursive`/`Const` field classification: since the type
// never varies, a non-recursive field's own (parameter-instantiated) type is
// already a fixed, non-interval-dependent type — there is no "varying
// parameter" line to transport along, only an ordinary `hcomp` *at that fixed
// type*. The only real case split left is whether a field recurses into `D`
// itself (needing the recursive sub-`hcomp` to walk one constructor layer
// deeper) or not (composing directly at the field's own type). Concretely,
// for a *non-indexed* inductive `D` with constructor `c`, when the base `u0`
// and **every** branch of the system `u` are (syntactically) the *same*
// constructor `c` applied to arguments:
//
// ```text
//   hcomp D φ [ ψ_k ↦ c(a_k1 … a_kn) ] (c b_1 … b_n)
//     ↦ c ( hcomp T_1 φ [ψ_k ↦ a_k1] b_1 ) … ( hcomp T_n φ [ψ_k ↦ a_kn] b_n )
// ```
//
// where `T_j` is field `j`'s declared type, read off `c`'s own checked
// `Π`-telescope with the (fixed, non-varying) parameters of `D` substituted
// in, **except** when `T_j` is `D` applied to exactly those same parameters —
// then the sub-composition recurses in `D` itself (`T_j := D`, i.e. the very
// `ty` this `hcomp` is already at), rather than trying to build a "type of a
// `D`-argument" that isn't `D`.
//
// # Scope (what this rule fires on, precisely)
//
// * `ty` a user inductive (`env.get(D) = Some(Decl::Inductive(ind))`) with
//   **`ind.num_indices == 0`** (non-indexed — matching [`transp_inductive_rule`]'s
//   own restriction) applied, *syntactically* (no `whnf`, this file's standing
//   discipline), to *exactly* `ind.num_params` arguments.
// * `u` is, syntactically, a literal [`Term::Sys`] — exactly
//   [`hcomp_pi_rule`]/[`hcomp_pathp_rule`]'s own discipline (only a literal
//   `Sys`'s branches are concrete enough to project a field out of soundly).
// * `u0` is, syntactically, a fully-applied constructor of `D`:
//   `u0.unfold_apps() = (Const(c, ls), args)` with `c` a constructor of `D`
//   (`env.get(c) = Some(Decl::Constructor(ctor)), ctor.ind == D`) and
//   `args.len() == ind.num_params + ctor.num_fields`.
// * **Every** branch body of `u`, unfolded the same way, is headed by that
//   *same* `c` with the *same* total argument count. If even one branch is
//   headed by a different constructor (the "heterogeneous" case) — or by
//   anything that isn't a literal constructor application at all (an opaque
//   neutral branch, say) — the rule declines (`None`); this is the genuinely
//   *stuck* case CCHM itself doesn't give a value to without extra machinery
//   (Glue-style structure identifying the mismatched constructors' images),
//   which this pass does not attempt. **`u` with zero branches also declines**
//   (there is no constructor to agree on, and — degenerately — building
//   `c()` from an empty `Sys` would silently discard the "same constructor as
//   every branch" premise the rule exists to check).
// * Each field's declared type (`Constructor::ty`'s telescope, read exactly as
//   [`transp_inductive_rule`] reads it) must be **non-dependent on earlier
//   fields** — the identical restriction, checked the identical way
//   (`mentions_var` on each earlier field index before classification), for
//   the identical reason (a later field's *type* depending on an earlier
//   field's *value* needs a strictly harder, dependent-composition rule, out
//   of scope here). Declines (`None`) rather than mis-firing.
//
// # The two field kinds
//
// Reading a field's domain type in the pure-parameter telescope context
// (`Var(num_params-1) = param_0, …, Var(0) = param_{num_params-1}`, exactly
// [`transp_inductive_rule`]'s own convention), *after* substituting `D`'s
// actual (fixed, `ty`'s own) parameter arguments in for those telescope
// variables (via [`Term::subst_ctx`] — sound because a field type that
// mentions no earlier field, just confirmed, is a closed term over exactly
// those `num_params` telescope variables, the standard-instantiation case
// `subst_ctx` is built for):
//
// * **Recursive** — the field's *raw* (un-substituted) telescope type is `D`
//   applied to exactly the parameters, in order (`args.len() == num_params`
//   and `args[i] == Var(num_params-1-i)`, [`transp_inductive_rule`]'s own
//   `FieldKind::Recursive` test, reused verbatim) — e.g. `List A`'s tail
//   field. Composed by recursing at `ty` itself: `hcomp ty φ [ψ_k↦a_kj] b_j`.
// * **Generic** — anything else. Composed at the field's own substituted type
//   `T_j` (`dom_reduced.subst_ctx(&images)`, `images` the parameters in
//   telescope order): `hcomp T_j φ [ψ_k↦a_kj] b_j`. Unlike
//   [`transp_inductive_rule`], this rule does **not** need `Param`/`Const` as
//   *separate* cases — since `ty` never varies, `T_j` is already a fixed,
//   non-interval-dependent type regardless of which telescope shape produced
//   it, so an ordinary (possibly further-reducible, lazily — one constructor
//   layer of `hcomp` fires per `whnf` step, matching every other rule's
//   posture) `hcomp` at `T_j` is always the right sub-composition — no
//   further case analysis needed, and (unlike `transp_inductive_rule`) no
//   field shape is declined here as "none of the known kinds".
//
// # Construction and index bookkeeping
//
// Unlike [`hcomp_pi_rule`]/[`hcomp_pathp_rule`], this rule introduces **no new
// binder** — the projected field terms `a_kj := args_k[num_params+j]` live in
// exactly the *same* frame the original branches `t_k` already lived in
// (`Term::HComp`'s own convention: `u`'s branches are terms under the
// enclosing `hcomp`'s own implicit interval binder, with no extra `Lam`/`PLam`
// wrapper the way the `Π`/`PathP` rules had to introduce one for their own
// fresh `x`/`j`). So no `lift` bookkeeping is needed when projecting a field
// out of each branch — `ψ_k` and `a_kj` are used completely unchanged.
//
// # Soundness
//
// No new axiom or primitive — a pure rewriting of one `HComp` node into a
// constructor application whose arguments are themselves (possibly
// further-reducible) `HComp`/original-field terms, each independently
// re-typechecked by the existing, unmodified `Checker::infer`/`check_sys`.
//
// 1. **Type preservation.** The source `HComp(ty, φ, u, u0)` node's checked
//    type is `ty` unchanged (`Checker::infer`'s `Term::HComp` arm always
//    reports `ty`, regardless of which rule fires). The built term is
//    `c (hcomp T_1 …) … (hcomp T_n …)` — by `Checker::infer`'s
//    `Term::Const`/`Term::App` arms (unmodified), this infers to `D
//    (params…)` — exactly `ty` — **provided** each `hcomp T_j φ new_u_j b_j`
//    checks at the type `c`'s telescope predicts for field `j` once the
//    parameters are instantiated to `ty`'s own arguments, i.e.
//    `T_j[params := ty's args]`. This holds per field kind, by
//    `Checker::infer`'s own (unmodified) `Term::HComp` arm reporting its
//    first argument back unchanged:
//    - `Recursive`: `hcomp ty φ new_u_j b_j` infers to `ty` by construction —
//      exactly `FieldTy_j[params := ty's args]` for this kind (`FieldTy_j = D`
//      applied to the parameters, which after the substitution *is* `ty`).
//    - `Generic`: `hcomp T_j φ new_u_j b_j` infers to `T_j` by construction —
//      exactly `FieldTy_j[params := ty's args]` for this kind, *by
//      definition* (`T_j` is built as precisely that substitution).
//    Each such sub-`hcomp`'s own three obligations (well-formed `φ`; `new_u_j
//    : Partial φ T_j`; cap agreement) hold because they are *inherited*
//    unchanged from the source `HComp`'s own already-checked obligations:
//    - `check_cof_wellformed(φ)`: `φ` is reused completely unchanged (no
//      reindexing at all, per the "no new binder" note above) — the source
//      `HComp`'s own already-checked well-formedness applies verbatim.
//    - **Coverage** (`entails(φ, ψ_1 ∨ … ∨ ψ_n)`): the new system's guards are
//      *exactly* the original `ψ_k`'s, unchanged — this is *the same
//      disjunction*, already required to be entailed by `φ` by the source
//      `HComp`'s own `check(u, Partial(φ,ty))` obligation. **Each branch
//      typechecks**: `a_kj : T_j` (or `: ty` for `Recursive`) follows from the
//      *original* branch's own already-checked typing `t_k : ty` (`ty = D
//      (params…)`, forcing `t_k`'s spine to check against `c`'s telescope with
//      those parameters — the *same* argument [`transp_inductive_rule`]'s own
//      point-1 argument makes per field kind, `Field` vs `Recursive`, reused
//      here verbatim with `i0`/`i1` erased since there is no interval
//      dependence to begin with). **Compatibility**: a tube/tube overlap
//      between projected fields `a_kj`/`a_k'j` is a direct congruence of the
//      *original* system's own already-checked tube/tube compatibility
//      (`t_k ≡ t_k'` on the overlap forces, by injectivity of the *same*
//      constructor `c`'s spine — the very premise this rule's "same
//      constructor" guard establishes — `a_kj ≡ a_k'j` on that overlap too).
//    - **Cap agreement** `new_u_j[i:=i0] ≡ b_j`: the *original* cap agreement
//      `u[i:=i0] ≡ u0` (already checked) distributes, by the same congruence
//      just used for compatibility (both sides whnf to the same `c` spine —
//      the branches by the same-constructor guard, `u0` by hypothesis — so
//      `is_def_eq` recurses into their arguments), to
//      `new_u_j[i:=i0] ≡ b_j` field-by-field, exactly the obligation each
//      sub-`hcomp` needs.
// 2. **Every produced subterm independently re-typechecks** — not merely
//    argued: [`kernel_tests::hcomp_list_rule_reduces_and_reinfers_the_list_type`]
//    below builds a concrete two-branch system over a `List`-like inductive,
//    reduces it (confirming the rule genuinely fires, producing a literal
//    `List.cons`), and re-runs `Checker::infer` on the result from scratch.
// 3. **Reducer/NbE agreement**:
//    [`kernel_tests::hcomp_list_rule_agrees_between_reducer_and_nbe`] confirms
//    both engines land on the same (up-to-conversion) value.
// 4. **Agreement with the trivial `⊤` rule**: as with `hcomp_pi_rule`/
//    `hcomp_pathp_rule`, both call sites check `is_true(phi)` first,
//    unconditionally, so the two rules never both fire on the same term.
//    [`kernel_tests::hcomp_list_rule_agrees_with_the_trivial_rule_when_phi_is_top`]
//    confirms the *values* still agree even though only one rule's reduction
//    step literally fires.
// 5. **Fires only on same-constructor systems; heterogeneous/non-constructor
//    systems stay stuck.**
//    [`kernel_tests::hcomp_list_rule_declines_on_mixed_constructor_branches`]
//    and [`kernel_tests::hcomp_list_rule_declines_when_a_branch_is_not_a_constructor_application`]
//    pin this down directly at the function level.
// 6. **No new equation between unrelated closed terms; anti-`False`.** The
//    rule only ever rewrites via ordinary projection/re-wrapping in
//    `HComp`/`Sys`/`Const`-application — it never invents a value or asserts
//    an equation not already forced by the source system's own (already
//    checked) obligations, and it never fires on an inductive with no
//    constructors (`u0`/every branch would have no constructor to be headed
//    by, so the structural guard above can never match).
//    [`kernel_tests::hcomp_list_rule_cannot_conjure_an_inhabitant_of_an_unrelated_axiom`]
//    and [`kernel_tests::hcomp_list_rule_does_not_conflate_distinct_lists`]
//    re-run this module's standing anti-`False`/non-conflation attacks through
//    this specific rule.
//
// # What this does *not* handle (deferred, honestly)
//
// * **Heterogeneous (mixed-constructor) `hcomp`** — when branches disagree on
//   which constructor of `D` they use. Genuinely needs more machinery (a
//   Glue-style identification of the different constructors' images) that
//   this pass does not attempt; the rule declines and the `hcomp` stays stuck.
// * **Indexed inductives** — needs transporting/composing the indices too, a
//   strictly harder rule (mirrors [`transp_inductive_rule`]'s own deferral).
// * **HIT `hcomp`** (composition through a path constructor) — the next pass,
//   per the task's own "DEFER" list; untouched here.
// * **`Glue`** — untouched by this phase.
// * **Dependent fields** (a field's type depending on an earlier field's
//   value) — declines via the non-dependence check, mirroring
//   [`transp_inductive_rule`].

/// How a non-indexed inductive constructor's field's declared type relates to
/// `D` itself, for the [`hcomp_inductive_rule`] filling rule — see the module
/// doc's "The two field kinds" section for the full soundness argument.
enum HFieldKind {
    /// The field's type is `D` applied to exactly the parameters, in order
    /// (`List A`'s tail) — the sub-composition recurses in `D` itself.
    Recursive,
    /// Anything else — composed directly at the field's own (parameter-
    /// substituted) type `T_j`.
    Generic(Term),
}

/// The `hcomp`-for-non-indexed-inductives, same-constructor filling rule (see
/// the module doc's "Phase 3.11" section). `env` supplies the
/// inductive/constructor declarations; `ty` is the fixed, non-varying
/// composition type (ambient context); `phi`/`u`/`u0` are the `hcomp`'s
/// remaining fields exactly as `Checker::infer`'s `Term::HComp` arm sees them
/// (`u` under one interval binder, `phi`/`u0` in the ambient context). Returns
/// `None` — the `hcomp` stays stuck — unless every structural precondition in
/// the module doc holds; never panics on a malformed/unexpected shape.
pub(crate) fn hcomp_inductive_rule(
    env: &Env,
    ty: &Term,
    phi: &Cof,
    u: &Term,
    u0: &Term,
) -> Option<Term> {
    // `ty` must be, syntactically, a non-indexed user inductive applied to
    // exactly its uniform parameters.
    let (ty_head, ty_args) = ty.unfold_apps();
    let Term::Const(d_name, _d_ls) = &ty_head else { return None };
    let Some(Decl::Inductive(ind)) = env.get(d_name) else { return None };
    if ind.num_indices != 0 || ty_args.len() != ind.num_params {
        return None;
    }

    // `u` must be, syntactically, a literal `Sys` with at least one branch.
    let Term::Sys(branches) = u else { return None };
    if branches.is_empty() {
        return None;
    }

    // `u0` must be, syntactically, a fully-applied constructor of `D`.
    let (u0_head, u0_args) = u0.unfold_apps();
    let Term::Const(ctor_name, ctor_ls) = &u0_head else { return None };
    let Some(Decl::Constructor(ctor)) = env.get(ctor_name) else { return None };
    if ctor.ind.as_ref() != d_name.as_ref() || u0_args.len() != ind.num_params + ctor.num_fields {
        return None;
    }

    // Every branch must be headed by that *same* constructor, with the same
    // total argument count — the "same-constructor" guard; a mismatch (a
    // different constructor, or a non-constructor branch entirely) declines
    // the whole rule rather than guessing.
    let mut branch_args: Vec<(Cof, Vec<Term>)> = Vec::with_capacity(branches.len());
    for (psi_k, t_k) in branches.iter() {
        let (h_k, args_k) = t_k.unfold_apps();
        let Term::Const(n_k, _) = &h_k else { return None };
        if n_k.as_ref() != ctor_name.as_ref() || args_k.len() != u0_args.len() {
            return None;
        }
        branch_args.push(((**psi_k).clone(), args_k));
    }

    // Peel `ctor`'s own checked `Π`-telescope: `num_params` parameter binders,
    // then classify each field (see the module doc's "The two field kinds").
    let mut cur = &ctor.ty;
    for _ in 0..ind.num_params {
        match cur {
            Term::Pi(_, _, cod) => cur = cod,
            _ => return None,
        }
    }
    // The parameters, in `subst_ctx`'s expected image order (`images[k]` is
    // substituted for `Var(k)`, and the pure-parameter telescope convention
    // has `Var(0) = param_{num_params-1}`, …, `Var(num_params-1) = param_0`
    // — i.e. the *reverse* of `ty_args`'s left-to-right order).
    let images: Vec<Term> = ty_args.iter().rev().cloned().collect();

    let mut field_kinds = Vec::with_capacity(ctor.num_fields);
    for j in 0..ctor.num_fields {
        let Term::Pi(_, dom, cod) = cur else { return None };
        // Non-dependence: the field's type must not mention any earlier field.
        if (0..j).any(|k| mentions_var(dom, k)) {
            return None;
        }
        // Safe: `dom` mentions no `Var` in `0..j` (just confirmed), so
        // shifting those `j` field binders away is exactly `Term::lift`'s
        // documented negative-amount case.
        let dom_reduced = dom.lift(-(j as isize), 0);
        let (dhead, dargs) = dom_reduced.unfold_apps();
        let kind = if let Term::Const(n, _) = &dhead {
            if n.as_ref() == d_name.as_ref()
                && dargs.len() == ind.num_params
                && dargs
                    .iter()
                    .enumerate()
                    .all(|(i, a)| *a == Term::Var(ind.num_params - 1 - i))
            {
                HFieldKind::Recursive
            } else {
                HFieldKind::Generic(dom_reduced.subst_ctx(&images))
            }
        } else {
            HFieldKind::Generic(dom_reduced.subst_ctx(&images))
        };
        field_kinds.push(kind);
        cur = cod;
    }

    // Build the composed fields (see the module doc's "The two field kinds").
    // No new binder is introduced (see the module doc's "Construction" note),
    // so branch guards/projected field terms are reused completely unchanged.
    let fields0 = &u0_args[ind.num_params..];
    let mut new_fields = Vec::with_capacity(ctor.num_fields);
    for (j, kind) in field_kinds.into_iter().enumerate() {
        let new_branches: Vec<(Cof, Term)> = branch_args
            .iter()
            .map(|(psi_k, args_k)| (psi_k.clone(), args_k[ind.num_params + j].clone()))
            .collect();
        let new_u = Term::sys(new_branches);
        let cap = fields0[j].clone();
        let new_field = match kind {
            HFieldKind::Recursive => Term::hcomp(ty.clone(), phi.clone(), new_u, cap),
            HFieldKind::Generic(field_ty) => Term::hcomp(field_ty, phi.clone(), new_u, cap),
        };
        new_fields.push(new_field);
    }

    Some(Term::apps(
        Term::cnst(ctor_name.clone(), ctor_ls.clone()),
        ty_args.into_iter().chain(new_fields),
    ))
}

// ============================================================================
// Phase 3.12: `transp` through a `Glue` line (computational univalence) —
// INVESTIGATED AND DECLINED (Target C).
// ============================================================================
//
// This section documents the CCHM `transp^{i.Glue …}` rule — including its
// specialization to exactly the `ua`-shaped line `transp (λi. ua A B e @ i) a0`
// — and the precise, structural reason neither is wired into
// `reduce.rs`/`nbe.rs` this pass. Nothing below changes `Term::Transp`'s
// behavior: a `transp` through a `Glue` line (`ua`-shaped or otherwise) stays
// **stuck**, exactly as before this pass. Per the standing instruction, an
// honest decline with a precise diagnosis is the reported outcome — no new
// reduction rule, no pattern-matched shortcut, is added to the trusted core.
//
// # The goal, restated precisely
//
// `crate::glue::ua` builds `ua A B e := ⟨i⟩ Glue B [(i=0)↦(A,e),(i=1)↦(B,idE)]`,
// and `crate::cubical::transport(p, a) := transp (λi. p @ i) ⊥ a`. Composing
// them: `transport (ua A B e) a0` elaborates to
//
// ```text
//   Transp( PApp(PLam(Glue B [(i=0)↦(A,e),(i=1)↦(B,idEquiv B)]), Var(0)), ⊥, a0 )
// ```
//
// whose family, once its outer `PApp(PLam …, Var 0)` β-redex is peeled (an
// ordinary, unconditionally sound simplification — see `Term::PApp`'s own
// β-rule in `reduce.rs`), is exactly `i.Glue B [(i=0)↦(A,e),(i=1)↦(B,idEquiv B)]`.
// The goal is for this to reduce to `Equiv.f A B e a0` — the "propositions as
// types" content of univalence being *computational*, not merely provable.
//
// # Why the general CCHM rule doesn't apply directly
//
// CCHM (§6.4) states `transp`/`comp` through `i.Glue (A i) [φ(i) ↦ (T(i), w(i))]`
// for a *single* cofibration `φ` that may vary continuously in `i`, with a
// *single* type family `T` defined (only) where `φ` holds, and a *single*
// equivalence family `w : T ≃ A` likewise defined only there. Spelled out, the
// rule composes three things: (1) a transport of the *base* `A(i)` along `i`
// (needed whenever `φ` fails to hold throughout — the base is where the result
// ultimately "lives" once glued data runs out); (2) a transport of `T(i)` along
// `i`, valid only under `φ`; and (3) a correction term built from `w`'s
// homotopies (`sec`/`ret`) via an `hcomp` in the base type `A`, because the two
// transports from (1)/(2) need not agree on the nose where they overlap — only
// up to the equivalence's own coherence data. This is *exactly* the same
// per-type-former Kan recursion this module's top-level doc already lists as
// blocked (`comp`, "composition along a varying family") — a real
// `transp^Glue`/`comp^Glue` is not a special case bolted onto `Glue` alone; it
// is CCHM's `Π`/`PathP`-style filling rule *for* `Glue`, requiring the same
// `hcomp`-in-the-codomain machinery `transp_pi_rule`/`hcomp_pi_rule` needed for
// `Π`, but now composed with `Equiv`'s bi-invertibility data on top.
//
// `ua`'s line does *not* sidestep this. It looks simpler — the base `B` is
// syntactically **constant** in `i` (so component (1) above is trivially the
// identity, by the very regularity rule this module already implements), and
// each branch's `T`/`w` is *also* individually constant (`A`/`e` on `(i=0)`,
// `B`/`idEquiv B` on `(i=1)`) — but `ua`'s two branches sit on **complementary,
// individually-decided** faces `(i=0)` and `(i=1)`, not on one face `φ(i)` that
// is *itself* varying continuously with a single, once-only-defined `T`. There
// is no single `T(i)` connecting `A` to `B` continuously across the interval to
// hand to a Kan filling rule at all — the "family" only exists as two disjoint,
// boundary-only facts. Concretely: at any *generic* (undecided) point of the
// interval — the one place a genuine `transp^Glue` filling rule must produce
// data — `Glue B […]` is **stuck** (see `crate::term::Term::Glue`'s doc and
// `glue.rs`'s `glue_open_phi_stays_stuck` test): there is no canonical element
// of it to fill with, and no `Term::GlueIntro` (`glue`, the introduction form)
// exists yet in this kernel to construct one (see `glue.rs`'s module doc,
// "Deferred"). A sound `transp^Glue` rule would need to *produce* an
// intermediate glued value at that generic point (via `hcomp`+`glue`) and only
// then observe its `i0`/`i1` boundaries collapse to `A`/`B` — it cannot instead
// jump straight from "the boundaries are `A` and `B`" to "the answer is
// `Equiv.f a0`" without that intermediate construction, because nothing in this
// kernel has verified that shortcut is *definitionally* the same thing the
// general rule would produce.
//
// # Why a syntax-matched "ua-shaped shortcut" is not a sound alternative
//
// The tempting alternative — special-case `reduce.rs`'s `Term::Transp` arm to
// recognize the literal syntactic shape `Glue B [(i=0)↦(A,e),(i=1)↦(B,idEquiv
// B)]` and rewrite straight to `Equiv.f A B e a0` — was considered and
// rejected. Two independent problems:
//
// 1. **It would be a new axiom, not a derived computation.** Every other rule
//    in this module (`transp_pi_rule`, `hcomp_pi_rule`, `hcomp_pathp_rule`,
//    `transp_inductive_rule`, `hcomp_inductive_rule`) is *sound by
//    construction*: each is checked (see each rule's own doc, point "type
//    preservation") to independently re-typecheck to the *same* type the
//    original stuck term already had, using only primitives (`Transp`,
//    `HComp`, ordinary `App`/`Lam`) whose own soundness is separately
//    established. A "pattern-match on `ua`'s shape, output `Equiv.f a0`" rule
//    has no such derivation — it would be asserting, by fiat, the specific
//    mathematical *fact* "`transport(ua e) = e.f`" as a new primitive
//    reduction, rather than deriving it from `Glue`'s own Kan structure. That
//    fact is true in full cubical type theory, but true-and-unimplemented is
//    exactly the gap Target C exists to report honestly, not paper over with a
//    syntactically-scoped special case that happens to be independently
//    known-correct.
//
// 2. **It cannot be checked by this module's own soundness discipline.** Every
//    existing rule's soundness argument leans on "the built term re-typechecks
//    to the stuck term's own type from scratch" (point 2 in each rule's doc) —
//    a mechanical, adversarially-testable check. A hard-coded `ua`-shape
//    rewrite *would* pass that specific check (`Equiv.f A B e a0 : B` is easy
//    to confirm), so the usual test would not catch what's actually missing:
//    there is no way, with the primitives available (no `Glue`
//    `hcomp`/`comp`, no `glue` intro), to verify the *stronger* property every
//    other Kan rule in this module satisfies implicitly — that the rule
//    computes the value a *fully general* `transp^Glue`/`comp^Glue`
//    implementation would have computed, not merely *some* type-correct
//    value. Shipping a rule whose correctness cannot be checked against the
//    general construction it is supposedly a special case of is precisely the
//    "REVERT anything you cannot fully stand behind" situation the task
//    describes.
//
// # What's confirmed unaffected (non-regression)
//
// [`kernel_tests::transp_through_ua_line_stays_stuck`] and
// [`kernel_tests::transp_through_ua_line_cannot_smuggle_a_false_equation`]
// below pin down that `transport (ua A B e) a0` — for both `idEquiv` and a
// genuinely distinct pair `A ≠ B` — remains a stuck `Transp`/well-typed neutral
// under both the reducer and NbE (identical behavior to every other
// not-yet-covered `transp` shape, e.g. a `Σ`/record family), and that this
// stuck-ness cannot be abused to prove a false equation between distinct
// closed `Nat`s — the same anti-`False` battery every other phase in this
// module runs, confirming the *absence* of a Glue-transport rule is exactly as
// safe as its presence would need to be.
//
// # What this leaves for a future pass
//
// Target A (the fully general `transp`/`comp^Glue`) subsumes Target B (the
// `ua`-specialized case) precisely because — as argued above — there is no
// simpler, independently-derivable "just for `ua`" shortcut; both require the
// same missing prerequisites: `Term::GlueIntro`/`glue` (the introduction
// form), `hcomp` specialized to `Glue`, and a correction term built from
// `Equiv.sec`/`Equiv.ret`. Landing `Π`'s `comp` (composition along a varying
// family, already flagged as blocked by the Cartesian-interval `Π` reversal
// issue at this module's top) is a *harder* prerequisite than `Glue`'s Kan
// structure needs in isolation — `Glue`'s own filling rule does not require
// reversing `Π`, only `hcomp` in an *arbitrary* (here, the base `A`/`B`) type,
// which this module already has machinery for (`hcomp_pi_rule`,
// `hcomp_pathp_rule`, `hcomp_inductive_rule` all instantiate exactly that
// pattern for other type formers) — so a future `Glue`-specific `hcomp`/`comp`
// pass, followed by a `glue` introduction form, is the concrete next step, not
// blocked on resolving `Π`'s harder reversal problem first.
//
// ============================================================================
// Phase 3.13: `transp^Glue`/`ua`-transport RETRIED now that `Term::GlueIntro`
// exists — RE-INVESTIGATED AND DECLINED AGAIN, with the diagnosis corrected.
// ============================================================================
//
// The prerequisite Phase 3.12 named as missing — a `glue` introduction form —
// now exists (`Term::GlueIntro`, `crate::glue`'s "glue" tests, and the
// `unglue(glue…a) ↦ a` β-rule; see `glue.rs`'s module doc). This section
// re-examines whether that removes the obstruction, and reports precisely what
// is (and is not) now derivable. As before: nothing below changes `Term::Transp`
// or `Term::HComp`'s behavior — `transp` through any `Glue` line, `ua`-shaped or
// not, stays exactly as stuck as it was before this pass. No new reduction rule
// is added.
//
// # Correcting Phase 3.12's framing of the obstruction
//
// Phase 3.12's doc (above) argued the general rule doesn't apply to `ua`
// because "`ua`'s two branches sit on complementary, individually-decided faces
// … not on one face `φ(i)` that is itself varying continuously with a single …
// `T`." That framing overstates the obstruction: CCHM's `Glue` (and this
// kernel's own [`Term::Glue`]) is already defined for an arbitrary *system* of
// branches `[φ_1 ↦ (T_1,e_1), …, φ_n ↦ (T_n,e_n)]`, not just a single
// continuously-varying face — `ua`'s two-branch, disjoint-decided-face system is
// a perfectly ordinary instance of that general shape, not a structurally
// different one. The *real* content of `transp^Glue` is not "one face `T`
// varying continuously"; it is, for **each** branch `k`, independently:
//
//   1. transport the *base* `A(i)` from `i=0` to `i=1` (trivial here — `ua`'s
//      base is the syntactically constant `B`, so this is the identity, by the
//      regularity rule already implemented);
//   2. for the branch(es) whose `φ_k` holds at the source endpoint, transport
//      `T_k(i)` under `φ_k` (also trivial for `ua` — each branch's `T`/`e` is
//      individually constant: `A`/`e` throughout `(i=0)`, `B`/`idEquiv B`
//      throughout `(i=1)`); then
//   3. **glue** the transported `T`-result back onto the transported base via
//      `Term::GlueIntro`, correcting the (generally non-definitional) mismatch
//      between "transport-then-apply-`e`" and "apply-`e`-then-transport" using
//      `Equiv.sec`/`Equiv.ret`'s coherence data, composed via an `hcomp` **in
//      the base type**.
//
// So `Term::GlueIntro` genuinely does remove *one* real prerequisite (step 3's
// output shape now exists to construct at all). What it does *not* provide is
// step 3's *correction term* — an `hcomp` in the base type `B`, built from
// `Equiv.sec`/`Equiv.ret`, of exactly the shape `hcomp_pi_rule`/
// `hcomp_pathp_rule`/`hcomp_inductive_rule` each independently hand-build for
// their own type former. No `hcomp_glue_rule` (the `Glue`-specific analogue)
// exists in this module, and — critically — `ua`'s base `B` is an **opaque,
// caller-supplied type**, not fixed to `Π`/`PathP`/an inductive: a sound
// `transp^Glue` must build its correction `hcomp` *in whatever `B` the caller
// instantiated `ua` at*, which this module has no generic "hcomp in an
// arbitrary type" combinator for (only per-type-former specializations). Even
// though `ua`'s own soundness gates in this task only exercise `B = Nat`
// (where `hcomp_inductive_rule` *could* in principle supply that piece), wiring
// a `transp` rule for `Term::Glue`/`Term::Transp` into `reduce.rs`/`nbe.rs`
// that only works for inductive `B` and silently stays stuck (or, worse,
// panics) for `Π`/`PathP`/opaque-axiom `B` would be exactly the kind of
// partial, type-former-incomplete rule this module's top-level doc already
// rules out ("a wrong or partial computation rule" is treated the same as an
// unsound one — see this module's opening "deliberately MINIMAL sound core"
// section). Building `hcomp_glue_rule` generically (dispatching to
// `hcomp_pi_rule`/`hcomp_pathp_rule`/`hcomp_inductive_rule`/regularity as
// appropriate for whatever `B` turns out to be, with a *sound fallback* — stay
// stuck — for a `B` none of those cover) is therefore the concrete remaining
// prerequisite, not yet attempted this pass: it is real, non-trivial new Kan
// machinery (its own soundness argument, its own adversarial test suite,
// mirroring each of `hcomp_pi_rule`'s/`hcomp_pathp_rule`'s own point-by-point
// doc), not a one-line pattern match now that `glue` intro exists.
//
// # Why no `ua`-scoped shortcut is shipped either, even now
//
// The same two objections Phase 3.12 raised against a hard-coded
// `Glue B [(i=0)↦(A,e),(i=1)↦(B,idEquiv B)] ↝ Equiv.f A B e a0` pattern-match
// still apply verbatim: (1) it would assert the univalence computation rule as
// a new axiom rather than derive it from `Glue`'s Kan structure — `Term::GlueIntro`
// changes *what can be constructed*, not *what has been derived* — and (2) this
// module's soundness discipline requires each rule's output to be checked
// against what the *general* rule would have produced, which — absent
// `hcomp_glue_rule` — there is still nothing to check against. Constructing the
// correction term *by hand* for exactly `ua`'s shape (using `GlueIntro` +
// `Equiv.sec`/`ret` + `hcomp_inductive_rule`/regularity, scoped to constant
// bases only) was attempted as a design sketch during this pass and set aside:
// it independently re-derives (rather than reuses) a piece of the general
// `Glue`-`hcomp` rule for exactly one caller, which is precisely the "special
// case bolted on rather than derived" pattern Phase 3.12 already rejected —
// doing it honestly means building the general `hcomp_glue_rule` first, then
// specializing, not the reverse.
//
// # Non-regression (re-confirmed with `GlueIntro` now present)
//
// [`kernel_tests::transp_through_ua_line_stays_stuck_even_with_glue_intro_available`]
// below re-runs Phase 3.12's two pins with `Term::GlueIntro` now installed in
// the environment (via `declare_equiv`/`ua`/`crate::glue`), confirming its
// presence alone does not perturb `transp`'s behavior on a `Glue` line: still a
// stuck `Term::Transp` under both the reducer and NbE, and still safe against
// the anti-`False` battery.
//
// # Updated next step
//
// Unchanged in spirit from Phase 3.12, sharpened: (1) a generic `hcomp_glue_rule`
// (dispatching to existing per-type-former `hcomp` rules for the base, with a
// sound stuck fallback when the base's shape isn't covered), then (2) a
// `transp_glue_rule` built from it plus `Equiv.sec`/`ret`, independently
// re-typechecked and reducer/NbE cross-checked exactly like every existing rule
// in this module — at which point `ua`'s case (constant base, two decided
// branches) falls out as the simplest possible instance, not a bespoke rule.

#[cfg(test)]
mod kernel_tests {
    use crate::face::Cof;
    use crate::kernel::Kernel;
    use crate::term::{name, Term};

    fn cn(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    /// `A B : Type 0`, `a b c : A`.
    fn base_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k.add_axiom("b", 0, cn("A")).unwrap();
        k.add_axiom("c", 0, cn("A")).unwrap();
        k
    }

    // ---- transp: the regularity rule ----

    /// `transp (λ_. A) ⊥ a : A` and definitionally reduces to `a` — the core
    /// payoff of this phase.
    #[test]
    fn transp_along_a_constant_family_typechecks_and_is_the_identity() {
        let k = base_env();
        let fam = cn("A").lift(1, 0); // doesn't mention the new interval binder
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("A")));
        assert!(k.def_eq(&t, &cn("a")));
    }

    /// Same, but with `φ = ⊤` — the guard's value must not matter for a genuinely
    /// constant family (it still reduces, since regularity never looks at `φ`).
    #[test]
    fn transp_along_a_constant_family_is_the_identity_regardless_of_phi() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let t = Term::transp(fam, Cof::top(), cn("a"));
        assert!(k.def_eq(&t, &cn("a")));
    }

    /// Differential check (this crate's standing convention): the trusted reducer
    /// and NbE agree on the regularity reduction.
    #[test]
    fn transp_regularity_agrees_between_reducer_and_nbe() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert!(reducer.is_def_eq(&t, &cn("a")));
        assert!(nbe.conv(&t, &cn("a")));
    }

    /// `check` also accepts `transp` at its reduced form's type (not just `infer`).
    #[test]
    fn transp_along_a_constant_family_checks_against_a() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        k.check(&t, &cn("A")).unwrap();
    }

    /// Sanity: a definition built from `transp` survives the independent recheck
    /// harness (mirrors Phase 1/2's equivalent coverage).
    #[test]
    fn transp_definitions_survive_independent_recheck() {
        let mut k = base_env();
        let fam = cn("A").lift(1, 0);
        k.add_definition("ta", 0, cn("A"), Term::transp(fam, Cof::bot(), cn("a"))).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 1);
    }

    // ---- transp: adversarial soundness tests ----

    /// **Adversarial**: a `transp` whose family genuinely varies (mentions the
    /// interval variable) stays **stuck** — it must NOT reduce to `a` (that would
    /// be exactly the unsound shortcut this module's doc describes and reverted).
    /// Built via `p @ Var(0)` for an axiomatized `p : Path (Sort 1) A B` (i.e. `A`
    /// and `B`, both `: Type 0`, connected by an — individually opaque, like any
    /// axiom — path *in the universe*).
    #[test]
    fn transp_along_a_type_level_path_axiom_does_not_smuggle_a_type_change() {
        let mut k = base_env();
        // p : Path (Type 0's own sort) A B  (A B : Type 0, i.e. both `: Sort 1`).
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        let fam = Term::papp(cn("p").lift(1, 0), Term::Var(0));
        // Sanity: this family genuinely mentions the interval variable, and its
        // endpoints are (via the Phase-1 boundary rule) A and B respectively —
        // otherwise this wouldn't be exercising the case at all.
        assert!(crate::term::mentions_var(&fam, 0));
        let fam_i0 = fam.instantiate(&Term::IZero);
        let fam_i1 = fam.instantiate(&Term::IOne);
        assert!(k.def_eq(&fam_i0, &cn("A")));
        assert!(k.def_eq(&fam_i1, &cn("B")));

        let t = Term::transp(fam, Cof::top(), cn("a"));
        // It still type-checks (infer succeeds, `a : A` matches `fam[i:=i0] ≡ A`)…
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("B")));
        // …but it must NOT reduce to `a` (which has type `A`, not `B`) — the
        // reducer/NbE must leave it stuck, not silently launder a type change.
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert!(!reducer.is_def_eq(&t, &cn("a")));
        assert!(!nbe.conv(&Term::app(Term::lam(cn("B"), Term::Var(0)), t.clone()).unfold_apps().0, &cn("a")));
        // Directly: whnf leaves the head as a stuck `Transp`, not `a`.
        let whnf = reducer.whnf(&t);
        assert!(matches!(whnf, Term::Transp(..)), "expected a stuck Transp, got {}", whnf.pretty());
        // Directly against `family_is_constant` itself (not just its call sites):
        // the axiom-headed family must be judged non-constant even after full
        // computation — the fresh neutral standing in for the interval variable
        // propagates straight through the opaque `PApp(p, ·)` head (no `PLam`/
        // ι-rule ever fires on it) and survives into the normal form.
        assert!(!super::family_is_constant(k.env(), &Term::papp(cn("p").lift(1, 0), Term::Var(0))));
    }

    /// **Adversarial, normalization-aware regularity specifically**: wrapping the
    /// same type-level path axiom attack in extra, genuinely-reducible scaffolding
    /// (an outer `App(Lam(...), ...)` β-redex around the family, and the family
    /// itself built through an extra `refl`-composed layer) must still leave
    /// `family_is_constant` — and hence the `Transp` it guards — stuck. This is the
    /// case the *original*, purely syntactic regularity check could never even be
    /// tempted by (it never reduces anything), but the new normalization-aware
    /// extension explicitly computes through scaffolding like this, so it is the
    /// one that most needs a dedicated adversarial pin: over-firing here would mean
    /// the fresh interval-neutral got silently "reduced away" through the opaque
    /// `p`, which must never happen.
    #[test]
    fn normalization_aware_regularity_does_not_smuggle_a_type_change_through_scaffolding() {
        let mut k = base_env();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        // `(λ_:A. p @ i) a`-shaped scaffolding: a genuinely-collapsible outer
        // β-redex (an identity-shaped `Lam`/`App` around the family) wrapped around
        // the still-opaque `p @ i` — the redex itself reduces away (that's the
        // "scaffolding"), but must NOT drag the interval dependency on the opaque
        // axiom `p` away with it.
        let scaffolded = Term::app(Term::lam(cn("A"), Term::papp(cn("p").lift(2, 0), Term::Var(1))), cn("a"));
        // Sanity: after the outer β-redex reduces, this is exactly `p @ i` (`i` =
        // the outer transp binder, `Var(0)`) — the same family the sibling test
        // above (`transp_along_a_type_level_path_axiom_does_not_smuggle_a_type_change`)
        // exercises directly, just reached here through an extra layer of
        // genuinely-reducible scaffolding.
        let reducer = crate::reduce::Reducer::new(k.env());
        assert_eq!(reducer.whnf(&scaffolded), Term::papp(cn("p"), Term::Var(0)));
        assert!(
            !super::family_is_constant(k.env(), &scaffolded),
            "the opaque path axiom must never be judged constant, even through extra reducible scaffolding"
        );
        let t = Term::transp(scaffolded, Cof::top(), cn("a"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("B")));
        let whnf = reducer.whnf(&t);
        assert!(
            matches!(whnf, Term::Transp(..)),
            "expected a stuck Transp even through scaffolding, got {}",
            whnf.pretty()
        );
        assert!(!reducer.is_def_eq(&t, &cn("a")));
    }

    /// **Adversarial**: no closed, non-stuck term of `Path Type A B` can itself be
    /// *constructed* from `a : A` alone (this is really Phase 1's guarantee, but
    /// re-confirmed here since `transp` is the thing that would try to *use* such
    /// a path if one existed) — `refl` only ever proves reflexivity, so `A` and
    /// `B` (distinct axioms) stay unrelated absent an explicit (opaque, axiom-only)
    /// postulate.
    #[test]
    fn no_path_between_distinct_types_is_derivable_without_an_axiom() {
        let k = base_env();
        assert!(!k.def_eq(&cn("A"), &cn("B")));
        assert!(k
            .check(&crate::cubical::refl(&cn("A")), &Term::path(Term::typ(1), cn("A"), cn("B")))
            .is_err());
    }

    /// **Adversarial**: `transp` cannot manufacture a proof of `Path A a b` for
    /// distinct closed `a`/`b` (i.e. it doesn't let you sidestep Phase 1's
    /// "no `False`" guarantee for ordinary paths either) — since `transp`'s only
    /// firing rule is the identity, the result is always def-eq to the very `a`
    /// you started with; it can never produce a *different* closed value.
    #[test]
    fn transp_never_produces_a_value_other_than_its_own_input() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        assert!(k.def_eq(&t, &cn("a")));
        assert!(!k.def_eq(&t, &cn("b")));
        assert!(!k.def_eq(&t, &cn("c")));
    }

    /// **Adversarial**: `transp`'s declared source type is enforced — you cannot
    /// check `a : A` as if it already had a *different*, unrelated type by
    /// wrapping it in `transp` with a mismatched claimed source.
    #[test]
    fn transp_source_type_mismatch_is_rejected() {
        let k = base_env();
        // family is (lifted) B, but `a : A` — a genuine mismatch, no path involved.
        let fam = cn("B").lift(1, 0);
        let t = Term::transp(fam, Cof::bot(), cn("a"));
        assert!(k.infer(&t).is_err());
    }

    // ---- hcomp: the trivial-system rule ----

    /// `hcomp A ⊤ (⟨i⟩ a) a : A` and reduces to `a` (the single-branch, always-on
    /// system case).
    #[test]
    fn hcomp_with_top_guard_reduces_to_the_lines_value_at_i1() {
        let k = base_env();
        // `u`'s type is `Partial φ A`, only ever inhabited by a `Sys` (see
        // `crate::face`) — `⟨i⟩ [⊤ ↦ a]`, a constant line built through a system.
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("a"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &cn("A")));
        assert!(k.def_eq(&t, &cn("a")));
    }

    /// A genuinely varying (but still well-typed and cap-agreeing) line: `⟨i⟩
    /// [(i=i0)↦a, (i=i1)↦b]`— wait, that wouldn't cap-agree with `a` unless `a ≡
    /// b`. Use `[⊤ ↦ a]` reshaped so the line is trivially `a` at every point but
    /// built through a `Sys`, exercising `Sys`-inside-`hcomp` end to end.
    #[test]
    fn hcomp_line_built_from_a_system_reduces_correctly() {
        let k = base_env();
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("a"));
        assert!(k.def_eq(&t, &cn("a")));
    }

    /// Differential check: reducer and NbE agree on the trivial `hcomp` rule.
    #[test]
    fn hcomp_trivial_rule_agrees_between_reducer_and_nbe() {
        let k = base_env();
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("a"));
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        assert!(reducer.is_def_eq(&t, &cn("a")));
        assert!(nbe.conv(&t, &cn("a")));
    }

    /// Sanity: an `hcomp`-built definition survives the independent recheck
    /// harness.
    #[test]
    fn hcomp_definitions_survive_independent_recheck() {
        let mut k = base_env();
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        k.add_definition("ha", 0, cn("A"), Term::hcomp(cn("A"), Cof::top(), u, cn("a"))).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 1);
    }

    // ---- hcomp: well-formedness / adversarial tests ----

    /// The cap-agreement obligation (`u[i:=i0] ≡ u0`) is enforced — a line whose
    /// value at `i0` disagrees with the supplied cap is rejected.
    #[test]
    fn hcomp_rejects_a_cap_mismatch() {
        let k = base_env();
        let u = cn("b").lift(1, 0); // constant line ⟨i⟩ b
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("a")); // cap claims `a`, line is `b`
        assert!(k.infer(&t).is_err());
    }

    /// `hcomp` with `φ = ⊥` (an empty system) still requires a well-typed `u`/`u0`
    /// pair (cap agreement is required *unconditionally* — see the module doc for
    /// why this stricter-than-textbook rule keeps the design simple and sound) but
    /// never *reduces* (no branch is ever decided true) — it stays stuck, valid
    /// inert data, exactly like an unresolved `Sys`.
    #[test]
    fn hcomp_with_bot_guard_typechecks_but_stays_stuck() {
        let k = base_env();
        // `⊥` trivially entails the coverage obligation for *any* branches, so a
        // `⊤`-guarded (i.e. always-reducible-once-forced) line still checks fine
        // against `Partial ⊥ A` — but the outer `hcomp`'s own guard (`⊥`) is what
        // gates the *hcomp* reduction rule, and that's never decided true.
        let u = Term::sys(vec![(Cof::top(), cn("a").lift(1, 0))]);
        let t = Term::hcomp(cn("A"), Cof::bot(), u, cn("a"));
        k.infer(&t).unwrap(); // well-typed (cap agrees: ⟨i⟩[⊤↦a] at i0 reduces to a)
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        assert!(matches!(whnf, Term::HComp(..)), "expected a stuck HComp, got {}", whnf.pretty());
    }

    /// **Adversarial**: `hcomp` cannot conjure an inhabitant of an unrelated,
    /// otherwise-uninhabited axiom type `E` — the only way to populate `u0`/`u` is
    /// with an already-well-typed-at-`E` term, and there is none to reuse (`a` is
    /// at the wrong type `A`, not `E`).
    #[test]
    fn hcomp_cannot_conjure_an_inhabitant_of_an_unrelated_axiom() {
        let mut k = base_env();
        k.add_axiom("E", 0, Term::typ(0)).unwrap();
        let u = cn("a").lift(1, 0); // `a : A`, not `: E`
        let t = Term::hcomp(cn("E"), Cof::top(), u, cn("a"));
        assert!(k.infer(&t).is_err());
    }

    /// **Adversarial**: routing an opaque axiom of `Partial`-type through `hcomp`
    /// (attempting to sidestep the cap check by aliasing `u` and `u0` to the very
    /// same free-standing neutral) is rejected — `u0`'s independent `check(u0,
    /// ty)` obligation fails since the axiom's own type is `Partial ⊤ A`, not `A`
    /// (see the module doc's `hcomp` soundness argument for the general case).
    #[test]
    fn hcomp_opaque_partial_typed_axiom_cannot_bypass_the_cap_check() {
        let mut k = base_env();
        k.add_axiom("q", 0, Term::partial(Cof::top(), cn("A"))).unwrap();
        let u = cn("q").lift(1, 0); // doesn't mention the interval binder
        let t = Term::hcomp(cn("A"), Cof::top(), u, cn("q")); // u0 := q, at the wrong type
        assert!(k.infer(&t).is_err());
    }

    /// **Adversarial**: two structurally-distinct `hcomp` terms (different caps)
    /// are not equated merely by both being *some* `hcomp` of the same type — the
    /// structural `compare`/`is_def_eq` cases stay componentwise.
    #[test]
    fn distinct_hcomp_terms_are_not_conflated() {
        let k = base_env();
        let ua = cn("a").lift(1, 0);
        let ub = cn("b").lift(1, 0);
        let ta = Term::hcomp(cn("A"), Cof::top(), ua, cn("a"));
        let tb = Term::hcomp(cn("A"), Cof::top(), ub, cn("b"));
        assert!(!k.def_eq(&ta, &tb));
    }

    /// **Adversarial**: `I` still cannot be smuggled through `transp`/`hcomp` as a
    /// `Π` domain or as ordinary data (mirrors Phase 1/2's equivalent checks) —
    /// this phase adds no new way to make `I` fibrant.
    #[test]
    fn interval_still_cannot_be_a_pi_domain_with_kan_ops_in_scope() {
        let mut k = Kernel::new();
        let err = k.add_axiom("bad", 0, Term::pi(Term::I, Term::typ(0))).unwrap_err();
        assert!(err.contains('I'), "got: {err}");
    }

    /// **Adversarial**: `transp`'s guard `φ` must still be a genuine cofibration
    /// over interval-classified subjects — it cannot smuggle ordinary data through
    /// an atom's subject position (mirrors `Partial`'s equivalent check).
    #[test]
    fn transp_rejects_a_non_interval_cofibration_subject() {
        let k = base_env();
        let fam = cn("A").lift(1, 0);
        let bad_phi = Cof::eq0(cn("a")); // `a : A`, not `: I`
        let t = Term::transp(fam, bad_phi, cn("a"));
        assert!(k.infer(&t).is_err());
    }

    // ---- transp: the `Π`-case filling rule (Phase 3.6, see the module doc above) ----

    fn pi_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("f", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        k.add_axiom("a", 0, cn("A")).unwrap();
        k
    }

    /// Build `λi. (p @ i) → (p @ i)` — a `Π` family whose domain *and* codomain both
    /// walk the same type-level path `p` (an axiom of type `Path Type A B`, or
    /// `refl A`). `p_amb` is `p` as it lives in the *ambient* context (no interval
    /// binder in scope yet). The domain lives in frame `[i, Γ]` (`p` lifted by one
    /// to sit under the fresh interval binder); the codomain lives in frame `[x, i,
    /// Γ]` (`p` lifted by two, referencing `i` as `Var(1)`, `x` unused) — built
    /// directly at the right frame rather than derived from the domain via `lift`
    /// (which would put `x`/`i` in the wrong relative order; see
    /// `Term::subst_ctx_keep_frame`'s doc for the general index bookkeeping this
    /// mirrors).
    fn path_pi_family(p_amb: &Term) -> Term {
        let dom = Term::papp(p_amb.lift(1, 0), Term::Var(0));
        let cod = Term::papp(p_amb.lift(2, 0), Term::Var(1));
        Term::pi(dom, cod)
    }

    /// **Refl-agreement, now via normalization-aware regularity**: transporting
    /// `f : A → A` along a `Π` family connected by `refl A` (syntactically
    /// *varying* — `mentions_var` sees the interval variable in `(refl A) @ i`, so
    /// the *original*, purely syntactic half of the regularity rule does not fire on
    /// its own — but *semantically*, hence now also *computationally* via
    /// `crate::kan::family_is_constant`, constant) type-checks at exactly `A → A`
    /// and reduces straight to `f` itself: the whole `Π`-headed family normalizes to
    /// the constant `A → A`, so `family_is_constant` fires *before* the `Π`-case
    /// filling rule is even consulted — a strictly better result than routing
    /// through [`transp_pi_rule`] (which would produce a semantically-equal but
    /// differently-shaped `Lam`, per this test's previous, narrower version).
    ///
    /// [`coe`]'s own reparametrized family `dom[i := (r∧~k)∨(r'∧k)]` still always
    /// syntactically mentions the fresh connection binder `k`, and — unlike a
    /// top-level `Transp`'s family — is genuinely *not* constant in the general case
    /// (only at the special boundary `r=r'`, which `family_is_constant`'s
    /// normalization *would* also catch if invoked there; `coe` isn't the direct
    /// object of this test, its own `Π`-rule call sites are covered elsewhere).
    #[test]
    fn transp_pi_rule_typechecks_on_a_refl_connected_pi_family() {
        let k = pi_env();
        let fam = path_pi_family(&crate::cubical::refl(&cn("A")));
        assert!(crate::term::mentions_var(&fam, 0), "sanity: family is syntactically varying");
        let t = Term::transp(fam, Cof::bot(), cn("f"));

        // Type is (as always, independent of which reduction rule fires) A → A.
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &Term::arrow(cn("A"), cn("A"))));

        // Normalization-aware regularity fires directly: whnf is exactly `f`, not a
        // stuck `Transp` and not a `Π`-rule-built `Lam`.
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        assert_eq!(whnf, cn("f"), "expected regularity to fire, got {}", whnf.pretty());
        let reinferred = k.infer(&whnf).unwrap();
        assert!(k.def_eq(&reinferred, &Term::arrow(cn("A"), cn("A"))));
    }

    /// **Concrete Π-transport**: build a genuine type-level path `p : Path Type A B`
    /// (an axiom — Phase 1's `Path` in the universe, same device the module doc's
    /// own anti-smuggling test above uses), transport `f : A → A` along the `Π`
    /// family `λi. p@i → p@i`, and confirm the transported function type-checks at
    /// the *target* arrow type `B → B` and genuinely applies there (re-checked from
    /// scratch on the reduced normal form, not merely trusted from the original
    /// `Transp` node's `infer`).
    #[test]
    fn transp_pi_rule_transports_a_concrete_function() {
        let mut k = pi_env();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        k.add_axiom("b", 0, cn("B")).unwrap();
        let fam = path_pi_family(&cn("p"));
        let t = Term::transp(fam, Cof::top(), cn("f"));

        let ty = k.infer(&t).unwrap();
        let expected_ty = Term::arrow(cn("B"), cn("B"));
        assert!(k.def_eq(&ty, &expected_ty));

        // The Π rule fires…
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        assert!(matches!(whnf, Term::Lam(..)), "expected the Π rule to fire, got {}", whnf.pretty());

        // …and the reduced term *independently* re-typechecks at B → B (subject
        // reduction, checked from scratch — see the module doc's soundness point 2).
        let reinferred = k.infer(&whnf).unwrap();
        assert!(k.def_eq(&reinferred, &expected_ty));

        // It genuinely applies at B (the transported domain), producing a
        // well-typed `B`-classified result.
        let applied = Term::app(whnf.clone(), cn("b"));
        let applied_ty = k.infer(&applied).unwrap();
        assert!(k.def_eq(&applied_ty, &cn("B")));
    }

    /// Differential check (this crate's standing convention): the trusted reducer
    /// and NbE agree on the `Π`-rule reduction (same setup as the concrete-transport
    /// test above).
    #[test]
    fn transp_pi_rule_agrees_between_reducer_and_nbe() {
        let mut k = pi_env();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        k.add_axiom("b", 0, cn("B")).unwrap();
        let fam = path_pi_family(&cn("p"));
        let t = Term::transp(fam, Cof::top(), cn("f"));

        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        let applied = Term::app(t.clone(), cn("b"));
        // Both engines must land the application on the same (up-to-conversion)
        // `B`-classified result.
        let whnf_applied = reducer.whnf(&applied);
        assert!(nbe.conv(&applied, &whnf_applied));
    }

    /// Sanity: a definition built by transporting `f` through a genuine `Π`-typed
    /// family survives the independent recheck harness.
    #[test]
    fn transp_pi_rule_definitions_survive_independent_recheck() {
        let mut k = pi_env();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        let fam = path_pi_family(&cn("p"));
        let t = Term::transp(fam, Cof::top(), cn("f"));
        k.add_definition("transported_f", 0, Term::arrow(cn("B"), cn("B")), t).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 1);
    }

    /// **Adversarial (anti-`False`, Π-case)**: the transported function must *not*
    /// be usable at the *source* domain `A` (only the genuinely path-connected
    /// target `B`) — i.e. the rule doesn't erase the domain change, and it doesn't
    /// let you apply the "new" function to old-typed data and get something
    /// type-incorrect silently accepted.
    #[test]
    fn transp_pi_rule_transported_function_rejects_the_source_domain() {
        let mut k = pi_env();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        let fam = path_pi_family(&cn("p"));
        let t = Term::transp(fam, Cof::top(), cn("f"));
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        // Applying the transported (now `B → B`) function to `a : A` must be rejected.
        let bad_app = Term::app(whnf, cn("a"));
        assert!(k.infer(&bad_app).is_err());
    }

    /// **Adversarial (anti-`False`, Π-case)**: without an actual path axiom
    /// connecting two types, the `Π` rule cannot be used to move a function between
    /// *unrelated* types — attempting to claim `f : A → A` also inhabits `C → C`
    /// for an unrelated, path-free axiom `C` is rejected exactly as it always was
    /// (this phase changes no *checking* rule — see the module doc — only adds a
    /// reduction; `infer`'s pre-existing `check(a, family[i:=i0])` obligation is the
    /// one thing guarding this, completely unmodified by this phase).
    #[test]
    fn transp_pi_rule_cannot_smuggle_a_function_to_an_unrelated_type() {
        let mut k = pi_env();
        k.add_axiom("C", 0, Term::typ(0)).unwrap();
        // No path between A and C: `fam := λ_. C → C` (constant, no `i` at all —
        // deliberately not even syntactically varying, to isolate the check being
        // tested: the *source*-type obligation, not reduction).
        let fam = Term::arrow(cn("C"), cn("C")).lift(1, 0);
        let t = Term::transp(fam, Cof::top(), cn("f")); // f : A → A, not C → C
        assert!(k.infer(&t).is_err());
    }

    /// **Adversarial (anti-`False`, Π-case)**: the transported term is not
    /// definitionally equal to the original `f` (their types genuinely differ, `A →
    /// A` vs `B → B`, and `A`/`B` are distinct unrelated axioms) — the rule doesn't
    /// quietly conflate the source and target functions as if nothing changed.
    #[test]
    fn transp_pi_rule_transported_function_is_not_the_original() {
        let mut k = pi_env();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        assert!(!k.def_eq(&cn("A"), &cn("B")));
        let fam = path_pi_family(&cn("p"));
        let t = Term::transp(fam, Cof::top(), cn("f"));
        // Structurally: a whnf'd `Lam` is never going to be `is_def_eq` to the bare
        // constant `f` (different term shapes, and — decisively — different types).
        assert!(!k.def_eq(&t, &cn("f")));
    }

    // ---- hcomp: the `Π`-case filling rule (Phase 3.7, see the module doc above) ----

    /// **`hcomp_pi_rule` itself returns `None` for a non-`Sys` line** — checked at the
    /// pure-function level (bypassing the full checker) since, in this kernel, a
    /// well-typed `hcomp` whose line `u` is *not* a literal `Sys` necessarily has an
    /// inferred type of `Partial φ ty` (never reducible back to plain `ty` — `Partial`
    /// has no elimination rule here, see `hcomp_pi_rule`'s module doc), so its cap
    /// `u[i:=i0]` can never be definitionally equal to a plain-`ty`-typed `u0` other
    /// than in degenerate, non-representative ways — there is no well-typed
    /// non-`Sys`-line `hcomp`-at-`Π` term to exercise this through the full checker
    /// (see `hcomp_opaque_partial_typed_axiom_cannot_bypass_the_cap_check` above for
    /// the general form of that rejection). Confirms the conservative "only a literal
    /// `Sys` pushes through" guard directly instead.
    #[test]
    fn hcomp_pi_rule_returns_none_for_a_non_sys_line() {
        let dom = cn("A");
        let cod = cn("A").lift(1, 0);
        let u = cn("f").lift(1, 0); // constant line ⟨i⟩ f, not a literal Sys
        assert!(super::hcomp_pi_rule(&dom, &cod, &Cof::bot(), &u, &cn("f")).is_none());
    }

    /// **The `Π` rule fires** on a `Sys`-built line at a `Π` type, producing a literal
    /// `Lam`, which independently re-typechecks (subject reduction, checked from
    /// scratch — mirrors `transp_pi_rule_transports_a_concrete_function`'s discipline)
    /// at the *original* `Π` type, and genuinely applies.
    #[test]
    fn hcomp_pi_rule_transports_a_concrete_partial_function() {
        let k = pi_env();
        let u = Term::sys(vec![(Cof::top(), cn("f").lift(1, 0))]); // ⟨i⟩ [⊤ ↦ f]
        // φ = ⊥ so the trivial (`φ=⊤`) rule does NOT fire first — this isolates the
        // Π rule specifically (see the module doc's "Agreement" point: the two rules
        // are mutually exclusive by construction, trivial always tried first).
        let t = Term::hcomp(Term::arrow(cn("A"), cn("A")), Cof::bot(), u, cn("f"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &Term::arrow(cn("A"), cn("A"))));

        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        assert!(matches!(whnf, Term::Lam(..)), "expected the Π rule to fire, got {}", whnf.pretty());

        // Subject reduction: the reduced Lam independently re-typechecks at A → A.
        let reinferred = k.infer(&whnf).unwrap();
        assert!(k.def_eq(&reinferred, &Term::arrow(cn("A"), cn("A"))));

        // It genuinely applies at `a : A`, producing a well-typed `A`-classified
        // (if not further reduced, since φ = ⊥ never decides) result.
        let applied = Term::app(whnf, cn("a"));
        let applied_ty = k.infer(&applied).unwrap();
        assert!(k.def_eq(&applied_ty, &cn("A")));
    }

    /// Differential check (this crate's standing convention): the trusted reducer and
    /// NbE agree on the `Π`-rule reduction.
    #[test]
    fn hcomp_pi_rule_agrees_between_reducer_and_nbe() {
        let k = pi_env();
        let u = Term::sys(vec![(Cof::top(), cn("f").lift(1, 0))]);
        let t = Term::hcomp(Term::arrow(cn("A"), cn("A")), Cof::bot(), u, cn("f"));
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        let applied = Term::app(t.clone(), cn("a"));
        let whnf_applied = reducer.whnf(&applied);
        assert!(nbe.conv(&applied, &whnf_applied));
    }

    /// **Agreement with the trivial `⊤` rule**: when `φ` genuinely is `⊤` (so the
    /// trivial rule fires, not the Π rule — priority order, see the module doc), the
    /// value produced is still the *same* (up to conversion, applied at a concrete
    /// argument) as what the Π rule *would* have built had it fired instead — checked
    /// by calling `hcomp_pi_rule` directly (bypassing the reducer's priority order) and
    /// comparing.
    #[test]
    fn hcomp_pi_rule_agrees_with_the_trivial_rule_when_phi_is_top() {
        let k = pi_env();
        let u = Term::sys(vec![(Cof::top(), cn("f").lift(1, 0))]);
        let t = Term::hcomp(Term::arrow(cn("A"), cn("A")), Cof::top(), u.clone(), cn("f"));
        let reducer = crate::reduce::Reducer::new(k.env());

        // The trivial rule's own answer, applied at `a`.
        let trivial_applied = Term::app(t.clone(), cn("a"));
        let trivial_whnf = reducer.whnf(&trivial_applied);

        // What the Π rule would have built, had it fired, applied at `a`.
        let Term::Pi(_g, dom, cod) = Term::arrow(cn("A"), cn("A")) else { unreachable!() };
        let pi_built = super::hcomp_pi_rule(&dom, &cod, &Cof::top(), &u, &cn("f")).unwrap();
        let pi_applied = Term::app(pi_built, cn("a"));
        let pi_whnf = reducer.whnf(&pi_applied);

        assert!(reducer.is_def_eq(&trivial_whnf, &pi_whnf));
    }

    /// Sanity: an `hcomp`-built definition using the `Π` rule survives the independent
    /// recheck harness.
    #[test]
    fn hcomp_pi_rule_definitions_survive_independent_recheck() {
        let mut k = pi_env();
        let u = Term::sys(vec![(Cof::top(), cn("f").lift(1, 0))]);
        let t = Term::hcomp(Term::arrow(cn("A"), cn("A")), Cof::bot(), u, cn("f"));
        k.add_definition("hf", 0, Term::arrow(cn("A"), cn("A")), t).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 1);
    }

    /// **Adversarial (anti-`False`, Π-case)**: `hcomp`'s `Π` rule cannot conjure an
    /// inhabitant of an unrelated, otherwise-uninhabited axiom type `E` — pushing `@x`
    /// through the system's branches only ever reuses already-well-typed-at-`ty`
    /// branch terms; there's no way to land at a type the source system never
    /// mentioned.
    #[test]
    fn hcomp_pi_rule_cannot_conjure_an_inhabitant_of_an_unrelated_axiom() {
        let mut k = pi_env();
        k.add_axiom("E", 0, Term::typ(0)).unwrap();
        // `u`'s branch is `f : A → A`, not `: A → E` — mismatched against the claimed
        // `hcomp` type `A → E`.
        let u = Term::sys(vec![(Cof::top(), cn("f").lift(1, 0))]);
        let t = Term::hcomp(Term::arrow(cn("A"), cn("E")), Cof::bot(), u, cn("f"));
        assert!(k.infer(&t).is_err());
    }

    /// **Adversarial**: two structurally-distinct `hcomp`-at-`Π` terms (different
    /// systems) are not equated merely by both reducing to *some* `Lam` of the same
    /// `Π` type — the built `Lam`s stay distinguishable when applied to distinct
    /// arguments (here, two systems that behave differently isn't set up directly;
    /// instead this pins that the same system applied to two *different* arguments
    /// does NOT get conflated — the branches aren't smeared together across
    /// applications).
    #[test]
    fn hcomp_pi_rule_does_not_conflate_branches_at_different_arguments() {
        let mut k = pi_env();
        k.add_axiom("g", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        assert!(!k.def_eq(&cn("f"), &cn("g")));
        let u = Term::sys(vec![(Cof::top(), cn("f").lift(1, 0))]);
        let t = Term::hcomp(Term::arrow(cn("A"), cn("A")), Cof::bot(), u, cn("f"));
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        // Applying the transported `f` must not be confused with an unrelated `g`.
        let applied_f = Term::app(whnf.clone(), cn("a"));
        let g_applied = Term::app(cn("g"), cn("a"));
        assert!(!k.def_eq(&applied_f, &g_applied));
    }

    /// **Adversarial**: `hcomp`'s cap-agreement check still gates the `Π` rule's own
    /// input — a `Sys`-built line whose cap doesn't match `u0` is rejected before the
    /// `Π` rule ever gets a chance to fire (this phase adds no new *checking* rule, so
    /// the pre-existing cap-agreement obligation is untouched).
    #[test]
    fn hcomp_pi_rule_input_still_requires_cap_agreement() {
        let mut k = pi_env();
        k.add_axiom("g", 0, Term::arrow(cn("A"), cn("A"))).unwrap();
        let u = Term::sys(vec![(Cof::top(), cn("g").lift(1, 0))]); // line is g
        let t = Term::hcomp(Term::arrow(cn("A"), cn("A")), Cof::bot(), u, cn("f")); // cap claims f
        assert!(k.infer(&t).is_err());
    }

    // ---- hcomp: the `PathP`-case rule — the naive CCHM assembled-system
    // construction, once (see the module doc's "Phase 3.8" section) adversarial
    // evidence that this kernel's *unconditional* `check_sys` compatibility
    // condition was too strict to accept it. `crate::check::Checker::check_sys`'s
    // compatibility condition is now **restriction-aware** (see `crate::face`'s
    // `restrict_clause_term` doc): two overlapping branches need only agree *after*
    // substituting the interval endpoints their overlap forces, which is exactly
    // the standard cubical "compatible system" condition. This test is the payoff:
    // the tube branch `p @ j` and the endpoint branch `j=0 ↦ a0` overlap on exactly
    // `(j=0)`, and restricting the tube along that clause substitutes `j := i0`,
    // giving `p @ i0` — definitionally equal to `a0` by the `PathP` boundary
    // equation (`crate::check::Checker::path_boundary`), for *any* `p : Path A a0
    // a1`, opaque axiom included. Symmetrically for `j=1 ↦ a1`. So the enlarged
    // system built by the (still not wired-in) `PathP`-case `hcomp` rule now passes
    // `check_sys` — confirming the diagnosed blocker is fixed, even though the
    // reduction rule itself remains a separate, not-yet-taken step (`hcomp` at
    // `PathP` still doesn't *reduce* through this shape; only the `Sys` it would
    // produce is now accepted as well-typed).
    #[test]
    fn hcomp_pathp_rule_enlarged_system_now_passes_restriction_aware_check_sys() {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a0", 0, cn("A")).unwrap();
        k.add_axiom("a1", 0, cn("A")).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a0"), cn("a1"))).unwrap();

        // u = <i> [top -> p], u0 = p  (constant line, always well-typed hcomp)
        let u = cn("p").lift(1, 0);
        let u = Term::sys(vec![(Cof::top(), u)]);
        let t = Term::hcomp(Term::path(cn("A"), cn("a0"), cn("a1")), Cof::top(), u, cn("p"));
        // sanity: original hcomp is well-typed
        k.infer(&t).unwrap();

        // Build the enlarged CCHM assembled reduction candidate:
        // PLam( HComp( A (constant fam), phi' , [top -> p@j, j=0 -> a0, j=1 -> a1], p@j-at-cap ) )
        let fam = cn("A").lift(1, 0); // constant family, frame [j, Γ]
        let new_phi = Cof::or(Cof::or(Cof::top(), Cof::eq0(Term::Var(0))), Cof::eq1(Term::Var(0)));
        // tube branch: p lifted into frame [i', j, Γ], applied @ j (Var(1))
        let p_lifted = cn("p").lift(1, 0).lift(1, 1); // into [i', j, Γ]
        let tube = Term::papp(p_lifted, Term::Var(1));
        let e0 = cn("a0").lift(2, 0);
        let e1 = cn("a1").lift(2, 0);
        let new_u = Term::sys(vec![
            (Cof::top(), tube),
            (Cof::eq0(Term::Var(1)), e0),
            (Cof::eq1(Term::Var(1)), e1),
        ]);
        let new_u0 = Term::papp(cn("p").lift(1, 0), Term::Var(0));
        let body = Term::hcomp(fam, new_phi, new_u, new_u0);
        let candidate = Term::plam(body);

        // The restriction-aware `check_sys` now accepts this: the tube branch
        // overlaps the `j=0`/`j=1` branches only on those literal clauses, and
        // restricting the tube there yields `p @ i0 ≡ a0` / `p @ i1 ≡ a1` via the
        // `PathP` boundary equation — no unconditional (symbolic-`j`) equality is
        // ever demanded.
        let result = k.infer(&candidate);
        assert!(
            result.is_ok(),
            "expected the restriction-aware check_sys to accept the enlarged PathP-hcomp \
             system (tube and endpoint branches agree after restricting to their overlap); \
             got Err({result:?})"
        );
    }

    // ---- hcomp: the `PathP`-case filling rule (Phase 3.9, now WIRED IN) ----

    /// `A : Type 0`, `a0 a1 : A`, `p : Path A a0 a1` — the minimal setup for
    /// exercising `hcomp` at a `PathP` type through a genuine (opaque) path.
    fn pathp_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("a0", 0, cn("A")).unwrap();
        k.add_axiom("a1", 0, cn("A")).unwrap();
        k.add_axiom("p", 0, Term::path(cn("A"), cn("a0"), cn("a1"))).unwrap();
        k
    }

    /// Build `hcomp (Path A a0 a1) ⊥ (⟨i⟩ [⊤ ↦ p]) p` — a `Sys`-built, always-`⊤`
    /// tube around the constant line `p`, with `φ = ⊥` on the *outer* guard so the
    /// trivial rule does not fire first (isolating the `PathP` rule specifically,
    /// mirroring `hcomp_pi_rule_transports_a_concrete_partial_function`'s setup).
    fn concrete_pathp_hcomp() -> (Kernel, Term) {
        let k = pathp_env();
        let u = Term::sys(vec![(Cof::top(), cn("p").lift(1, 0))]);
        let t = Term::hcomp(Term::path(cn("A"), cn("a0"), cn("a1")), Cof::bot(), u, cn("p"));
        (k, t)
    }

    /// **The `PathP` rule fires**, producing a literal `PLam`, which independently
    /// re-typechecks (subject reduction, checked from scratch) at the *original*
    /// `PathP A a0 a1` type — and, critically, its `j=i0`/`j=i1` boundaries
    /// (re-derived via `PApp` at literal `IZero`/`IOne`, not merely assumed from the
    /// construction) are definitionally equal to `a0`/`a1` respectively: this is the
    /// task's required **type-preservation** proof, executed as a test rather than
    /// merely argued in the doc comment above.
    #[test]
    fn hcomp_pathp_rule_reduces_and_reinfers_the_pathp_type() {
        let (k, t) = concrete_pathp_hcomp();
        let expected_ty = Term::path(cn("A"), cn("a0"), cn("a1"));
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &expected_ty));

        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        assert!(matches!(whnf, Term::PLam(..)), "expected the PathP rule to fire, got {}", whnf.pretty());

        // Subject reduction: re-infer the reduced normal form from scratch.
        let reinferred = k.infer(&whnf).unwrap();
        assert!(k.def_eq(&reinferred, &expected_ty));

        // Re-derive the boundary independently: `whnf @ i0 ≡ a0`, `whnf @ i1 ≡ a1`
        // (the PathP checking rule for PLam already enforces this when re-inferring
        // `whnf` above, but re-deriving it explicitly via PApp is the direct,
        // "boundary=a,b" check the task asks for).
        let at_i0 = Term::papp(whnf.clone(), Term::IZero);
        let at_i1 = Term::papp(whnf.clone(), Term::IOne);
        assert!(k.def_eq(&at_i0, &cn("a0")), "expected the j=i0 boundary to be a0");
        assert!(k.def_eq(&at_i1, &cn("a1")), "expected the j=i1 boundary to be a1");
    }

    /// Differential check (this crate's standing convention): the trusted reducer
    /// and NbE agree on the `PathP`-rule reduction.
    #[test]
    fn hcomp_pathp_rule_agrees_between_reducer_and_nbe() {
        // Note: `reducer.is_def_eq`/`nbe.conv` are the *bare* structural engines —
        // unlike `Kernel::def_eq` (used by the type-preservation test above), they
        // deliberately do NOT include the checker-level `path_boundary` special case
        // (see `crate::check::Checker::path_boundary`'s doc — that rule lives only in
        // the checker's `is_def_eq`, layered on top of these engines), so `p @ i0`
        // stays a *stuck* normal form at this bare layer rather than reducing to
        // `a0`. What this test pins down is the thing these two engines actually
        // own: that they agree with *each other* on the PathP rule's reduction.
        let (k, t) = concrete_pathp_hcomp();
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        let at_i0 = Term::papp(t.clone(), Term::IZero);
        let at_i1 = Term::papp(t.clone(), Term::IOne);
        let whnf_i0 = reducer.whnf(&at_i0);
        let whnf_i1 = reducer.whnf(&at_i1);
        assert!(nbe.conv(&at_i0, &whnf_i0));
        assert!(nbe.conv(&at_i1, &whnf_i1));
        // The checker-level engine, which *does* know `path_boundary`, confirms the
        // same boundary facts the type-preservation test above already established.
        assert!(k.def_eq(&at_i0, &cn("a0")));
        assert!(k.def_eq(&at_i1, &cn("a1")));
    }

    /// **Agreement with the trivial `⊤` rule**: when `φ` genuinely is `⊤` (so the
    /// trivial rule fires, not the `PathP` rule — priority order, see the module
    /// doc), the value produced is still the *same* (up to conversion, applied at
    /// each boundary) as what the `PathP` rule *would* have built had it fired
    /// instead — mirrors `hcomp_pi_rule_agrees_with_the_trivial_rule_when_phi_is_top`.
    #[test]
    fn hcomp_pathp_rule_agrees_with_the_trivial_rule_when_phi_is_top() {
        let k = pathp_env();
        let u = Term::sys(vec![(Cof::top(), cn("p").lift(1, 0))]);
        let t = Term::hcomp(Term::path(cn("A"), cn("a0"), cn("a1")), Cof::top(), u.clone(), cn("p"));
        let reducer = crate::reduce::Reducer::new(k.env());

        let trivial_at_i0 = reducer.whnf(&Term::papp(t.clone(), Term::IZero));
        let trivial_at_i1 = reducer.whnf(&Term::papp(t.clone(), Term::IOne));

        let Term::PathP(fam, a0, a1) = Term::path(cn("A"), cn("a0"), cn("a1")) else { unreachable!() };
        let pathp_built = super::hcomp_pathp_rule(&fam, &a0, &a1, &Cof::top(), &u, &cn("p")).unwrap();
        let pathp_at_i0 = reducer.whnf(&Term::papp(pathp_built.clone(), Term::IZero));
        let pathp_at_i1 = reducer.whnf(&Term::papp(pathp_built, Term::IOne));

        assert!(reducer.is_def_eq(&trivial_at_i0, &pathp_at_i0));
        assert!(reducer.is_def_eq(&trivial_at_i1, &pathp_at_i1));
    }

    /// Sanity: an `hcomp`-at-`PathP`-built definition using the new rule survives
    /// the independent recheck harness.
    #[test]
    fn hcomp_pathp_rule_definitions_survive_independent_recheck() {
        let (mut k, t) = concrete_pathp_hcomp();
        let ty = Term::path(cn("A"), cn("a0"), cn("a1"));
        k.add_definition("hp", 0, ty, t).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 1);
    }

    /// **Adversarial (anti-`False`, PathP-case)**: `hcomp`'s `PathP` rule cannot
    /// conjure a path between two *unrelated* axioms `c0`/`c1` that have no
    /// connecting path — pushing `@j` through the system's branches only ever
    /// reuses already-`PathP`-typed branch terms, and the enlarged system's
    /// endpoint branches are exactly the *claimed* type's own `a0`/`a1`, which the
    /// checker independently verifies against; there's no way to land at a path
    /// between unconnected axioms without one already being supplied.
    #[test]
    fn hcomp_pathp_rule_cannot_conjure_a_path_between_unrelated_axioms() {
        let mut k = pathp_env();
        k.add_axiom("c0", 0, cn("A")).unwrap();
        k.add_axiom("c1", 0, cn("A")).unwrap();
        // u's branch is `p : Path A a0 a1`, not `: Path A c0 c1` — mismatched
        // against the claimed hcomp type `Path A c0 c1`.
        let u = Term::sys(vec![(Cof::top(), cn("p").lift(1, 0))]);
        let t = Term::hcomp(Term::path(cn("A"), cn("c0"), cn("c1")), Cof::bot(), u, cn("p"));
        assert!(k.infer(&t).is_err());
    }

    /// **Adversarial (anti-`False`)**: no closed inhabitant of `Path B c0 c1` for
    /// two *distinct*, path-free axioms `c0`/`c1` (a concrete "distinct closed
    /// canonical values" instance of the module doc's anti-`False` guarantee) can be
    /// produced by routing an unrelated, opaque `PathP`-typed axiom `p : Path A a0
    /// a1` through the new `hcomp` rule — the rule only ever reshapes an
    /// *already*-`Path B c0 c1`-typed term (of which there is none to reuse here,
    /// `p` being at the wrong type entirely), never manufactures a boundary the
    /// source didn't already have.
    #[test]
    fn no_closed_path_between_unrelated_values_via_hcomp_pathp_rule() {
        let mut k = pathp_env();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("c0", 0, cn("B")).unwrap();
        k.add_axiom("c1", 0, cn("B")).unwrap();
        assert!(!k.def_eq(&cn("c0"), &cn("c1")));
        let u = Term::sys(vec![(Cof::top(), cn("p").lift(1, 0))]);
        // Claim the hcomp lands at `Path B c0 c1` while the system's own branch is
        // `p : Path A a0 a1` — a genuine type mismatch, rejected by the unmodified
        // `check(t_k, ty)` obligation inside `check_sys`.
        let t = Term::hcomp(Term::path(cn("B"), cn("c0"), cn("c1")), Cof::bot(), u, cn("p"));
        assert!(k.infer(&t).is_err());
    }

    /// **Adversarial**: `hcomp`'s cap-agreement check still gates the `PathP` rule's
    /// own input — a `Sys`-built line whose cap doesn't match `u0` is rejected
    /// before the `PathP` rule ever gets a chance to fire.
    #[test]
    fn hcomp_pathp_rule_input_still_requires_cap_agreement() {
        let mut k = pathp_env();
        k.add_axiom("q", 0, Term::path(cn("A"), cn("a0"), cn("a1"))).unwrap();
        let u = Term::sys(vec![(Cof::top(), cn("q").lift(1, 0))]); // line is q
        let t = Term::hcomp(Term::path(cn("A"), cn("a0"), cn("a1")), Cof::bot(), u, cn("p")); // cap claims p
        assert!(k.infer(&t).is_err());
    }

    /// **`hcomp_pathp_rule` itself returns `None` for a non-`Sys` line** — mirrors
    /// `hcomp_pi_rule_returns_none_for_a_non_sys_line`'s discipline: checked at the
    /// pure-function level, since a well-typed `hcomp`-at-`PathP` whose line `u` is
    /// not a literal `Sys` has an inferred type of `Partial φ ty` with no
    /// elimination back to plain `ty` here (see the module doc).
    #[test]
    fn hcomp_pathp_rule_returns_none_for_a_non_sys_line() {
        let fam = cn("A").lift(1, 0);
        let a0 = cn("a0");
        let a1 = cn("a1");
        let u = cn("p").lift(1, 0); // constant line ⟨i⟩ p, not a literal Sys
        assert!(super::hcomp_pathp_rule(&fam, &a0, &a1, &Cof::bot(), &u, &cn("p")).is_none());
    }

    // ---- transp: the parametrized-inductive filling rule (Phase 3.10, see the
    // module doc's "Phase 3.10" section above) ----

    use crate::env::{Constructor, Decl, Inductive};
    use std::rc::Rc;

    /// Declare a minimal `List A` inductive by hand (mirrors `inductive.rs`'s own
    /// `declare_nat`/`declare_eq` hand-builds): `List : Type 0 → Type 0`,
    /// `List.nil : Π A, List A`, `List.cons : Π A, A → List A → List A`. No
    /// recursor is declared — this phase's rule only pattern-matches on
    /// constructor *shape* (via `Decl::Inductive`/`Decl::Constructor`), never
    /// ι-reduces, so `Inductive::recursor` is a dangling placeholder name that is
    /// never looked up.
    fn declare_list(env: &mut crate::env::Env) {
        let list = || Term::cnst(name("List"), vec![]);
        let inductive = Inductive {
            num_levels: 0,
            ty: Term::arrow(Term::typ(0), Term::typ(0)),
            num_params: 1,
            num_indices: 0,
            ctors: vec![name("List.nil"), name("List.cons")],
            recursor: name("List.rec"),
            group: vec![name("List")],
        };
        // List.nil : Π (A : Type 0), List A
        let nil_ty = Term::pi(Term::typ(0), Term::app(list(), Term::Var(0)));
        let ctor_nil =
            Constructor { num_levels: 0, ty: nil_ty, ind: name("List"), index: 0, num_fields: 0 };
        // List.cons : Π (A : Type 0) (x : A) (xs : List A), List A
        let cons_ty = Term::pi(
            Term::typ(0),
            Term::pi(
                Term::Var(0),                        // x : A
                Term::pi(
                    Term::app(list(), Term::Var(1)), // xs : List A
                    Term::app(list(), Term::Var(2)), // List A
                ),
            ),
        );
        let ctor_cons =
            Constructor { num_levels: 0, ty: cons_ty, ind: name("List"), index: 1, num_fields: 2 };
        env.insert(name("List"), Decl::Inductive(Rc::new(inductive))).unwrap();
        env.insert(name("List.nil"), Decl::Constructor(Rc::new(ctor_nil))).unwrap();
        env.insert(name("List.cons"), Decl::Constructor(Rc::new(ctor_cons))).unwrap();
    }

    fn list_nil(a: Term) -> Term {
        Term::app(cn("List.nil"), a)
    }
    fn list_cons(a: Term, x: Term, xs: Term) -> Term {
        Term::apps(cn("List.cons"), [a, x, xs])
    }
    fn list_of(a: Term) -> Term {
        Term::app(cn("List"), a)
    }

    /// `A B : Type 0`, `p : Path Type A B`, `a1 a2 : A`, plus `List` declared.
    fn list_env() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom("A", 0, Term::typ(0)).unwrap();
        k.add_axiom("B", 0, Term::typ(0)).unwrap();
        k.add_axiom("p", 0, Term::path(Term::typ(0), cn("A"), cn("B"))).unwrap();
        k.add_axiom("a1", 0, cn("A")).unwrap();
        k.add_axiom("a2", 0, cn("A")).unwrap();
        declare_list(k.env_mut());
        k
    }

    /// `λi. List (p @ i)` — the family transporting a `List A` to a `List B`.
    fn list_family() -> Term {
        Term::app(cn("List"), Term::papp(cn("p").lift(1, 0), Term::Var(0)))
    }

    /// **The rule fires** on a two-element concrete list, producing a literal
    /// `List.cons` application (not a stuck `Transp`), which independently
    /// re-typechecks (subject reduction, checked from scratch) at the *target*
    /// type `List B`.
    #[test]
    fn transp_list_rule_transports_a_concrete_list() {
        let k = list_env();
        let xs = list_cons(cn("A"), cn("a1"), list_cons(cn("A"), cn("a2"), list_nil(cn("A"))));
        let t = Term::transp(list_family(), Cof::top(), xs);

        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &list_of(cn("B"))));

        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        // Genuinely fires: head is List.cons, not a stuck Transp.
        let (head, args) = whnf.unfold_apps();
        assert_eq!(head, cn("List.cons"), "expected the rule to fire, got {}", whnf.pretty());
        assert!(k.def_eq(&args[0], &cn("B")), "the new parameter must be B");

        // Subject reduction: the reduced normal form independently re-typechecks
        // at List B, from scratch.
        let reinferred = k.infer(&whnf).unwrap();
        assert!(k.def_eq(&reinferred, &list_of(cn("B"))));
    }

    /// **Type preservation, walked all the way down**: fully reduce (whnf at each
    /// layer) the transported two-element list and confirm every element is
    /// individually `B`-typed (via `transport p`, which stays stuck since `p` is
    /// an opaque axiom — no further reduction rule applies to it — but is still,
    /// independently, a well-typed `B`-classified term), and the tail bottoms out
    /// at a literal `List.nil B`.
    #[test]
    fn transp_list_rule_type_preservation_from_scratch() {
        let k = list_env();
        let xs = list_cons(cn("A"), cn("a1"), list_cons(cn("A"), cn("a2"), list_nil(cn("A"))));
        let t = Term::transp(list_family(), Cof::top(), xs);
        let reducer = crate::reduce::Reducer::new(k.env());

        // Layer 1: cons B (transp p a1) (transp fam (cons A a2 (nil A)))
        let l1 = reducer.whnf(&t);
        let (h1, args1) = l1.unfold_apps();
        assert_eq!(h1, cn("List.cons"));
        assert_eq!(args1.len(), 3);
        assert!(k.def_eq(&args1[0], &cn("B")));
        assert!(k.check(&args1[1], &cn("B")).is_ok(), "head element must check at B");

        // Layer 2: whnf the tail — another cons, since the tail field is the
        // Recursive case (transp fam (cons A a2 (nil A))).
        let l2 = reducer.whnf(&args1[2]);
        let (h2, args2) = l2.unfold_apps();
        assert_eq!(h2, cn("List.cons"));
        assert_eq!(args2.len(), 3);
        assert!(k.def_eq(&args2[0], &cn("B")));
        assert!(k.check(&args2[1], &cn("B")).is_ok(), "second element must check at B");

        // Layer 3: whnf the final tail — bottoms out at List.nil B (no fields to
        // transport, so the constructor rebuild is immediate).
        let l3 = reducer.whnf(&args2[2]);
        assert!(k.def_eq(&l3, &list_nil(cn("B"))), "expected List.nil B, got {}", l3.pretty());
    }

    /// **Regularity agreement**: transporting a list along a *constant* parameter
    /// family (no varying parameter at all — the top-level regularity rule fires
    /// first, unconditionally, exactly as every other rule in this file defers to
    /// it) is still the identity, and this new rule never even runs (there is no
    /// varying parameter for it to find).
    #[test]
    fn transp_list_rule_agrees_with_regularity_on_a_constant_parameter() {
        let k = list_env();
        let xs = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        let fam = list_of(cn("A")).lift(1, 0); // ⟨i⟩ List A, doesn't mention i
        let t = Term::transp(fam, Cof::top(), xs.clone());
        assert!(k.def_eq(&t, &xs));
        let reducer = crate::reduce::Reducer::new(k.env());
        assert!(matches!(reducer.whnf(&t).unfold_apps().0, Term::Const(ref n, _) if n.as_ref() == "List.cons"));
    }

    /// Differential check (this crate's standing convention): the trusted reducer
    /// and NbE agree on the list rule's reduction, down to the individual
    /// (still-stuck-on-the-opaque-`p`) transported elements.
    #[test]
    fn transp_list_rule_agrees_between_reducer_and_nbe() {
        let k = list_env();
        let xs = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        let t = Term::transp(list_family(), Cof::top(), xs);
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        let whnf = reducer.whnf(&t);
        assert!(nbe.conv(&t, &whnf));
    }

    /// Sanity: a definition built by transporting a concrete list survives the
    /// independent recheck harness.
    #[test]
    fn transp_list_rule_definitions_survive_independent_recheck() {
        let mut k = list_env();
        let xs = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        let t = Term::transp(list_family(), Cof::top(), xs);
        k.add_definition("transported_xs", 0, list_of(cn("B")), t).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 1);
    }

    /// **Adversarial (anti-`False`, inductive case)**: the transported list's
    /// elements must *not* be usable at the *source* type `A` — only at the
    /// genuinely path-connected target `B` — i.e. the rule doesn't erase the
    /// element-type change. Mirrors
    /// `transp_pi_rule_transported_function_rejects_the_source_domain`.
    #[test]
    fn transp_list_rule_transported_list_rejects_the_source_element_type() {
        let k = list_env();
        let xs = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        let t = Term::transp(list_family(), Cof::top(), xs);
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        let (_h, args) = whnf.unfold_apps();
        // The transported head element (`args[1]`) is `B`-typed, not `A`-typed.
        assert!(k.check(&args[1], &cn("B")).is_ok());
        assert!(k.check(&args[1], &cn("A")).is_err());
    }

    /// **Adversarial (anti-`False`, inductive case)**: without an actual path
    /// axiom connecting the element types, the rule cannot be used to move a list
    /// to an *unrelated* element type — `Checker::infer`'s pre-existing
    /// `check(a, family[i:=i0])` obligation (completely unmodified by this phase)
    /// is the one thing guarding this.
    #[test]
    fn transp_list_rule_cannot_smuggle_a_list_to_an_unrelated_type() {
        let mut k = list_env();
        k.add_axiom("C", 0, Term::typ(0)).unwrap();
        let xs = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        // Constant family (no path at all): claims `List A` transports along
        // `List C`, which is simply false — `xs : List A`, not `List C`.
        let fam = list_of(cn("C")).lift(1, 0);
        let t = Term::transp(fam, Cof::top(), xs);
        assert!(k.infer(&t).is_err());
    }

    /// **`transp_inductive_rule` itself returns `None`** when the argument is not
    /// a syntactically literal constructor application (here, a free neutral
    /// variable of `List A` type) — mirrors `hcomp_pi_rule_returns_none_for_a_non_sys_line`'s
    /// discipline: the rule declines rather than guesses, leaving the `transp`
    /// stuck (valid, inert data).
    #[test]
    fn transp_list_rule_returns_none_for_a_non_constructor_argument() {
        let mut k = list_env();
        k.add_axiom("xs_opaque", 0, list_of(cn("A"))).unwrap();
        let fam = list_family();
        assert!(super::transp_inductive_rule(k.env(), &fam, &cn("xs_opaque")).is_none());
        // And the full `transp` genuinely stays stuck through the reducer too.
        let t = Term::transp(fam, Cof::top(), cn("xs_opaque"));
        let reducer = crate::reduce::Reducer::new(k.env());
        assert!(matches!(reducer.whnf(&t), Term::Transp(..)));
    }

    /// **`transp_inductive_rule` declines when more than one parameter varies**
    /// (out of scope for this pass — see the module doc). Built directly at the
    /// function level with a two-parameter inductive stand-in (`List`'s own
    /// single-parameter shape can't exercise this, so this test fabricates a
    /// family whose *two* arguments both mention the interval variable against
    /// `List`'s single-parameter signature is a bad fit — instead, confirm the
    /// guard by checking a family with a mismatched argument count is declined
    /// too, the simpler structural precondition failure).
    #[test]
    fn transp_list_rule_returns_none_for_wrong_parameter_count() {
        let k = list_env();
        // `List` takes exactly one parameter; apply it (nonsensically) to two.
        let fam = Term::apps(
            cn("List"),
            [Term::papp(cn("p").lift(2, 0), Term::Var(1)), Term::Var(0)],
        );
        let xs = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        assert!(super::transp_inductive_rule(k.env(), &fam, &xs).is_none());
    }

    /// **Adversarial**: two structurally-distinct transported lists (different
    /// source elements) are not conflated — the built `List.cons` applications
    /// stay distinguishable.
    #[test]
    fn transp_list_rule_does_not_conflate_distinct_lists() {
        let k = list_env();
        assert!(!k.def_eq(&cn("a1"), &cn("a2")));
        let xs1 = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        let xs2 = list_cons(cn("A"), cn("a2"), list_nil(cn("A")));
        let t1 = Term::transp(list_family(), Cof::top(), xs1);
        let t2 = Term::transp(list_family(), Cof::top(), xs2);
        assert!(!k.def_eq(&t1, &t2));
    }

    // ---- hcomp: the constructor-compatible inductive filling rule (Phase 3.11,
    // see the module doc's "Phase 3.11" section above) ----

    /// A single-branch, constant `Sys` (mirrors
    /// `hcomp_pi_rule_transports_a_concrete_partial_function`'s own setup) whose
    /// one branch is a concrete two-element `List A`, with `φ = ⊥` so the trivial
    /// `φ=⊤` rule does *not* fire first — isolating the inductive rule
    /// specifically (see the module doc's "Agreement" point: the rules are
    /// mutually exclusive by construction, trivial always tried first).
    fn list_hcomp_term() -> Term {
        let xs = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        let u = Term::sys(vec![(Cof::top(), xs.clone().lift(1, 0))]);
        Term::hcomp(list_of(cn("A")), Cof::bot(), u, xs)
    }

    /// **The rule fires** on a concrete same-constructor system, producing a
    /// literal `List.cons` application (not a stuck `HComp`), which
    /// independently re-typechecks (subject reduction, checked from scratch) at
    /// `List A`. Its head/tail fields are themselves (still-stuck, since φ=⊥ —
    /// deliberately, to isolate this rule from the trivial `φ=⊤` rule, mirroring
    /// `hcomp_pi_rule_transports_a_concrete_partial_function`'s own choice) `hcomp`
    /// terms, each independently well-typed at the field's own target type — the
    /// head at `A` (the `Generic` field kind), the tail at `List A` (the
    /// `Recursive` field kind, correctly recursing in `D` itself rather than in
    /// some unrelated type).
    #[test]
    fn hcomp_list_rule_reduces_and_reinfers_the_list_type() {
        let k = list_env();
        let t = list_hcomp_term();
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &list_of(cn("A"))));

        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        let (head, args) = whnf.unfold_apps();
        assert_eq!(head, cn("List.cons"), "expected the rule to fire, got {}", whnf.pretty());
        assert_eq!(args.len(), 3);
        assert!(k.def_eq(&args[0], &cn("A")));

        // Subject reduction: the reduced normal form independently re-typechecks
        // at `List A`, from scratch.
        let reinferred = k.infer(&whnf).unwrap();
        assert!(k.def_eq(&reinferred, &list_of(cn("A"))));

        // The head field (`Generic` kind) is well-typed at `A`, and — since φ=⊥
        // is never decided true — stays a genuinely stuck `hcomp A ⊥ […] a1`
        // rather than being eagerly further-reduced.
        assert!(k.check(&args[1], &cn("A")).is_ok(), "head field must check at A");
        assert!(matches!(reducer.whnf(&args[1]), Term::HComp(..)));

        // The tail field (`Recursive` kind) is well-typed at `List A` — recursing
        // in `D` itself, not e.g. `A` or some other unrelated type — and, since
        // `List.nil` has zero fields, *this* rule immediately bottoms out at a
        // literal `List.nil A` (no sub-`hcomp` left to build, regardless of φ),
        // one constructor layer deeper than the outer `hcomp`.
        assert!(k.check(&args[2], &list_of(cn("A"))).is_ok(), "tail field must check at List A");
        assert!(k.def_eq(&args[2], &list_nil(cn("A"))), "tail field must reduce to List.nil A");
    }

    /// Differential check (this crate's standing convention): the trusted
    /// reducer and NbE agree on the inductive rule's reduction.
    #[test]
    fn hcomp_list_rule_agrees_between_reducer_and_nbe() {
        let k = list_env();
        let t = list_hcomp_term();
        let reducer = crate::reduce::Reducer::new(k.env());
        let nbe = crate::nbe::Nbe::new(k.env());
        let whnf = reducer.whnf(&t);
        assert!(nbe.conv(&t, &whnf));
    }

    /// **Agreement with the trivial `⊤` rule**: when `φ` genuinely is `⊤` (so the
    /// trivial rule fires first, not the inductive rule — priority order, see the
    /// module doc), calling [`hcomp_inductive_rule`] directly (bypassing the
    /// reducer's priority order) still produces a value convertible to the
    /// trivial rule's own answer.
    #[test]
    fn hcomp_list_rule_agrees_with_the_trivial_rule_when_phi_is_top() {
        let k = list_env();
        let xs = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        let u = Term::sys(vec![(Cof::top(), xs.clone().lift(1, 0))]);
        let trivial_answer = u.instantiate(&Term::IOne); // the trivial rule's own value
        assert!(k.def_eq(&trivial_answer, &xs));

        let ctor_built =
            super::hcomp_inductive_rule(k.env(), &list_of(cn("A")), &Cof::top(), &u, &xs).unwrap();
        assert!(k.def_eq(&ctor_built, &trivial_answer));
    }

    /// Sanity: an `hcomp`-built (inductive-rule-reduced) definition survives the
    /// independent recheck harness.
    #[test]
    fn hcomp_list_rule_definitions_survive_independent_recheck() {
        let mut k = list_env();
        let t = list_hcomp_term();
        k.add_definition("composed_list", 0, list_of(cn("A")), t).unwrap();
        assert_eq!(crate::kernel::recheck_all_definitions(k.env()).unwrap(), 1);
    }

    /// **`hcomp_inductive_rule` declines on a mixed-constructor system**: one
    /// branch is `List.cons …`, the other `List.nil A` — the "heterogeneous"
    /// case this pass explicitly defers (see the module doc). The rule returns
    /// `None` (rather than guessing), and the full `hcomp` genuinely stays stuck
    /// through the reducer too.
    #[test]
    fn hcomp_list_rule_declines_on_mixed_constructor_branches() {
        let k = list_env();
        let cap = list_nil(cn("A"));
        let u = Term::sys(vec![
            (Cof::eq0(Term::Var(0)), list_cons(cn("A"), cn("a1"), list_nil(cn("A")))),
            (Cof::eq1(Term::Var(0)), list_nil(cn("A")).lift(1, 0)),
        ]);
        assert!(super::hcomp_inductive_rule(k.env(), &list_of(cn("A")), &Cof::bot(), &u, &cap)
            .is_none());
        let t = Term::hcomp(list_of(cn("A")), Cof::bot(), u, cap);
        let reducer = crate::reduce::Reducer::new(k.env());
        assert!(matches!(reducer.whnf(&t), Term::HComp(..)), "expected a stuck HComp");
    }

    /// **`hcomp_inductive_rule` declines when a branch is not (syntactically) a
    /// constructor application at all** — an opaque neutral of `List A` type
    /// (mirrors `hcomp_pi_rule_returns_none_for_a_non_sys_line`'s "stay stuck
    /// rather than guess" discipline).
    #[test]
    fn hcomp_list_rule_declines_when_a_branch_is_not_a_constructor_application() {
        let mut k = list_env();
        k.add_axiom("xs_opaque", 0, list_of(cn("A"))).unwrap();
        let cap = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        let u = Term::sys(vec![(Cof::top(), cn("xs_opaque").lift(1, 0))]);
        assert!(super::hcomp_inductive_rule(k.env(), &list_of(cn("A")), &Cof::bot(), &u, &cap)
            .is_none());
    }

    /// **`hcomp_inductive_rule` declines on an empty system** (`u = Sys([])`) —
    /// there is no constructor for the branches to agree on, so building anything
    /// would silently discard the rule's own defining premise (see the module
    /// doc's scope section).
    #[test]
    fn hcomp_list_rule_declines_on_an_empty_system() {
        let k = list_env();
        let cap = list_nil(cn("A"));
        let u = Term::sys(vec![]);
        assert!(super::hcomp_inductive_rule(k.env(), &list_of(cn("A")), &Cof::bot(), &u, &cap)
            .is_none());
    }

    /// **Adversarial (anti-`False`)**: [`hcomp_inductive_rule`] declines outright
    /// (a purely structural guard failure, not even reaching field composition)
    /// when the composition type isn't a user inductive at all — it cannot be
    /// used to conjure an inhabitant of an unrelated axiom type.
    #[test]
    fn hcomp_list_rule_cannot_conjure_an_inhabitant_of_an_unrelated_axiom() {
        let mut k = list_env();
        k.add_axiom("E", 0, Term::typ(0)).unwrap();
        let u = Term::sys(vec![(Cof::top(), cn("a1").lift(1, 0))]);
        assert!(super::hcomp_inductive_rule(k.env(), &cn("E"), &Cof::bot(), &u, &cn("a1")).is_none());
    }

    /// **Adversarial**: two structurally-distinct `hcomp`-composed lists
    /// (different source elements) are not conflated — the built `List.cons`
    /// applications stay distinguishable.
    #[test]
    fn hcomp_list_rule_does_not_conflate_distinct_lists() {
        let k = list_env();
        assert!(!k.def_eq(&cn("a1"), &cn("a2")));
        let xs1 = list_cons(cn("A"), cn("a1"), list_nil(cn("A")));
        let xs2 = list_cons(cn("A"), cn("a2"), list_nil(cn("A")));
        let u1 = Term::sys(vec![(Cof::top(), xs1.clone().lift(1, 0))]);
        let u2 = Term::sys(vec![(Cof::top(), xs2.clone().lift(1, 0))]);
        let t1 = Term::hcomp(list_of(cn("A")), Cof::bot(), u1, xs1);
        let t2 = Term::hcomp(list_of(cn("A")), Cof::bot(), u2, xs2);
        assert!(!k.def_eq(&t1, &t2));
    }

    // ---- Phase 3.12: `transp` through a `Glue`/`ua` line — declined, so these
    // pin down "stays honestly stuck", not a computed answer (see this module's
    // "Phase 3.12" doc for the full obstruction argument). ----

    fn ua_env() -> crate::env::Env {
        let mut env = crate::env::Env::new();
        crate::inductive::declare_nat(&mut env).unwrap();
        crate::equiv::declare_equiv(&mut env).unwrap();
        env
    }

    fn nat_t() -> Term {
        Term::cnst(name("Nat"), vec![])
    }

    /// `transport (ua Nat Nat (idEquiv Nat)) zero` — the cleanest possible case
    /// (identity equivalence, so *if* this reduced, the "obvious" answer would
    /// just be `zero` again) — stays a stuck `Term::Transp`, under both the
    /// reducer and NbE, exactly as before this pass: no Glue-transport rule was
    /// wired in, so nothing here should have started firing.
    #[test]
    fn transp_through_ua_line_stays_stuck() {
        let env = ua_env();
        let lvl = crate::level::Level::of_nat(1);
        let n = nat_t();
        let e = Term::app(Term::cnst(name("idEquiv"), vec![lvl.clone()]), n.clone());
        let p = crate::glue::ua(lvl, n.clone(), n.clone(), e);
        let zero = Term::cnst(name("Nat.zero"), vec![]);
        let transported = crate::cubical::transport(&p, &zero);

        let r = crate::reduce::Reducer::new(&env);
        assert!(
            matches!(r.whnf(&transported), Term::Transp(..)),
            "no Glue-transport rule is wired in: whnf must leave a stuck Transp"
        );
        let nbe = crate::nbe::Nbe::new(&env);
        assert!(
            matches!(nbe.normalize(&transported), Term::Transp(..)),
            "NbE must agree: still stuck, not silently computed to `zero` (or anything else)"
        );
    }

    /// **Anti-`False`**: with `A ≠ B` (`A = Nat`, `B = Nat → Nat`) the stuck
    /// `transport (ua A B e) a0` must not be usable to manufacture any equation
    /// between distinct closed `Nat`s — confirming the *absence* of a
    /// Glue-transport rule is exactly as safe as a correct one would need to be
    /// (a stuck neutral proves nothing).
    #[test]
    fn transp_through_ua_line_cannot_smuggle_a_false_equation() {
        let env = ua_env();
        let lvl = crate::level::Level::of_nat(1);
        let n = nat_t();
        let arrow = Term::arrow(n.clone(), n.clone());
        // A bogus `e : Equiv Nat (Nat->Nat)` is fine here — this test only probes
        // *reduction*, and `ua`'s boundary rule (see `glue.rs`) never inspects
        // `e`'s content, only whether the guarding face is decided.
        let bogus_e = Term::lam(n.clone(), Term::Var(0));
        let p = crate::glue::ua(lvl, n.clone(), arrow, bogus_e);
        let zero = Term::cnst(name("Nat.zero"), vec![]);
        let one = Term::app(Term::cnst(name("Nat.succ"), vec![]), zero.clone());
        let transported = crate::cubical::transport(&p, &zero);

        let r = crate::reduce::Reducer::new(&env);
        // Stays stuck (same shape as above)...
        assert!(matches!(r.whnf(&transported), Term::Transp(..)));
        // ...and in particular is never compared/reduced down to `one`, nor does
        // its mere presence perturb the unrelated fact that `zero ≠ one`.
        assert!(!r.is_def_eq(&zero, &one));
        assert!(!r.is_def_eq(&transported, &one));
    }

    // ---- Phase 3.13: re-confirm the above with `Term::GlueIntro` installed ----

    /// **Non-regression**: [`transp_through_ua_line_stays_stuck`] and
    /// [`transp_through_ua_line_cannot_smuggle_a_false_equation`] re-run with
    /// `Term::GlueIntro` (the `glue` introduction form) now available in the
    /// environment and exercised alongside the `Transp` — its mere presence
    /// (declaring `Equiv`, building a `glue [(i=0)↦a0] a0`-shaped witness of
    /// `Glue`'s branch type at a *different* interval variable, then leaving
    /// the actual `transport (ua e) a0` untouched) must not perturb `transp`'s
    /// stuck-ness on the `Glue`/`ua` line: still a stuck `Term::Transp` under
    /// both the reducer and NbE, and the anti-`False` battery still holds. This
    /// pins down that Phase 3.13's diagnosis (a real `Glue`-`hcomp` rule is
    /// still missing, `GlueIntro` alone doesn't supply it) matches the kernel's
    /// actual behavior, not just its documentation.
    #[test]
    fn transp_through_ua_line_stays_stuck_even_with_glue_intro_available() {
        let env = ua_env();
        let lvl = crate::level::Level::of_nat(1);
        let n = nat_t();
        let e = Term::app(Term::cnst(name("idEquiv"), vec![lvl.clone()]), n.clone());
        let p = crate::glue::ua(lvl.clone(), n.clone(), n.clone(), e.clone());
        let zero = Term::cnst(name("Nat.zero"), vec![]);
        let one = Term::app(Term::cnst(name("Nat.succ"), vec![]), zero.clone());

        // A genuine `Term::GlueIntro` witness of `ua`'s own branch type, built
        // and independently type-checked, sitting in the same environment/
        // universe as the `transport (ua e) zero` under test — confirming
        // `GlueIntro`'s mere availability (not just its *existence* as a
        // variant) doesn't change anything about `Transp`'s behavior.
        let phi = Cof::eq0(Term::Var(0));
        let g = Term::glue_intro(vec![(phi.clone(), zero.clone().lift(1, 0))], zero.clone().lift(1, 0));
        let gty = Term::glue_ty(n.clone().lift(1, 0), phi, n.clone().lift(1, 0), e.lift(1, 0));
        let chk = crate::check::Checker::new(&env);
        let mut ctx = crate::check::LocalCtx::new();
        ctx.push(Term::I);
        chk.check(&mut ctx, &g, &gty).expect("glue intro witness should still check fine");

        let transported = crate::cubical::transport(&p, &zero);
        let r = crate::reduce::Reducer::new(&env);
        assert!(
            matches!(r.whnf(&transported), Term::Transp(..)),
            "GlueIntro's presence must not make transp(ua) start firing"
        );
        let nbe = crate::nbe::Nbe::new(&env);
        assert!(matches!(nbe.normalize(&transported), Term::Transp(..)));
        // Anti-`False`, re-run alongside GlueIntro's availability.
        assert!(!r.is_def_eq(&zero, &one));
        assert!(!r.is_def_eq(&transported, &one));
    }
}


