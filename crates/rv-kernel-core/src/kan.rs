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

use crate::face::Cof;
use crate::term::Term;

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
// [`kernel_tests::hcomp_pathp_rule_declined_naive_cchm_construction_fails_check_sys_compatibility`]
// makes this concrete and adversarially reproducible: builds exactly the assembled
// term the rule above would produce, for an ordinary axiom `p : Path A a0 a1`
// (opaque — no special structure to exploit), and confirms `Checker::infer`
// rejects it with precisely `check_sys`'s "branches disagree on their overlap"
// error. Were this rule wired into `reduce.rs`/`nbe.rs` regardless, it would
// silently break **subject reduction**: a well-typed `HComp(PathP …, φ, u, u0)`
// term (checked once, via the *original* `n`-branch system, which never needed
// this compatibility) would `whnf`-reduce to a form that the very same checker,
// run again from scratch, rejects — exactly the class of bug this crate's
// "independently re-typechecks" testing discipline exists to catch (see
// [`transp_pi_rule`]'s and [`hcomp_pi_rule`]'s own soundness arguments, point 2,
// both of which — unlike this one — *pass* that test).
//
// # What would it take to ship this — out of scope for this pass
//
// The blocker is in `check_sys`'s compatibility condition itself: making it
// *cofibration-aware* (checking `t_i ≡ t_j` only after substituting the interval
// variables an overlap pins down, i.e. genuinely "under" `φ_i ∧ φ_j` rather than
// unconditionally) is a substantive, independently soundness-critical change to
// `crate::check` — it would need its own adversarial scrutiny (does substituting
// under a *satisfiable-but-not-decided* overlap ever let two genuinely different
// closed terms be conflated? almost certainly a delicate argument) entirely
// separate from, and larger than, "add one more Kan filling rule". Bundling that
// redesign into this already soundness-critical pass is exactly the kind of
// "ship something you can't stand behind" this task explicitly warns against.
// **Declined, not shipped** — `hcomp` at a `PathP` type remains stuck, an honest,
// tested incompleteness. `J`, HIT composition, and `Glue` remain deferred as
// before (see the top-level module doc), now joined by this specific,
// precisely-diagnosed `PathP`-case gap for any future pass to pick up.

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

    /// **Refl-agreement**: transporting `f : A → A` along a `Π` family connected by
    /// `refl A` (syntactically *varying* — `mentions_var` sees the interval
    /// variable in `(refl A) @ i`, so the regularity rule does *not* fire — but
    /// *semantically* constant) still type-checks at exactly `A → A` (the same type
    /// `family[i:=i1]` reports regardless of which reduction rule fires) and the
    /// `Π`-rule genuinely fires (whnf reaches a literal `Lam`).
    ///
    /// This test does **not** additionally check that applying the result to some
    /// `c : A` is *definitionally* `f c` — it isn't, at least not automatically:
    /// [`coe`]'s reparametrized family `dom[i := (r∧~k)∨(r'∧k)]` **always**
    /// syntactically mentions the fresh connection binder `k` by construction (even
    /// when `r` and `r'` happen to be the same term), so the structural-only
    /// regularity check (deliberately *not* extended by this phase — see the module
    /// doc above) never fires *inside* a `coe`, even at a literal `r=r'` boundary.
    /// The nested `Transp`s this produces are still **sound** (a `Transp` that
    /// doesn't reduce is valid, inert data, exactly like an unresolved `Sys` — see
    /// the top-level module doc's soundness argument, point "no new equation"),
    /// just not maximally reduced — a real, but narrow and honestly-reported,
    /// incompleteness (not unsoundness) of this minimal implementation.
    #[test]
    fn transp_pi_rule_typechecks_on_a_refl_connected_pi_family() {
        let k = pi_env();
        let fam = path_pi_family(&crate::cubical::refl(&cn("A")));
        assert!(crate::term::mentions_var(&fam, 0), "sanity: family is syntactically varying");
        let t = Term::transp(fam, Cof::bot(), cn("f"));

        // Type is (as always, independent of which reduction rule fires) A → A.
        let ty = k.infer(&t).unwrap();
        assert!(k.def_eq(&ty, &Term::arrow(cn("A"), cn("A"))));

        // The `Π` rule actually fires (whnf is a literal `Lam`, not a stuck `Transp`),
        // and the reduced form independently re-typechecks at the very same type.
        let reducer = crate::reduce::Reducer::new(k.env());
        let whnf = reducer.whnf(&t);
        assert!(matches!(whnf, Term::Lam(..)), "expected the Π rule to fire, got {}", whnf.pretty());
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

    // ---- hcomp: the `PathP`-case rule — INVESTIGATED AND DECLINED (see the module
    // doc's "Phase 3.8" section for the full account). This test is the concrete,
    // reproducible adversarial evidence backing that decision: it shows the naive
    // CCHM assembled-system construction fails this kernel's own `check_sys`
    // compatibility condition for a perfectly ordinary (opaque axiom) `PathP`
    // value — i.e. the construction is not merely "not yet proven sound", it is
    // demonstrably **rejected by the existing, unmodified, trusted checker** the
    // moment you try to independently re-typecheck it, for any non-degenerate input.
    #[test]
    fn hcomp_pathp_rule_declined_naive_cchm_construction_fails_check_sys_compatibility() {
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

        // Now build the naive assembled reduction candidate:
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

        // The naive construction must be *rejected* by the existing, unmodified
        // `check_sys` — this is the whole point of the test (see the module doc's
        // "Phase 3.8" section): were this to unexpectedly succeed, the analysis
        // there would be wrong and the rule would need re-examining before ever
        // being wired into `reduce.rs`/`nbe.rs`.
        let result = k.infer(&candidate);
        assert!(
            result.is_err(),
            "expected check_sys to reject the naive PathP-hcomp construction (the tube \
             branch, applied at a *symbolic* path coordinate `j`, cannot be unconditionally \
             `is_def_eq` to the endpoint `a0`/`a1` for an opaque axiom `p` — see the module \
             doc); got Ok({result:?}) instead, meaning the prior analysis needs revisiting"
        );
        let msg = result.unwrap_err();
        assert!(
            msg.contains("disagree on their overlap"),
            "expected check_sys's compatibility-condition error specifically, got: {msg}"
        );
    }
}
