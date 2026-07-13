# The cubical layer

Raven's trusted kernel (`crates/rv-kernel-core`) carries a cubical type theory
layer alongside the ordinary dependent core: an interval, path types, Kan
operations, several higher-inductive types (HITs) built on genuine path
constructors, a bi-invertible/half-adjoint equivalence hierarchy, and `Glue`/`ua`
(univalence, *stated*). This document is a map of what exists, where it lives,
how it is surfaced to `.rv` source, and — honestly — what is not yet
computational.

Everything described here is exercised end-to-end by
`examples/proofs/cubical.rv` (the base `Path`/`I2` layer) and
`examples/proofs/cubical_showcase.rv` (the `S1c`/`S2`/`T2`/`S3`/`SetQ`/
`Equiv`/`ua` pieces), both checked by `crates/rv-driver/tests/rv_proofs.rs`.

## 1. The interval and paths (`crates/rv-kernel-core/src/cubical.rs`)

- The interval `I` — **not** a fibrant type (it can never be an ordinary
  `Π`-domain; `Checker::infer_sort` rejects `I` on purpose). Its elements are
  `i0`/`i1` (`Term::IZero`/`IOne`) and interval variables, with De Morgan
  structure: `ineg` (`Term::INeg`), `imeet`/`ijoin` (`Term::IMeet`/`IJoin`).
- `PathP` (`Term::PathP`) — the dependent path type over a family, with
  introduction `plam`/`Term::PLam` and elimination `papp`/`Term::PApp`, plus
  **η** for paths. `Path A a b` is the non-dependent special case (a constant
  family).
- Faces and systems (`crates/rv-kernel-core/src/face.rs`): cofibrations `Cof`
  (`i=0`/`i=1` and their meet/join), and `Term::Sys`/`Term::Partial` for
  partial elements agreeing on their overlaps.
- Kan operations (`crates/rv-kernel-core/src/kan.rs`): `transp`
  (`Term::Transp`) and `hcomp` (`Term::HComp`), with per-type-former filling
  rules (`Π`, `PathP`, inductives, …).
- Derived combinators, all genuinely computing (no new axioms): `refl`, `ap`,
  `funext` (dependent function extensionality, a *direct* cubical proof, not
  routed through `Quot`), `transport`/`subst` (`transport` specializes `transp`
  to a `Path` in `Sort u`), `j` (path induction — computes on `refl` by
  β-reducing the `Path`/`transp` definition of `J` used here), `trans3`, and a
  `Path ⇄ Eq` bridge (`path_to_eq`/`eq_to_path`).

## 2. Higher-inductive types

Two independent HIT presentations exist:

- **`Eq`-based (propositional) HITs** — `crates/rv-kernel-core/src/circle.rs`
  (`S¹`), `src/hit.rs` (a general schema), `src/quotient.rs` (`Quot`), and
  `src/trunc.rs` (`Trunc`, 1-truncation). Their path constructors classify by
  the *inductive* `Eq`, so they hold only propositionally — no reduction rule
  fires on the path constructor itself (e.g. `S¹.rec`'s `lp` datum is inert,
  discarded at ι-time).
- **Genuinely cubical (computing) HITs** — path constructors classified by the
  *real* `PathP`, whose recursor ι-rules actually apply the path case at the
  constructor:
  - `crates/rv-kernel-core/src/interval_hit.rs` — `I2` (`I2.zero`/`I2.one`/
    `I2.seg : Path I2 zero one`), the interval as a HIT between two distinct
    points.
  - `crates/rv-kernel-core/src/circle_cubical.rs` — `S1c` (`S1c.base`/
    `S1c.loop : Path S1c base base`), a genuine **self**-loop: `S1c.rec C b l
    S1c.base ↝ b` and `S1c.rec C b l (S1c.loop @ r) ↝ l @ r`.
  - `crates/rv-kernel-core/src/cubical_hit.rs` — `declare_cubical_hit`, a
    **general schema** with a full points → 1-paths → 2-cells → 3-cells →
    set-quotients ladder:
    - an arbitrary number of (possibly fielded, possibly self-referential)
      **point** constructors;
    - **1-path** constructors — quantified paths between any two points (the
      field-arity/positivity side conditions are checked), including
      self-loops;
    - **2-path ("surface")** constructors (`CubSurfSpec`): a square based at a
      single nullary point, each of whose four sides is either `refl` or a
      previously-declared unquantified self-loop. All-`refl` recovers the
      **"S²"** shape — one point `base`, one 2-cell `surf : Path (Path S²
      base base) (refl base) (refl base)`, with a computing `S2.rec` whose
      2-path ι-rule is `S2.rec C b t (S2.surf @ i @ j) ↝ (t @ i) @ j`.
      Setting `left = right` to one self-loop and `top = bottom` to a
      *distinct* self-loop gives the **torus `T²`**: one point `base`, two
      self-loops `loopP`/`loopQ`, and a square `surf : PathP (λi. Path T²
      (loopP@i) (loopP@i)) loopQ loopQ` — the textbook `l = r`,
      `top = bottom` cubical presentation, with `T2.rec` reducing on
      `loopP@i`/`loopQ@i`/`surf@i@j` alike.
    - **3-path ("cube")** constructors (`CubCubeSpec`): a fully-degenerate
      3-cell one dimension up from "S²" — the **3-sphere `S³`**: one point
      `base`, one 3-cell `cube : Path (Path (Path S³ base base) (refl base)
      (refl base)) (refl (refl base)) (refl (refl base))`, with `S3.rec`
      reducing on `cube@i@j@k` to `((u@i)@j)@k`.
    - `S1c` and `I2` are re-derivable through this general schema (see that
      module's tests).

`declare_cubical_hit` is also the mechanism for declaring a
**set-quotient-style HIT** without going through the propositional `Quot`: a
single fielded point constructor `mk : A → Q` plus a quantified path
constructor `eq : Π (a b : A) (h : R a b). Path Q (mk a) (mk b)` is exactly one
`CubHitSpec`, giving a genuinely-computing quotient path in place of
`Quot.sound`'s propositional one — surfaced as the worked example `SetQ`
(`SetQ.mk`/`SetQ.glue`/`SetQ.rec`, quotienting a two-point domain `SQDom` by
the "collapse everything" relation `SQDom.R`, mirroring
`examples/proofs/quotient_demo.rv`'s `AlwaysR`/`Quot` example but with a
genuinely-reducing `glue` path in place of `Quot.sound`).

## 3. Equivalences (`equiv.rs`, `contr.rs`, `equiv_hae.rs`)

No primitive `Σ`-type exists in this kernel (structured data goes through
hand-built single-constructor inductives instead), so each equivalence notion
is its own record-shaped inductive:

- `Equiv A B` (`crates/rv-kernel-core/src/equiv.rs`) — **bi-invertible**: `f :
  A → B`, `g : B → A`, `sec : Π b. Path B (f (g b)) b`, `ret : Π a. Path A (g
  (f a)) a`, with no coherence required between `sec`/`ret`. `idEquiv` is the
  identity map's instance. This is exactly what `Glue`'s strictness laws need
  computationally.
- `IsContr A` / `Fiber A B f b` / `IsEquiv A B f := Π b. IsContr (Fiber A B f
  b)` (`crates/rv-kernel-core/src/contr.rs`) — the **contractible-fibers**
  notion (HoTT book §4.2/§4.4), plus `idIsEquiv : Π A. IsEquiv A A (id A)`.
- `IsHAE A B f` (`crates/rv-kernel-core/src/equiv_hae.rs`) — the
  **half-adjoint** notion (HoTT book §4.2.1): `f`/`g`/`sec`/`ret` plus a
  coherence field `tau` (the triangle identity is *stated* as a field of the
  right type; `idHAE`'s own `tau` witness is the deferred piece — see that
  module's doc for exactly what is and is not proved).

## 4. `Glue`/`ua` (`glue.rs`, `Term::Glue`/`Term::Unglue`/`Term::GlueIntro`)

`Glue A [φ_1 ↦ (T_1,e_1), …]` is a type that is `T_k` where `φ_k` holds and `A`
off every face, glued to `A` by `e_k : Equiv T_k A`, with the strictness laws
`Glue A [.., φ_k ↦ .., ..] ↝ T_k` (φ_k decided ⊤) and `↝ A` (every φ_k decided
⊥). `unglue` is the identity off every face and `e_k.f` on a decided face.

`ua : Π (A B : Sort u) (e : Equiv A B). Path (Sort u) A B` is defined
(CCHM §6.3) as

```text
ua A B e := ⟨i⟩ Glue B [ (i=0) ↦ (A,e), (i=1) ↦ (B, idEquiv B) ]
```

and **type-checks** — `ua e` really is a `Path` between `A` and `B` — through
the ordinary `Checker`, exactly like every other term in this kernel.

## 5. Surfacing to `.rv` (this consolidation pass)

None of the above needed new surface grammar. Every construct is either (a) an
ordinary function/type installed once as a `Decl::Def`/`Decl::Axiom`/hand-built
inductive constant (exactly the `Quot`/`Trunc` pattern), reachable from `.rv`
through the ordinary `Expr::Var`/`Expr::Call` path and dotted-name field access
(`X.ctor`), or (b) already-existing surface grammar (`Path`/`PathP`/`plam`/
`papp`/`i0`/`i1`/`ineg`/`imeet`/`ijoin`, handled directly in
`crates/rv-kernel/src/elab2.rs`'s `Expr::{IZero,IOne,INeg,IMeet,IJoin,PLam,
PApp,PathTy,PathPTy}` arms, since `I` can never be an ordinary `Π`-domain).

- `crates/rv-kernel/src/cubical_surface.rs::install_cubical` — `Path`/`PathP`/
  `refl`/`ap`/`pfunext`/`transport`/`psubst`/`J`/`ptrans`/`path_to_eq`/
  `eq_to_path` (pre-existing).
- `crates/rv-kernel/src/cubical_surface.rs::install_ua` (new) — installs `ua`
  as an ordinary by-name-callable constant, requiring `Equiv`/`idEquiv` to
  already be installed.
- `crates/rv-kernel/src/kernel_ext.rs`'s `KernelExt` trait (new methods):
  - `install_s1c` → `rv_kernel_core::circle_cubical::install_circle_cubical`
    (`S1c`/`S1c.base`/`S1c.loop`/`S1c.rec`).
  - `install_s2` → `declare_cubical_hit` with a fixed `S2` spec (`S2`/
    `S2.base`/`S2.surf`/`S2.rec`).
  - `install_torus` → `declare_cubical_hit` with a fixed `T2` spec (`T2`/
    `T2.base`/`T2.loopP`/`T2.loopQ`/`T2.surf`/`T2.rec`).
  - `install_s3` → `declare_cubical_hit` with a fixed `S3` spec (`S3`/
    `S3.base`/`S3.cube`/`S3.rec`).
  - `install_set_quotient` → declares the demo domain `SQDom`
    (`SQDom.a`/`SQDom.b`) and relation `SQDom.R` (a plain `Decl::Def`), then
    `declare_cubical_hit` with a fielded-point/quantified-path `SetQ` spec
    (`SetQ`/`SetQ.mk`/`SetQ.glue`/`SetQ.rec`).
  - `declare_cubical_hit` → the general escape hatch, exposing
    `rv_kernel_core::cubical_hit::declare_cubical_hit`/`CubHitSpec` directly
    (used by `install_s2`/`install_torus`/`install_s3`/`install_set_quotient`;
    also how any other set-quotient-style HIT can be declared, per §2 above).
  - `install_equiv` → `Equiv`/`idEquiv` (`rv_kernel_core::equiv`).
  - `install_contr` → `IsContr`/`Fiber`/`IsEquiv`/`idIsEquiv`
    (`rv_kernel_core::contr`).
  - `install_hae` → `IsHAE`/`idHAE` (`rv_kernel_core::equiv_hae`).
  - `install_ua` → `ua` (above).
- `crates/rv-driver/src/lib.rs`'s prelude (`verify_rv_session`/`vm_eval`/
  `nbe_eval`) calls all of the above, after `install_cubical`, so every `.rv`
  program sees the whole layer by name with no per-file setup.

Nothing here adds new trusted machinery: every installer either calls straight
into `rv-kernel-core`'s existing, already-argued-sound installers, or (for
`install_ua`) builds an ordinary `Decl::Def` whose value the kernel's own
`Checker` re-checks against its declared type at install time — a bug in this
surfacing layer can only make installation *fail*, never make an unsound term
verify.

## 6. Known limitation: `ua` is stated, not computational

`ua e : Path (Sort u) A B` type-checks, but **`transport (ua e) a` does not
reduce to `e.f a`** — the computation rule that makes univalence usable as a
rewriting principle, not just an inhabited `Path`. `transport (ua e) a`
(equivalently `transp (λi. ua A B e @ i) a` composed with the `Sort`-level
`transp`/`hcomp` machinery `kan.rs` implements) stays a **soundly stuck**
`Term::Transp` term: it type-checks, it just doesn't reduce further, and this
is the correct, safe behavior for machinery that has not been proved to
compute the intended value — not a workaround, but the honest state of an
underivable rule.

This is not an oversight; `crates/rv-kernel-core/src/kan.rs`'s Phase 3.12–3.14
worklog documents three separate, in-depth attempts and why each was declined:

- **Phase 3.12** — `transp` through a `Glue` line, the direct CCHM
  `transp^{i.Glue …}` rule specialized to `ua`. Investigated and declined: a
  hard-coded pattern match on `ua`'s exact two-branch shape would assert the
  computation rule as a new axiom rather than derive it from `Glue`'s own Kan
  structure, and (at the time) `Term::GlueIntro` — the `glue` introduction
  form needed to even state the target value — did not yet exist.
- **Phase 3.13** — retried once `Term::GlueIntro` was added. Re-investigated
  and declined again, with a corrected diagnosis: the real prerequisite is a
  *generic* `hcomp_glue_rule` (an `hcomp` filling rule for `Glue`, mirroring
  the existing per-type-former `hcomp_pi_rule`/`hcomp_pathp_rule`/
  `hcomp_inductive_rule` dispatch), from which a `transp_glue_rule` could then
  be built — not a `ua`-specific shortcut. Non-regression was re-confirmed:
  `Term::GlueIntro`'s mere presence does not perturb `transp`'s existing
  (stuck) behavior on a `Glue` line.
- **Phase 3.14** — `hcomp_glue_rule` itself attempted, in depth, and declined
  with the sharpest diagnosis of the three: a sound construction needs each
  face's correction term `a'` built from an **`hcomp`-in-the-base-type-`A`**
  construction using `Equiv.sec`/`Equiv.ret`'s coherence data — i.e. it needs
  the *naturality square* the bi-invertible `Equiv` (§3 above) does not carry
  (`Equiv.sec`/`ret` have no coherence between them), pointing at the
  half-adjoint `IsHAE`/`τ`/`τ'` coherence field (`equiv_hae.rs`) as the
  missing ingredient, and — unlike Phase 3.13's obstruction — this one does
  not shrink by narrowing scope further (even the single-branch case still
  has the same cross-overlap obstruction).

In short: computational univalence needs genuine 2-dimensional naturality-
square tooling (an `hcomp_glue_rule` built from `IsHAE`'s coherence, not just
`Equiv`'s bi-invertibility) that has not been built. `ua` staying soundly stuck
under `transport` is the correct, checked state of the kernel today, not a
silently-accepted gap — every attempt and its precise failure mode is on
record in `kan.rs`'s own comments for the next pass to pick up.

## 7. What's not covered

- The *fully* general square schema: `CubSurfSpec`'s four sides are each
  restricted to `refl` or a single previously-declared, **unquantified
  self-loop** path (covers "S²" and the torus `T²`'s `l = r`/`top = bottom`
  shape, but not e.g. Eckmann–Hilton-style composite-path sides, quantified
  surfaces, or a surface based at a fielded point). Symmetrically, `CubCubeSpec`
  only supports the fully-degenerate ("S³") 3-cell boundary, not a general cube
  with independently-chosen faces.
- A `glue` (introduction) form for `Glue` general enough to inhabit an
  *undecided* `Glue` type is deliberately absent (a load-bearing soundness
  choice — see `glue.rs`'s `glue_type_is_uninhabited_without_real_data`).
- Computational univalence (§6) — `transport (ua e) a` still does not reduce
  to `e.f a`; nothing in this pass touched `kan.rs`'s Phase 3.12–3.14
  obstruction (needs `IsHAE`'s coherence field threaded into a generic
  `hcomp_glue_rule`, not just `Equiv`'s bi-invertibility).
