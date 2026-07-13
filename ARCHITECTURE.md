# raven-v3 architecture

Two backends behind one `.rv` surface: an executable pipeline (**parse → lower →
infer/elaborate → verify → compile → run**) and a dependent proof kernel (**parse →
elaborate → check**), organized so the *trust base is small and physically isolated* and
concerns don't cross-cut. `rv-driver` classifies each declaration by fragment and routes
it to the appropriate backend, merging both into one report.

## Crate graph (dependencies point downward)

```
rvc (bin)
  └─ rv-driver ── orchestrates BOTH pipelines; classifies items by fragment, routes, merges
       │
       ├─ EXECUTABLE PIPELINE
       │    ├─ rv-syntax   ── lexer + parser → surface AST + fragment classification (deps: arena)
       │    ├─ rv-lower    ── AST → IR<Parsed>                              (deps: syntax, ir, core)
       │    ├─ rv-infer    ── IR<Parsed> → IR<Lowerable> + obligations      (deps: ir, core, logic)
       │    ├─ rv-borrow   ── ownership substrate: FracPerm resource algebra + QTT grade semiring
       │    ├─ rv-borrowck ── borrow/ownership checker over the IR         (deps: ir, borrow)
       │    ├─ rv-solve    ── discharge obligations (linear arith + prop)  (deps: core, logic)
       │    ├─ rv-codegen  ── IR<Lowerable> → bytecode                     (deps: ir, core)
       │    ├─ rv-vm       ── run bytecode                                 (deps: codegen)
       │    └─ rv-db       ── salsa incremental engine over the above      (deps: syntax, lower, infer, ...)
       │
       └─ PROOF PIPELINE
            └─ rv-kernel   ── UNTRUSTED elaborator/tactics/surface installers (deps: rv-kernel-core)
                 └─ rv-kernel-core ── THE TRUSTED KERNEL (zero deps on rv-kernel or anything above)

foundation (written first, fixed):
  rv-logic ── resource algebra trait, Prop obligations, Solver registry      (deps: core)
  rv-ir    ── phase-indexed IR (Trees That Grow), places, terminators        (deps: arena, core)
  rv-core  ── executable-path kernel: Ty, Term, first-order Prop + checker   (deps: arena)
  rv-arena ── ids, interner, arenas, SideTable<T>                           (no deps)
```

## The two kernels

Raven has **two** trusted checkers, one per fragment, deliberately kept separate rather
than merged into one god-kernel:

- **`rv-core`** (~500 LOC) — the executable path's kernel: `Ty`/`Term`/a first-order
  `Prop` (arithmetic + logic over scalars and struct-field projections) + a checker. Small
  and dependency-light; what `rv-infer`'s obligations are ultimately checked against.
- **`rv-kernel-core`** — the dependent + cubical type theory kernel: a de Bruijn term
  language, universe levels, the bidirectional checker, β/δ/ζ/ι/Kan reduction, inductive
  families (including indexed-mutual), quotients, propositional truncation, coinductives,
  and the whole cubical layer (interval, `Path`/`PathP`, faces/systems, `transp`/`hcomp`,
  higher inductive types, `Equiv`/`IsHAE`/`IsContr`, `Glue`/`ua`). **Physically isolated**:
  it has zero dependency on `rv-kernel` or anything above it in the graph, so the
  untrusted elaborator, tactics, and surface syntax can only reach it through its checked
  public API — a bug in any of them can only cause a rejection, never an unsound accept.
  `rv-kernel` re-exports `rv-kernel-core`'s public items so existing `rv_kernel::Foo`
  import paths are unchanged; it also owns everything *not* required for soundness:
  elaboration from the `.rv` AST (`elab.rs`/`elab2.rs`), tactic/reflection support, generic
  installers for the standard axiomatic schemas (`kernel_ext.rs`'s `KernelExt` — inductive/
  coinductive declaration, `install_cubical`/`install_s1c`/`install_equiv`/`install_ua`/…),
  and the QTT usage-graded binder pass (`graded.rs`).

## Trust base (what a bug here is a soundness bug)

- **`rv-core`** and **`rv-kernel-core`** — the two logics: term/type/checker definitions.
  Small, dependency-light, and (for `rv-kernel-core`) compiler-enforced isolation, not just
  documentation.
- **`rv-solve`**'s linear-arithmetic decision procedure — the one piece of the executable
  pipeline still trusted rather than certificate-checked. `Certificate` is designed to
  carry a proof; the **structural** discharge fragment already replays its certificates
  against the original obligation (so a structural-solver bug can only reject, never
  falsely accept) — moving the remaining linear-arithmetic core off the trust base the
  same way is open work.
- Everything else (`rv-syntax`, `rv-lower`, `rv-infer`, `rv-borrow`/`rv-borrowck`,
  `rv-codegen`, `rv-vm`, `rv-db`, `rv-driver`, and all of `rv-kernel` above the
  `rv-kernel-core` boundary) is *outside* the trust base: a bug there yields a
  stuck/rejected program or a failed obligation, never an unsound "verified".

## Cross-cutting-concern controls

- **Phases** (`rv-ir::Phase`) make "not-yet-inferred" a *type*, so you cannot lower
  un-elaborated IR; codegen accepts only `Lowerable`, enforced by the type system.
- **Side-tables** (`rv-arena::SideTable`) hold every analysis result keyed by `NodeId`; the
  IR core carries no lifetime/strategy/ordering fields.
- **Solvers are a registry** (`rv-logic::SolverRegistry`); obligation routing is data, not
  a baked-in enum.
- **Disciplines/resource algebras are traits** (`rv-logic`, `rv-borrow`'s `FracPerm`/QTT
  grade semiring); no concrete discipline is named by either core.
- **Fragment classification is data, not a second parser.** `rv-syntax::fragment`
  classifies each top-level item (executable / proof / shared) from the *one* AST;
  `rv-driver` routes by that classification instead of running two front-ends. A shared
  `enum`/`struct` is elaborated once and used by both backends (`examples/shared_type.rv`).
- **QTT grade-driven erasure.** A proof-fragment declaration (grade 0, a term whose type is
  a `Prop`) is checked by `rv-kernel-core` and then erased to zero runtime bytes
  (`rv-kernel/src/erase.rs`); a proof-fragment entry point can additionally be erased,
  compiled to bytecode by the *same* codegen path as executable code, and run natively on
  `rv-vm` — recursors (including mutual groups) compile to tag-switching functions, so the
  executable and dependent fragments share one reduction engine end to end.

## The cubical/HoTT layer

Lives inside `rv-kernel-core` (interval, `Path`/`PathP`, faces/systems/Kan ops, HITs,
`Equiv`/`IsHAE`/`IsContr`, `Glue`/`ua` — all part of the trusted core's typing/reduction
rules) with its surface installers in `rv-kernel/src/cubical_surface.rs` and
`kernel_ext.rs` (untrusted: each installer either calls straight into an already-argued-
sound `rv-kernel-core` function, or builds an ordinary `Decl::Def` whose value the
checker re-verifies against its declared type at install time — a bug in the surfacing
layer can only make installation fail, never make an unsound term verify). See
`docs/cubical.md` for the complete map of what exists, how it is surfaced, and — honestly
— what is not yet computational (`ua`'s computation rule, and hence the univalence
theorem).

## Scope of this slice (honest)

- **Executable fragment**: `fn`/`let`/`struct`/`enum`/generics/traits/closures,
  `&`/`&mut`/`*` (borrow-checked, strong updates), arrays/`Vec` with verified bounds, loop
  invariants, refinement types, `requires`/`ensures`, checked overflow, fixed-width
  integers including `i128`. Specs are first-order over scalars and struct-field
  projections; deeper aggregate reasoning (bounding a field's *range*, not just its
  identity) is still future `rv-core` growth.
- **Proof kernel**: dependent types, indexed-mutual inductives, quotients, propositional
  truncation, coinductives, graded QTT usage contexts, and the cubical/HoTT layer above.
  Open: computational univalence (`docs/cubical.md` §6), `trans_assoc` (`#[ignore]`d,
  nine investigative passes in), coinductives not yet surfaced by name to `.rv`.
- **Verification**: a sound, deliberately-incomplete linear-integer-arithmetic +
  propositional decision procedure for the executable fragment (no external SMT, no AI
  proving); full bidirectional type/definitional-equality checking (including Kan
  operations) for the proof fragment.
- **Backend**: a register/stack bytecode + interpreter shared by both fragments, so
  `compile + run` is self-contained for executable code and for erased proof entry points
  alike.
