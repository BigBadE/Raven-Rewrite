# raven-v3 architecture

Implements `docs/semantic-ir-v3.md` (the design). A vertical slice of the full pipeline:
**parse → lower → infer/elaborate → verify → compile → run**, organized so the *trust base
is small* and *concerns don't cross-cut*.

## Crate graph (dependencies point downward)

```
rvc (bin)
  └─ rv-driver ── orchestrates the pipeline; the only crate that knows all phases
       ├─ rv-syntax  ── lexer + parser → surface AST            (deps: rv-arena)
       ├─ rv-lower   ── AST → IR<Parsed>                        (deps: syntax, ir, core)
       ├─ rv-infer   ── IR<Parsed> → IR<Lowerable> + obligations(deps: ir, core, logic)
       ├─ rv-solve   ── discharge obligations (decidable frag)  (deps: core, logic)
       ├─ rv-codegen ── IR<Lowerable> → bytecode                (deps: ir, core)
       └─ rv-vm      ── run bytecode                            (deps: codegen)

foundation (the contracts; written first, fixed):
  rv-logic ── resource algebra trait, Prop obligations, Solver registry  (deps: core)
  rv-ir    ── phase-indexed IR (Trees That Grow), places, terminators    (deps: arena, core)
  rv-core  ── THE KERNEL / trust base: Ty, Term, Prop + checker          (deps: arena)
  rv-arena ── ids, interner, arenas, SideTable<T>                        (no deps)
```

## Trust base (what a bug here is a soundness bug)

- **`rv-core`** — the logic: the type/term/`Prop` definitions and the checker. Small, dependency-light.
- **`rv-solve`** — until it emits checkable certificates, a sound solver is trusted. (`Certificate`
  is designed to carry a proof later; for now `Provenance::TrustedBase` marks solver-discharged goals.)
- Everything else (`syntax`, `lower`, `infer`, `codegen`, `vm`, `driver`) is *outside* the trust base:
  a bug there yields a stuck/rejected program or a failed obligation, never an unsound "verified".

## Cross-cutting-concern controls

- **Phases** (`rv-ir::Phase`) make "not-yet-inferred" a *type*, so you cannot lower un-elaborated IR.
- **Side-tables** (`rv-arena::SideTable`) hold every analysis result keyed by `NodeId`; the IR core
  carries no lifetime/strategy/ordering fields.
- **Solvers are a registry** (`rv-logic::SolverRegistry`); obligation routing is data, not a baked-in enum.
- **Disciplines/resource algebras are traits** (`rv-logic`); no concrete discipline is named by the core.

## Scope of this slice (honest)

- Surface language: `fn`, `let`, `i64`/`bool`, arithmetic/comparison/logic, `if`/`while`, `return`,
  `requires`/`ensures`/`assert` clauses.
- Kernel: a small typed core + first-order `Prop` (arithmetic + logic). The path to full
  QTT/guarded/dependent (per the design) is left as `rv-core` growth; the *architecture* is faithful.
- Verification: division-by-zero, `assert`, and `ensures` obligations, discharged by a built-in
  linear-integer-arithmetic + congruence solver. (No external SMT; no AI proving — out of scope here.)
- Backend: a register/stack bytecode + interpreter, so `compile + run` is self-contained.
