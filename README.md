# raven-v3

**Ownership × dependency, in one type system.** Raven is a Rust-like language that is
also a full dependent-type proof assistant: the same `.rv` surface writes ordinary
borrow-checked programs *and* the mathematics that proves them correct, checked by a
small, physically isolated trusted kernel.

```
source ──parse──▶ AST ──classify by fragment──┬─▶ executable: infer/borrowck/solve ──▶ bytecode ──▶ VM
   (rv-syntax)        (rv-syntax::fragment)    │
                                                └─▶ proof: elaborate ──▶ rv-kernel-core (the kernel)
```

One parser, one AST. `rvc f.rv` classifies each item — executable, proof, or shared
data type both backends need — and routes it: executable code to `rv-solve` (obligation
discharge) + `rv-vm` (bytecode), proofs to the dependent kernel. A single file can mix
both (`examples/mixed.rv`) and get one merged verdict.

## Try it

```sh
cargo run -p rvc -- examples/div.rv --run                            # executable: VERIFIED, main() = Int(5)
cargo run -p rvc -- examples/mut_ref_spec.rv --run                   # strong update through &mut: Int(5)
cargo run -p rvc -- examples/unsafe_div.rv                           # NOT VERIFIED (intentional negative)
cargo run -p rvc -- examples/mixed.rv --run                          # one file: an inductive theorem + a VM-run main()
cargo run -p rvc -- examples/proofs/capstone.rv --run --entry main   # the consolidation showcase (below)
cargo run -p rvc -- examples/proofs/cubical_showcase.rv --verify     # the cubical/HoTT layer, kernel-checked
cargo test --workspace                                                # ~960 tests across the workspace
```

## The feature ladder

**Executable fragment** (`fn`/`let`/`struct`/`enum`/generics/traits/closures, checked by
`rv-infer`+`rv-borrowck`, discharged by `rv-solve`, run on `rv-vm`):

- `&`/`&mut`/`*` references, **borrow-checked** (move tracking as affine QTT usage
  grades, conflicts as `FracPerm` composition validity, NLL-style liveness-driven borrow
  ends). A unique `&mut` licenses a **strong update**: the verifier can prove
  `result == 5` after `*r = 5` because it knows the write touches exactly the pointee
  (`examples/mut_ref_spec.rv`).
- Refinement types (`type Pos = i64 where self > 0`) and `requires`/`ensures`, discharged
  by a sound (deliberately incomplete) linear-arithmetic + propositional decision
  procedure — no external SMT.
- Arrays/`Vec` with **verified bounds** (every index emits a `0 <= i < len` obligation,
  checked against a static length or a symbolic `.len()`), **loop invariants** (proved by
  induction — an invariant's own facts must be self-contained; a `requires` fact not
  restated in the invariant is dropped at the loop header, the standard inductive-invariant
  discipline, see `examples/loop_invariant.rv`), **checked overflow** (`+`/`-`/`*` must be
  proved in-range; `wrapping_*` opts out explicitly), fixed-width integers (`i8`..`i128`/
  `u8`..`u64`, width-specific bounds).
- `panic`, `Result`/`Option`, the `?` operator, generics (type-erased), traits/`impl`.

**Proof kernel** (`rv-kernel` elaborating onto the trusted `rv-kernel-core`): dependent
types, inductives, **indexed-mutual inductives**, **quotient types** (`Quot`/`mk`/`sound`/
`lift`/`ind`), **propositional truncation** (`Trunc`, a 1-HIT), **coinductives**
(`declare_coinductive`/`CoindSpec` — greatest fixpoints with generated corecursors;
present and kernel-tested, not yet surfaced by name into `.rv` examples), and **graded
QTT usage contexts** (`(x :1 T)` linear / `(x :0 T)` erased / unannotated unrestricted
binders, checked by a dedicated usage pass — a linear binder used twice is a hard
verification error, `examples/proofs/graded_demo_linear_violation.rv`).

**Cubical type theory** (the newest, deepest layer — see `docs/cubical.md` for the full
map): a De Morgan **interval** with `ineg`/`imeet`/`ijoin`, **`Path`/`PathP`** with
introduction/elimination and path-η, **faces and systems** for partial elements, **Kan
operations** (`transp`/`hcomp`) with per-type-former filling rules, and derived
combinators that genuinely compute (`refl`/`ap`/`funext`/`transport`/`J`/`trans`) — `J`
computes on `refl`, not just propositionally. On top of that: **higher inductive types**
with real path constructors whose recursor ι-rules fire *at* the constructor — the
interval HIT `I2`, the cubical **circle `S1c`** (a genuine self-loop), **spheres
`S2`/`S3`/`S4`**, the **torus `T2`**, and **set-quotient-style HITs** via a general schema
(`declare_cubical_hit`). Above that: the **`Equiv`/`IsHAE`/`IsContr`/`IsEquiv`**
equivalence hierarchy, an **equivalence algebra** (`idToEquiv`/`symEquiv`/`compEquiv`,
groupoid unit/involution laws, `ap`-functoriality), an **h-level hierarchy**
(`isProp`/`isSet`/`isGroupoid`, `isContrToIsProp`), and **`ua`** (univalence, *stated* and
type-checked via `Glue`). All of it reachable by name from `.rv` source — see
`examples/proofs/cubical.rv` and `cubical_showcase.rv`.

## Trust base

The kernel is small and **physically isolated**: `rv-kernel-core` has zero dependency on
anything else in the workspace, so nothing outside it — elaboration, tactics, surface
syntax, the executable pipeline — can influence what it accepts short of going through
its checked public API. A bug anywhere else can only *reject* a program or fail to prove
one; it can never make an unsound term type-check. Two kernels exist for the two
fragments: `rv-core` (small, ~500 LOC — the executable path's first-order `Prop`) and
`rv-kernel-core` (the dependent/cubical kernel).

`rv-solve`'s linear-arithmetic decision procedure is the one remaining piece still
*trusted* rather than checked: it emits `Certificate`s designed to carry a proof, and the
**structural** discharge fragment already replays its certificates against the original
obligation instead of being trusted outright (so a structural-solver bug can only reject,
never falsely accept) — the linear-arithmetic core itself is the last trusted solver
component. See `docs/trust-architecture.md` for the full discipline: model everything
machine-shaped (integers, references, effects, even non-termination) *in* Raven and
compile it down to the kernel's small vocabulary, rather than growing the kernel to meet
the runtime language partway.

## The capstone: `examples/proofs/capstone.rv`

One file, the whole ladder, each section independently checked and commented:

1. An executable `fn` with a borrow-checked strong update through `&mut` and a
   refinement-typed (`NonZero`) division precondition, discharged by `rv-solve` and run
   on the VM.
2. An inductive proof by recursion (`add_zero : add(n, Z) == n`, induction on `n`) —
   grade-0, erased to zero runtime bytes.
3. Cubical `refl`/`ap`/`transport`/`J`.
4. The genuinely-computing HIT recursor `S1c` (a real self-loop, checked to reduce back
   to the base-point value at both boundaries — not merely propositionally).
5. The `Equiv` algebra: `idEquiv`/`symEquiv`/`compEquiv`.
6. `ua`/`Univalence`, **stated** — with an explicit comment on exactly what remains open
   (below).

```sh
cargo run -p rvc -- examples/proofs/capstone.rv --run --entry main   # VERIFIED, main() = Int(7)
```

## Open frontier — honest, not overclaimed

**Computational univalence is not done.** `ua e : Path Type A B` type-checks — it really
is a path between the two types — but `transport (ua e) a` does **not** reduce to `e.f a`.
It stays a soundly-stuck `Term::Transp` term: correct and safe, just not yet a usable
rewriting principle. Three separate, in-depth attempts are on record and declined
(`rv-kernel-core/src/kan.rs`'s Phase 3.12–3.14 worklog): the blocker is a generic
`hcomp_glue_rule` for `Glue` that needs `IsHAE`'s coherence field (the half-adjoint
notion), not just `Equiv`'s bi-invertibility — a naturality-square construction that has
not been built. Transitively blocked on the same gap: `biInvToHAE`, Glue-Kan reasoning,
`isPropToIsSet`, and the **`Univalence` theorem** (its *statement* type-checks and is
by-name-callable — see `examples/proofs/cubical_showcase.rv`'s `univalence_axiom` — but it
is assumed, not proved). See `docs/cubical.md` §6 for the complete diagnosis, one attempt
at a time, so the next pass can pick it up precisely where it was left.

Also open, smaller: `trans_assoc` (path-transitivity associativity) is `#[ignore]`d after
nine investigative passes pinpointed a subtle NbE/path-algebra completeness gap — the same
root cause blocking the full-record `Equiv` unit laws and, transitively, univalence.
Coinductives are kernel-complete but not yet surfaced by name into `.rv` examples. The
`rv-solve` linear-arithmetic core remains trusted rather than certificate-checked.

## Crates (dependencies point downward; see `ARCHITECTURE.md`)

| crate | role | trust |
|---|---|---|
| `rv-arena` | ids, interner, side-tables | — |
| `rv-core` | executable-path kernel: `Ty`/`Term`/first-order `Prop` + checker | **trusted** |
| `rv-kernel-core` | the dependent + cubical type theory kernel (physically isolated) | **trusted** |
| `rv-kernel` | untrusted elaborator/tactics/surface installers on top of `rv-kernel-core` | — |
| `rv-ir` | phase-indexed IR (Trees That Grow) | — |
| `rv-logic` | obligations, solver registry, resource-algebra traits | — |
| `rv-syntax` | lexer + parser → AST, and fragment classification | — |
| `rv-lower` | AST → `IR<Parsed>` | — |
| `rv-infer` | typecheck + phase fill + VC generation | — |
| `rv-solve` | linear-arithmetic + propositional decision procedure | linear-arithmetic core **trusted**; structural discharges replayed via certificate |
| `rv-codegen` | `IR<Lowerable>` → bytecode | — |
| `rv-vm` | bytecode interpreter | — |
| `rv-borrow` | ownership substrate: fractional-permission resource algebra + QTT grade semiring | — |
| `rv-borrowck` | borrow/ownership checker (moves as affine usage grades, borrows as `FracPerm` validity, NLL-style liveness) | — |
| `rv-db` | salsa incremental engine: memoized, dependency-tracked pipeline queries | — |
| `rv-driver` | pipeline orchestration: classifies + routes each item, merges one report | — |
| `rvc` | CLI: `rvc f.rv [--run] [--verify] [--entry name]` | — |

## Scope (honest)

A large, still-growing vertical slice, not the full design. The executable fragment's
specs are first-order over scalars and struct fields (a spec may project `p.v` as an
uninterpreted field term); deeper aggregate reasoning (proving a *bound* on a field, not
just its identity) is still future `rv-core` growth — several examples use `wrapping_add`
where a checked `+` would need exactly that (`examples/point.rv`,
`examples/generic_trait.rv`). The solver is sound but deliberately incomplete
linear-integer-arithmetic + propositional; no external SMT, no AI proving. The proof
kernel's open frontier is computational univalence, above.

See `ARCHITECTURE.md` for the trust boundary and crate graph, `docs/cubical.md` for the
cubical/HoTT layer in depth, `docs/trust-architecture.md` for the modeling discipline, and
`docs/raven-language.md` for the unified surface design (one `.rv` language, two
backends).
