# raven-v3

A from-scratch vertical slice of the Semantic IR v3 design (`docs/semantic-ir-v3.md` in
the design repo): a verification-oriented compiler whose pipeline runs **all the way from
parsing to compiling + proving**.

```
source ──parse──▶ AST ──lower──▶ IR<Parsed> ──elaborate──▶ IR<Lowerable> + obligations
                                                                │              │
                                                       compile ▼      discharge ▼ (solver registry)
                                                          bytecode         verified?
                                                                │
                                                            run ▼
                                                            result
```

## Try it

```sh
cargo run -p rvc -- examples/div.rv --run     # VERIFIED, then main() = Int(5)
cargo run -p rvc -- examples/recip.rv         # VERIFIED  (x > 0 ⟹ x != 0, via linear arithmetic)
cargo run -p rvc -- examples/unsafe_div.rv    # NOT VERIFIED  (100/x with no precondition)
cargo test                                    # 218 tests across the workspace
```

## Crates (dependencies point downward; see `ARCHITECTURE.md`)

| crate | role | trust |
|---|---|---|
| `rv-arena` | ids, interner, side-tables | — |
| `rv-core` | **kernel**: `Ty` / `Term` / `Prop` + checker | **trusted** |
| `rv-ir` | phase-indexed IR (Trees That Grow) | — |
| `rv-logic` | obligations, solver registry, resource-algebra traits | — |
| `rv-syntax` | lexer + parser → AST | — |
| `rv-lower` | AST → `IR<Parsed>` | — |
| `rv-infer` | typecheck + phase fill + VC generation | — |
| `rv-solve` | linear-arithmetic + propositional decision procedure | **trusted** (until certificates) |
| `rv-codegen` | `IR<Lowerable>` → bytecode | — |
| `rv-vm` | bytecode interpreter | — |
| `rv-borrow` | ownership substrate: fractional-permission resource algebra + QTT grade semiring | — |
| `rv-borrowck` | borrow/ownership checker: move tracking + borrow conflicts over the IR | — |
| `rv-db` | **salsa** incremental engine: source input + memoized, dependency-tracked pipeline queries | — |
| `rv-rustfe` | **real-Rust frontend**: rust-analyzer's parser (`ra_ap_syntax`) → IR for a Rust subset (`.rs` files) | — |
| `rv-driver` | pipeline orchestration (toy frontend via salsa; `.rs` via `rv-rustfe`) | — |
| `rvc` | CLI | — |
| `rv-coverage` | dev tool: measure `rv-rustfe` lowering coverage over a real-Rust corpus + histogram failure reasons | — |

## Design properties realized here

- **Small trust base.** Only `rv-core` (and, for now, the `rv-solve` decision procedure)
  can host a soundness bug. The other ten crates can only reject a program or fail to
  prove one — never falsely "verify".
- **Phases make illegal states unrepresentable.** `IR<Parsed>` has no types; `IR<Lowerable>`
  has them and a memory strategy. Codegen accepts only `Lowerable` — enforced by the type
  system (`rv_ir::Phase`).
- **Side-tables, not embedded facts.** Analysis results are keyed by node, outside the IR core.
- **Solvers are a registry**, not a baked-in enum; **disciplines are traits** the core never names.

## Language features today

`fn` · `let` · `i64`/`bool` · arithmetic/comparison/logic · `if`/`else` · `while` · `return` ·
`struct` · `enum` · `match` (exhaustiveness-checked) · field access (readable in specs:
`requires p.v != 0`) · `requires` · `ensures` ·
`assert` · `while … invariant …` (loop invariants proved by induction) · **`&`/`&mut`/`*`
references** (borrow-checked: move tracking + conflict detection) · **generics** (`fn f<T>`,
`struct S<T>`, `enum E<T>`; type-erased) · **traits / `impl` / methods** (`x.method()`,
desugared to functions + resolved calls).

Effects: **`panic`** (aborts the path), **`Result`/`Option` enums**, and the **`?` operator**
(desugared to match + early-return).

**Real-Rust frontend (`rv-rustfe`, `.rs` files via tree-sitter):** free `fn`s, `struct`/`enum`,
generics, references, `match`/`if`/`else` (in **statement *and* value position** —
`let x = match ..` / `let y = if ..`), **`if let`**, **`while`/`loop`/`for a..b` with `break`/`continue`**,
compound assignment (`+=`), **`impl` blocks + `trait` impls + methods** (inc. `self.m()` chains),
**`?`**, **`panic!`/`assert!`/`assert_eq!` macros**, **`let S { x, y } = ..` struct destructuring**,
**tuples** (`(a, b)`, `t.0`, `let (x, y) = t`), **fixed arrays** (`[a, b, c]`, `[x; N]`, `a[i]`,
`a[i] = v`), **`Vec<T>`** (`Vec::new`, `push`, `len`, indexing), a built-in **`Option`/`Result`
prelude** with **combinators** (`unwrap`/`unwrap_or`/`is_some`/`is_ok`/`expect`/…),
unqualified variants (`Some`/`None`/`Ok`/`Err`), **`Self`** (`Self { .. }`, `Self::new`),
`as` casts, **sized integers** (`i8`/`i16`/`i32`/`u8`/`u16`/`u32` carry their width), and
`#[requires(..)]`/`#[ensures(..)]` specs. Parsed by **rust-analyzer** (`ra_ap_syntax`).

**Array & `Vec` bounds are checked.** Every `a[i]` / `v[i]` (read or write) emits a bounds
obligation (`0 <= i < len`): a fixed array against its static length, a `Vec` against its
*symbolic* length (so a constant `a[5]` on a length-3 array does **not** verify, while a
`if i < v.len()` guard discharges `v[i]`).

**Sized-integer overflow is width-specific.** A `u8` add emits `a + b <= 255`, so it must be
proved in range (a `u8` parameter carries its implicit `0 <= a <= 255`); `i64`/`usize`/… keep
the default i64-range check. `wrapping_*` opts out, as always.

**Modules + multi-file.** Inline `mod m { .. }` blocks are flattened, `use` is accepted, and
multiple `.rs` files compile together as one program (`rvc a.rs b.rs`). Names share one flat
namespace; a path-qualified reference (`m::f`, `Type::assoc`, `m::Type`) resolves by its last
segment.

**Checked-overflow discipline.** `+`/`-`/`*` emit an *overflow obligation* — the result must be
proved to stay within `i64` range — so an unbounded `a + b` does **not** verify (it can overflow),
while a bounded one does. To wrap intentionally, use the explicit opt-out: `a.wrapping_add(b)`
(Rust path) / `wrapping_add(a, b)` (toy path), which emits no obligation. *Not overflowing is a
proof; overflow must be handled explicitly.*

Incremental: the pipeline is a **salsa** query graph (`rv-db`) — re-analysis memoizes and
recomputes only what a source change affects.

Verified end-to-end: division-by-zero safety, assertions, modular call pre/postconditions,
refinement preconditions (via linear arithmetic), match exhaustiveness, and loop invariants.

## Scope (honest)

A growing vertical slice, not yet the full design. The kernel is a small typed core +
first-order `Prop` (full QTT/guarded/dependent is `rv-core` growth — so specs are first-order
over scalars, now including **struct fields**: a spec may project `p.v` as an uninterpreted
field term, so `requires p.v != 0` discharges a body's division by `p.v` via congruence;
deeper aggregate reasoning — equational struct/enum theories — is still future `rv-core`
growth). The solver
is a sound, deliberately-incomplete linear-integer-arithmetic + propositional prover (no
external SMT, no AI proving). The backend is a bytecode interpreter. Open frontier: closures /
higher-order combinators (`map`/`and_then`), wider integers (`u64`/`i128`) with sound bounds,
spec field-access in the real-Rust frontend (the toy frontend has it), and moving the `rv-solve`
decision procedure out of the trust base via checkable certificates. See `ARCHITECTURE.md` for
the trust boundary.
