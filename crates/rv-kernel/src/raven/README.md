# Raven kernel-surface corpus (`.rvk`)

These `.rvk` files are the **Raven kernel-surface programs** that the kernel crate
loads and verifies — the standard library, the reflection prelude, and the verified
object-language metatheory (STLC, System F, the CEK machine, the typed object
language). They were previously embedded as `r#"…"#` string constants inside the
adjacent `.rs` modules; each is now a real file, included verbatim via
`include_str!` so the Raven code lives in editable, verifiable files rather than
Rust string literals.

The content is **kernel-surface syntax** (Lean-like: `inductive`, `def`, `Sort u`,
`.{u}` universe levels), which is why these are `.rvk` (the `rvc` CLI routes
`.rvk` → the dependent kernel) and not `.rv` (the Rust-like surface used by
`examples/proofs/*.rv`). They are loaded as **ordered sessions** (each fragment
builds on the constants declared by the previous one), so they are checked through
the kernel test suite — not standalone via `rvc --verify`.

| Prefix | Module | What it is |
|---|---|---|
| `stdlib_*`    | `stdlib.rs`    | the standard proof library (Eq, And/Or, Nat, List, …) |
| `reflect_*`   | `reflect.rs`   | the reflection prelude (`Decidable`, `decide`, `of_decide_eq_true`) |
| `typedlang_*` | `typedlang.rs` | a small typed object language + decidable type checker |
| `objlang_*`   | `objlang.rs`   | the first verified object-language pass |
| `stlc_*`      | `stlc.rs`      | the simply-typed λ-calculus: language, dynamics, progress, preservation |
| `systemf_*`   | `systemf.rs`   | System F: language, dynamics, and full type safety (incl. substitution lemmas) |
| `cek_*`       | `cek.rs`       | the CEK abstract machine: machine, metatheory, type-safety, adequacy, pipeline |

The Rust-like `.rv` *rewrite* of this material (data as `enum`s, lemmas as `fn`s) is a
separate, ongoing effort — see [`examples/proofs/`](../../../../examples/proofs/),
where the same theorems (type soundness, compiler correctness, full type safety for
typed arithmetic, the CEK machine) are written in the traditional-developer-facing
syntax.
