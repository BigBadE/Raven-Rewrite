# Verified math in Rust-like Raven

These `.rv` files are **verified mathematics written as ordinary Rust-like code** — data are
`enum`s, relations are indexed `enum`s, lemmas are `fn`s whose return *type* is the
proposition, and induction is recursion. Each is checked through the dependent kernel:

```sh
rvc --verify examples/proofs/<file>.rv     # prints VERIFIED
```

The `Eq` combinators (`subst`, `symm`, `trans`, `congr_arg`) come from the standard proof
prelude, [`crates/rv-driver/prelude.rv`](../../crates/rv-driver/prelude.rv), which `rvc
--verify` loads automatically. The whole corpus is checked in CI by
[`crates/rv-driver/tests/rv_proofs.rs`](../../crates/rv-driver/tests/rv_proofs.rs).

| File | Theorem | Techniques |
|---|---|---|
| `nat_induction.rv`     | `n + 0 == n` | induction, `congr_arg` |
| `nat_arithmetic.rv`    | `plus_comm` (+ `plus_succ`) | induction, `trans`/`symm` chaining |
| `arith_assoc.rv`       | associativity of `+` | induction |
| `mul.rv`               | `n * 0 == 0`, lemma composition | induction, `subst` |
| `bool_logic.rv`        | `not_not`, `and_false` | case analysis |
| `list.rv`              | `length (xs ++ ys) == len xs + len ys` | induction |
| `append_assoc.rv`      | `(xs ++ ys) ++ zs == xs ++ (ys ++ zs)` | induction |
| `list_map.rv`          | `length (map f xs) == length xs` | induction, **higher-order** `f` |
| `optimizer.rv`         | `eval (opt e) == eval e` (constant folding) | induction, `trans`/`congr_arg` |
| `indexed_relation.rv`  | `Plus` (graph of `+`) + structural induction | **indexed `enum`**, `.rec` |
| `mutual_trees.rv`      | `Tree`/`Forest` sizes (computes) | **mutual `enum`s**, mutual recursion |
| `compiler_correctness.rv` | `EvalS e v ⟹ EvalT (compile e) v` | mutual `Val/Env` **closures**, two indexed relations |
| `type_soundness.rv`    | well-typed `e` ⟹ `eval e` well-typed | **canonical-forms inversion** (no-confusion) |
| `le.rv`                | `<=` reflexive, `le_succ` | indexed relation |
| `le_trans.rv`          | transitivity of `<=` | **inversion + convoy + index-changing recursion** |
| `typed_arith.rv`       | **full type safety** (progress + preservation) for TAPL ch.8 typed arithmetic | indexed typing + small-step relations, canonical forms, structural typing inversion, injectivity, IH convoy |
| `cek_machine.rv`       | the CEK abstract machine — **runs** `(λx. x+1) 2 ⟹ 3` | mutual `Val/Env/Kont`, fuelled driver |
| `refinement.rv`        | `safe_pred(2)` — a precondition in the type | **refinement types** (`x: T where p`) with **auto-discharge** |

Nothing here uses special proof syntax: it all reads as recursive Rust functions over `enum`s.
The design is described in [`docs/raven-language.md`](../../docs/raven-language.md).
