# Raven — the unified language

This is the design for Raven as a *single* Rust-like language in which you write both
ordinary programs and the verified mathematics that justifies them. It supersedes the
earlier split between the executable surface (`rv-syntax` → VM) and the dependent kernel
surface (the Lean-like strings inside `rv-kernel`). Both become one surface, `.rv`, with two
lowering targets behind one type system.

The north star: **a traditional developer can read every line.** Proofs are functions,
relations are `enum`s, induction is recursion, and most verification is invisible (it lives
in the types). You only write an explicit proof when the solver can't, and even then it reads
like recursive code.

---

## 1. One language, two backends, one type system

```
            .rv source
               │  rv-syntax (lexer + parser)  → one AST
               ▼
        rv-elab (elaboration + QTT grading)
        ── splits each declaration by its runtime grade ──
          │                                   │
   grade > 0 (runtime)                  grade 0 (logical / erased)
          │                                   │
   rv-lower → rv-ir → rv-codegen → rv-vm   rv-kernel  (dependent core: checks proofs)
   (executable bytecode)                   (the trust base; nothing runs)
```

- **One AST, one parser.** `fn`, `enum`, `struct`, `trait`, `impl`, `match`, `where`,
  `requires`/`ensures`, and effect rows are all ordinary surface forms.
- **QTT separates the worlds.** Quantitative Type Theory grades every function arrow; grade-0
  (logical/ghost) content is erased before codegen, so proofs and indices cost **zero bytes**
  at runtime. The compiler — not the programmer — decides what runs.
- **One type system.** Refinement types, dependent signatures, and effect rows are all
  *types*; the checker routes their obligations either to the decidable solver (`rv-solve`)
  or, for the dependent fragment, to the kernel (`rv-kernel`).

The kernel stays the small trust base: a soundness bug can only live in `rv-core`/`rv-kernel`
or in a still-trusted `rv-solve` certificate. Everything else yields a *rejected* program,
never an unsound "verified".

---

## 2. Surface design

### 2.1 Programs (unchanged, plus the obvious gaps filled)

```rust
fn add(x: i64, y: i64) -> i64 { return x + y; }

fn main() -> i64 {
    print("hello");          // strings + I/O (new)
    return add(2, 3) * 10;
}
```

New executable features to reach a usable language: **strings & `print`**, **floats**,
**closures / first-class `fn` values**, and a **prelude written in `.rv` itself**.

### 2.2 Refinement types — verification that lives in the type

A proposition baked into a type; the obligation is discharged automatically by `rv-solve`.

```rust
type Pos = i64 where self > 0;

fn div(x: i64, y: i64 where y != 0) -> i64 { return x / y; }   // div-by-zero discharged at the call
```

Flow-sensitive refinement (occurrence typing) makes facts available after a check:

```rust
if y != 0 {
    // here  y : i64 where y != 0,  so `div(x, y)` just type-checks
}
```

`requires`/`ensures` are sugar for refinements on the function's type, so a function value
carries its contract and higher-order functions can demand contracts of their arguments.

### 2.3 Relations / propositions — an indexed `enum`

An inductive *relation* is a plain `enum` parameterized by its indices; each variant lists
its premises as fields and pins the indices with a `where` clause.

```rust
// Evidence that `e` evaluates to `v` under `env`.
enum Eval(env: Env, e: Src, v: Val) {
    Lit(n: Nat)
        where e == Src::Lit(n), v == Val::Nat(n);

    Var(n: Nat)
        where e == Src::Var(n), v == lookup(n, env);

    Add(x: Src, y: Src, m: Nat, n: Nat,
        hx: Eval(env, x, Val::Nat(m)),
        hy: Eval(env, y, Val::Nat(n)))
        where e == Src::Add(x, y), v == Val::Nat(m + n);

    Let(e1: Src, e2: Src, v1: Val,
        hb: Eval(env, e1, v1),
        hr: Eval(Env::Cons(v1, env), e2, v))
        where e == Src::Let(e1, e2);
}
```

### 2.4 Proofs — recursive functions

A lemma is a `fn` whose return *type* is the proposition. Induction is recursion: the
induction hypothesis is a recursive call to the same function. No `theorem`, no `.ih`.

```rust
fn plus_zero(n: Nat) -> plus(n, Zero) == n {
    match n {
        Nat::Zero    => refl,
        Nat::Succ(k) => congr(Nat::Succ, plus_zero(k)),    // plus_zero(k) is the IH
    }
}

fn compile_correct(env: Env, e: Src, v: Val, h: Eval(env, e, v)) -> EvalT(env, compile(e), v) {
    match h {
        Eval::Lit(n)                  => EvalT::Lit(n),
        Eval::Var(n)                  => EvalT::Var(n),
        Eval::Add(x, y, m, n, hx, hy) => EvalT::Add(compile(x), compile(y), m, n,
                                                    compile_correct(env, x, Val::Nat(m), hx),
                                                    compile_correct(env, y, Val::Nat(n), hy)),
        Eval::Let(e1, e2, v1, hb, hr) => EvalT::let_via_beta(
                                                    compile_correct(env, e1, v1, hb),
                                                    compile_correct(Env::Cons(v1, env), e2, v, hr)),
    }
}
```

Match arms bind only the **fields**; the indices come from the scrutinee's type. The hard
dependent eliminations (the "convoy" cases) are written as ordinary helper functions whose
signature is the motive — no special `match … returns` form.

Escape hatches, all expression-level (a proof is still a function):
`refl`, `congr`, `rewrite e => …`, `calc { … }`, `by(decide)`, `by(omega)`.

### 2.5 Algebraic effects — rows on the function type

```rust
effect State { fn get() -> i64; fn set(x: i64); }

fn counter() uses State -> i64 {        // effects in the signature, like `async`
    let n = get();
    set(n + 1);
    return n;
}

let r = handle counter() with State {   // a handler reads like a match
    get()  => resume(0),
    set(x) => resume(()),               // resumable — the CEK layer already supports this
};
```

Effect rows are tracked in the type system exactly as Rust tracks `async`/`?`.

---

## 3. Lowering: how the surface reaches the kernel

| Surface | Lowers to |
|---|---|
| `enum E { … }`, `struct` | inductive datatype (`rv-kernel`) |
| `enum R(idx…) { C(flds…) where … }` | **indexed** inductive in `Prop` |
| `fn f(..) -> T { … }`, grade > 0 | runtime function → `rv-ir` → bytecode |
| `fn f(..) -> P { proof }`, grade 0 | checked `def` whose **type is `P`** (`rv-kernel`); erased |
| `match h { … }` + recursive call | recursor application + induction hypotheses |
| index-*changing* recursion (`compile_correct`) | recursor / eliminator, **not** the restricted self-call form |
| `type T = U where p`, `x: U where p` | refinement → obligation to `rv-solve`, or a subset type in the kernel |
| `refl`/`congr`/`==` | `Eq`, `Eq.refl`, `congrArg` |
| `by(decide)`/`by(omega)` | reflection / the decision procedures |
| `effect`/`uses`/`handle` | the CBPV effect layer + handler semantics |

The dependent fragment reuses everything `rv-kernel`'s existing surface already does
(dependent elaboration, recursor generation, NbE conversion, implicit/level inference); the
work is to **front it with the Rust-like syntax** and to **route grade-0 declarations to it**.

---

## 4. What this design keeps, costs, and cannot do

**Keeps** (the kernel already has it): dependent types, indexed inductive families,
recursors, universe levels, impredicative `Prop`, propositional equality, classical axioms,
reflection/decision procedures, **QTT erasure grades**, and a **CBPV algebraic-effects layer**.

**Ergonomic costs** (power preserved, surface slightly less terse): the hardest dependent
eliminations need a helper function (or an optional `match x -> Goal`); tactic automation
stays as expression-level calls; type-level functions require allowing `Type` in return
position; universe polymorphism is inferred but can leak into errors.

**Genuine kernel gaps** (no surface fixes them — tracked as kernel growth):
- **Indexed *mutual* inductives** — unsupported today (sum-encoding workaround exists).
- **Coinduction / infinite data**, **quotient types**, **higher inductive types** — absent.
- **Effects × dependent types** interaction — the two layers exist separately; combining a
  proof-returning function that also performs effects is research-grade.

---

## 5. Implementation plan (staged; each stage is usable before the next)

The strategy is **reuse, not rewrite**: `rv-kernel`'s elaborator already does the hard
dependent work, so we front it with Rust-like syntax and migrate the embedded proofs to
`.rv`, in stages.

- **Stage 0 — doc + first verified slice** *(this turn)*: this document; the kernel surface
  accepts the Rust-like proof forms (`enum` = inductive, `fn`-as-proof); a real `.rv` proof
  file is checked end-to-end through `rvc`.
- **Stage 1 — indexed `enum` + `where` variants**: GADT-style relations lower to indexed
  inductives; recursion-as-induction compiles to recursors (incl. index-changing recursion).
- **Stage 2 — migrate the proof corpus to `.rv`**: move the ~1,500 lines of embedded
  kernel-surface (stdlib, STLC, System F, CEK, the pipeline) into `.rv` files; the Rust
  crates load them from disk instead of string literals. *All Raven code lives in `.rv`.*
- **Stage 3 — refinement types + auto-discharge**: `where` on types, flow-sensitive
  refinement, `requires`/`ensures` as type-level refinements, routed to `rv-solve`.
- **Stage 4 — executable language fills the gaps** *(done)*: strings + `print`, floats, and
  closures (`|x| body` with capture, lambda-lifted) all run on the VM.
- **Stage 5 — effect rows + handlers** on the CBPV layer. *(Kernel CBPV layer present; the
  executable `effect`/`uses`/`handle` surface + runtime handler dispatch are still to do.)*
  This stage must carry effect rows in callable types and make handler coverage a type-checking
  judgement; parsing syntax alone would create another unverified runtime side path.
- **Stage 6 — unify the two backends under QTT** so a single `.rv` file mixes runtime code
  and erased proofs, split automatically by grade. *(The unified type system is demonstrated —
  the kernel both checks AND runs the modeled fragment, see `examples/proofs/unified.rv`.)*
  **The two surface parsers are now unified: `rv-syntax` is the single lexer+parser for all
  `.rv` source.** The executable fragment lowers to `rv-lower`→VM as before; the proof
  fragment is translated from the same AST into kernel commands (`rv-driver/src/unify.rs`) and
  checked by the kernel — `verify_rv`/`rvc` no longer use a second text parser, and the whole
  proof corpus + prelude verify through the one parser. (The kernel keeps an internal
  text parser only for its own unit tests, which exercise raw `Sort u`/`.{u}` universe syntax
  the language surface doesn't expose; it is no longer a language front-end.)

  **Unified driver (one invocation, both backends).** `rvc f.rv` now runs a *single*
  pipeline over one file. [`rv_syntax::classify`](../crates/rv-syntax/src/fragment.rs) splits
  each item by fragment — executable, proof, or *shared* (a data type both backends need) —
  and `rv_driver::analyze_unified` routes them: the executable fragment to the salsa pipeline
  + `rv-solve` (run on the VM), the proof fragment to the dependent kernel, merged into one
  report. `--verify` is no longer a separate pipeline — it only suppresses the run. A single
  file may carry a runtime `main` *and* an inductive theorem and verify both at once
  (`examples/mixed.rv`, `examples/shared_type.rv`).
  - *Contract routing*: a `fn`'s spec goes to whichever backend owns it — a scalar spec
    (`y != 0`, `p.v != 0`) stays on `rv-solve`; a dependent spec (`result == Nat::Succ(x)`)
    is a kernel obligation.
  - *Grade-driven erasure*: proofs erase to **nothing** by proof irrelevance (a term whose
    type is a `Prop`), so they cost zero bytes at runtime while the computational core
    survives as runtime code (`rv-kernel/src/erase.rs`; surfaced in the report's erasure
    line). This is what makes "verification is type-checking, execution runs only the code"
    literally hold.
  - *Native execution on the VM*: a proof-fragment entry point is **erased and compiled to
    bytecode** (`rv-driver/src/erased_vm.rs`) and run on `rv-vm` — the same engine as the
    executable fragment. The compiler exploits two facts: all `match`/recursion is in
    recursors (so def bodies are straight-line λ-calculus), and recursors are structural — a
    switch on the constructor tag that calls the matching minor with each field followed by its
    induction hypothesis (`sibling_recursor(motives, minors, field)`), exactly mirroring the
    kernel's ι-rule. **Mutual** groups are handled: each member's recursor is synthesized with
    all the group's motives and minors and cross-calls its siblings on recursive fields of
    sibling types. Lambdas are curried to unary VM closures, so application is one argument at
    a time and never mismatches arity. `examples/proofs/unified.rv`'s `compute = 2 + 3` runs
    to `5`, and the CEK machine's `answer = (\x. x+1) 2` (mutual Val/Env/Kont + higher-order
    closures) runs to `3` — both natively on the bytecode VM.
  - *One value model + cross-check*: native execution and the kernel's trusted reducer both
    yield the same `rv_vm::Value` (the driver asserts agreement in tests), flowing through one
    `run` channel. Only **indexed** recursors (Prop relations, which are not runtime-evaluated)
    remain on the NbE bridge as a safety net; every runtime entry in the corpus executes
    natively on the VM. The executable and dependent fragments now share one reduction engine.
- **Stage 7 — kernel growth** (indexed-mutual, coinduction) only as specific proofs demand.

The trust discipline behind all of this — model machine types/refs/effects/partiality in `.rv`
and compile down to the tiny kernel, never growing it — is written up in
[`trust-architecture.md`](trust-architecture.md), with worked, kernel-checked examples
(`machine.rv`, `heap.rv`, `word.rv`, `partial.rv`, `realization.rv`).

Soundness is preserved throughout: new surface and lowering live *outside* the trust base, so
any bug is a rejected program, never an unsound "verified".
