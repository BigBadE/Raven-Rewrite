# Raven trust architecture — keep the kernel tiny, model everything else

This note records the load-bearing design decision behind Raven's unification: **the kernel
is a minimal logical core, and everything machine-shaped — integers, references, effects,
even non-termination — is *modeled in Raven* and compiled down to the primitives the kernel
already understands.** The kernel does not grow to accommodate the runtime language. It is
the companion to [`raven-language.md`](raven-language.md), which describes the surface.

---

## 1. The principle

The kernel (`rv-kernel`) is a dependent type theory: inductive types, recursors, Π/Σ,
universes, propositional equality, definitional reduction (NbE). That is the entire trusted
logical vocabulary. A feature is added to the *language* by **defining** it in `.rv` in terms
of that vocabulary — never by teaching the kernel a new primitive.

This is exactly how the proof fragment already works: the kernel has never heard of `match`,
generics `<A>`, `calc`, or `rewrite`. The elaborator (outside the trust base) compiles them to
recursor applications and `Eq`. Extending the same discipline to the *runtime* fragment is
more elaboration, not kernel surgery.

Concretely demonstrated in [`examples/proofs/machine.rv`](../examples/proofs/machine.rv):
booleans, a 1-bit machine word whose **wrapping** adder is *proved equal to mod-2 arithmetic*,
and signed integers with a proved negation involution — all ordinary `enum`/`fn`, zero kernel
changes.

## 2. Encoding strategy, per feature

| Surface feature | Modeled in Raven as | Kernel needs |
|---|---|---|
| `bool` | `enum Bool { false, true }` + `fn` ops | nothing (inductives) |
| `Nat`, unbounded `Int` | `enum Nat`, `enum Int { Pos(Nat), NegSucc(Nat) }` + proved ring laws | nothing |
| `iN`/`uN` machine words | a width-indexed model + reduction mod `2^N`; **overflow is a definition**, proved against the modular spec | nothing |
| references / `&mut` | a heap model (finite map) + points-to propositions; the borrow discipline emits a checkable certificate (`rv-borrowck`, outside the trust base) | nothing |
| algebraic effects | a free-monad / effect-signature encoding over inductive types; handlers are folds | nothing (the legacy in-kernel CBPV layer can become a library) |
| **partiality / non-termination** | a *type*, not an effect-in-the-kernel: `Partial<A> ≈ (fuel: Nat) -> Option<A>` (or an encoded `Delay`). A diverging computation has type `Partial<A>`, **not** `A` | nothing — misuse (`Partial<Empty>` used as `Empty`) is a **plain type error the existing kernel catches** |

The partiality row is the subtle one and the answer to "how do we stay Turing-complete without
admitting `fn bottom() -> Empty { bottom() }`". Because a partial value lives in a *different
type*, the one-way membrane (free to construct, impossible to eliminate into the pure logic
without a termination proof) is enforced by ordinary type-checking. The kernel needs no
`Div` effect; the type distinction does the work.

## 3. The two irreducible residues (neither is kernel growth)

**(a) Realization trust at the codegen boundary.** The modeled `wadd` is a slow logical
definition; at runtime a *native machine `add`* executes. Something must connect "what I proved
about the model" to "what the hardware does." That link is an **explicit, small, auditable
assumption** (`native_addᵢ₆₄` realizes `model_add`), or — better, later — a verified compiler
(CompCert-style). It lives at the `rv-codegen`/VM boundary, **outside the kernel**, and it is
unavoidable in *every* verified system (Lean trusts `@[extern]`/GMP; Coq trusts extraction +
OCaml; CompCert shrinks it by proving the compiler). The trust base is therefore
`rv-kernel` + a *named list of realization axioms* — not a fat kernel.

**(b) Genuinely new logical primitives with no sound encoding.** A few things cannot be defined
away and, *only when a specific proof demands one and no encoding suffices*, justify growing the
kernel: **quotient types**, **true coinduction**, **higher inductive types**, **indexed-mutual
inductives**. Several have encodings that dodge the need (coinduction via fuel/functions,
quotients via setoids), at an ergonomic cost. Kernel growth is thus rare and demand-driven, not
a standing requirement for ints/refs/effects/partiality.

## 4. Where the soundness lines fall

- **Kernel-checked proofs**: sound, full stop. The kernel re-derives and re-checks every type;
  it has no `bool`/`i64`-style leniency (it rejects `Bool` where `Nat` is expected).
- **The runtime language**: its convenience checker (`rv-infer`) is *not* the kernel and is
  *not* in the trust base. The end goal is to check the runtime fragment against the **models**
  above, so the kernel — not `rv-infer` — is what types it. Until then, `rv-infer` must at
  least enforce primitive types itself (its current `bool`/`i64` leniency is a bug to fix, not
  a design choice).
- **Realization**: trusted, explicit, small (residue (a)).

## 5. Status

- ✅ Rust frontend removed — one source language, `.rv`.
- ✅ Modeling pattern demonstrated and kernel-checked (`machine.rv`): no kernel growth.
- ✅ Generic `enum` parameters, proved-once generic stdlib, reflection — the proof surface.
- ⏳ Frontier: model `iN`/`uN` and the heap fully; route the runtime fragment's type-checking
  through the kernel + models (Stage 6 QTT unification); enumerate the realization axioms as a
  checked list; add the `Partial<A>` library.

The discipline in one line: **grow the realization layer and the `.rv` libraries, never the
kernel.**
