//! A first brick of **the pipeline written in verified Raven**: a tiny object language
//! formalized as an inductive, a *pass* over it (an evaluator) written with ordinary
//! structural recursion, and **proven equations** about that pass — all elaborated and
//! checked by the kernel through [`Session`], like any user program.
//!
//! This is the seed of the kernel-and-core endgame: the real compiler's analyses (the
//! borrow checker, the type checker, the solver) are meant to live *here* — as Raven
//! functions over inductively-defined syntax, with soundness theorems the kernel checks,
//! run by reflection — rather than as trusted Rust. This module is the smallest honest
//! instance of that shape: an AST, a verified pass, and machine-checked metatheory.
//!
//! `Expr ::= lit n | add e e | mul e e`, and `eval : Expr → Nat` is the pass. The
//! evaluator recurses **by name** (`eval(a)`, `eval(b)`), which the structural-recursion
//! compiler turns into the recursor's induction hypotheses. The proved facts
//! (`eval (add a b) = eval a + eval b`, `eval (lit n) = n`) are the evaluator's defining
//! equations — its *correctness contract* — discharged automatically by computation.

use crate::stdlib;
use crate::verify::Session;

/// The object language, its evaluator, and an optimization pass — in surface Raven (on
/// top of the [`stdlib`] `Nat`/`add`/`mul`).
pub const OBJLANG: &str = r#"
    -- A tiny arithmetic expression language. `wrap` is a semantically-transparent
    -- node (think: a redundant annotation / no-op the compiler should remove).
    inductive Expr : Type
      | lit  : Nat -> Expr
      | add  : Expr -> Expr -> Expr
      | mul  : Expr -> Expr -> Expr
      | wrap : Expr -> Expr

    -- The evaluation pass (semantics) — structural recursion written by name.
    fn eval(e: Expr) -> Nat {
        match e {
          | Expr.lit(n)    => n
          | Expr.add(a, b) => add(eval(a), eval(b))
          | Expr.mul(a, b) => mul(eval(a), eval(b))
          | Expr.wrap(a)   => eval(a)
        }
    }

    -- An optimization pass: strip `wrap` nodes (dead-node elimination), recursing
    -- structurally elsewhere. This genuinely changes the term — `opt` is not the
    -- identity — yet must preserve the evaluation semantics.
    fn opt(e: Expr) -> Expr {
        match e {
          | Expr.lit(n)    => Expr.lit(n)
          | Expr.add(a, b) => Expr.add(opt(a), opt(b))
          | Expr.mul(a, b) => Expr.mul(opt(a), opt(b))
          | Expr.wrap(a)   => opt(a)
        }
    }

    -- Constant folding: a `+` of two literals collapses to one literal. Uses NESTED
    -- patterns (a constructor whose children are themselves constructors) with a
    -- fall-through arm — and recurses by name.
    fn cfold(e: Expr) -> Expr {
        match e {
          | Expr.add(Expr.lit(m), Expr.lit(n)) => Expr.lit(add(m, n))
          | Expr.add(a, b)                     => Expr.add(cfold(a), cfold(b))
          | Expr.lit(n)                        => Expr.lit(n)
          | Expr.mul(a, b)                     => Expr.mul(cfold(a), cfold(b))
          | Expr.wrap(a)                       => cfold(a)
        }
    }
"#;

/// A session with the standard library and the object language + evaluator loaded.
pub fn session() -> Result<Session, String> {
    let mut s = Session::new();
    stdlib::load(&mut s)?;
    s.run(OBJLANG)?;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pass **runs**: `eval (add (lit 2) (mul (lit 3) (lit 4))) = 2 + 3·4 = 14`.
    #[test]
    fn evaluator_computes() {
        let mut s = session().unwrap();
        s.run(
            "def e0 : Expr := \
               Expr.add(Expr.lit(Nat.succ(Nat.succ(Nat.zero))), \
                        Expr.mul(Expr.lit(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))), \
                                 Expr.lit(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))))",
        )
        .unwrap();
        s.run("def v0 : Nat := eval(e0)").unwrap();
        assert_eq!(s.run_entry("v0").unwrap(), "14");
    }

    /// **Proven metatheory of the pass.** Its defining equations — checked by the kernel,
    /// discharged automatically by ι-computation of the recursor:
    ///   * `eval (lit n)   = n`
    ///   * `eval (add a b) = eval a + eval b`
    ///   * `eval (mul a b) = eval a · eval b`
    /// These are the evaluator's correctness contract, machine-verified for *all* inputs.
    #[test]
    fn evaluator_equations_are_verified() {
        let mut s = session().unwrap();
        s.run("fn eval_lit(n: Nat) -> Nat { ensures(result == n); eval(Expr.lit(n)) }").unwrap();
        s.run(
            "fn eval_add(a: Expr, b: Expr) -> Nat { \
               ensures(result == add(eval(a), eval(b))); \
               eval(Expr.add(a, b)) }",
        )
        .unwrap();
        s.run(
            "fn eval_mul(a: Expr, b: Expr) -> Nat { \
               ensures(result == mul(eval(a), eval(b))); \
               eval(Expr.mul(a, b)) }",
        )
        .unwrap();
        assert!(s.verified("eval_lit"), "eval (lit n) = n");
        assert!(s.verified("eval_add"), "eval (add a b) = eval a + eval b");
        assert!(s.verified("eval_mul"), "eval (mul a b) = eval a · eval b");
        assert!(s.all_verified());
    }

    /// `opt` genuinely transforms the term: `opt (wrap (lit 5))` strips the wrapper to
    /// `lit 5` (and both evaluate to `5`).
    #[test]
    fn optimizer_strips_wrappers() {
        let mut s = session().unwrap();
        s.run("def w : Expr := opt(Expr.wrap(Expr.lit(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))").unwrap();
        assert_eq!(s.run_entry("w").unwrap(), "Expr.lit 5", "the wrap node is removed");
    }

    /// **Constant folding with nested patterns + recursion.** `cfold` collapses `2 + 3`
    /// to the literal `5` (matching `add(lit(m), lit(n))` — a nested pattern — and folding
    /// the inner literals), recursing into other nodes. `add(lit 2, lit 3)` ⇒ `lit 5`.
    #[test]
    fn constant_folding_nested_patterns() {
        let mut s = session().unwrap();
        s.run(
            "def folded : Expr := \
               cfold(Expr.add(Expr.lit(Nat.succ(Nat.succ(Nat.zero))), \
                              Expr.lit(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))",
        )
        .unwrap();
        assert_eq!(s.run_entry("folded").unwrap(), "Expr.lit 5", "2 + 3 folds to the literal 5");
    }

    /// **The verified-compiler theorem, in Raven.** The optimization preserves the
    /// program's meaning — `∀ e, eval (opt e) = eval e` — proved **automatically** by the
    /// induction+rewrite prover: induction on `e`, each `add`/`mul` case closed by
    /// rewriting with the two sub-expression hypotheses, the `wrap` case by the
    /// hypothesis directly. A machine-checked semantics-preservation proof for a real
    /// pass, with no hand proof.
    #[test]
    fn optimizer_preserves_semantics() {
        let mut s = session().unwrap();
        s.run("fn opt_sound(e: Expr) -> Nat { ensures(eval(opt(e)) == eval(e)); eval(e) }")
            .unwrap();
        assert!(
            s.verified("opt_sound"),
            "eval (opt e) = eval e should auto-prove by induction + rewrite"
        );
    }
}
