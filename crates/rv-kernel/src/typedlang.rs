//! **A verified type checker, in Raven** — the first pipeline analysis whose *yes* is
//! backed by a machine-checked soundness theorem against an independent specification.
//!
//! The previous brick ([`crate::objlang`]) proved an *equational* metatheorem about a
//! pass (`eval (opt e) = eval e`). This one takes the decisive next step: it separates
//! **specification** from **implementation** and proves they agree.
//!
//!  * The *specification* is a typing **relation** `HasTy : Exp → Ty → Prop` — an
//!    inductively-defined judgment `e : T`, the ground truth for "well typed".
//!  * The *implementation* is a **type checker** written as ordinary Raven functions:
//!    `synth : Exp → Ty` (the inferred type) and `ok : Exp → Bool` (the decision).
//!  * The bridge is the **soundness theorem**
//!    ```text
//!    ok_sound : ∀ e, ok e = true → HasTy e (synth e)
//!    ```
//!    proved *in Raven* by structural recursion on `e` and checked by the kernel.
//!
//! This is the shape the kernel-and-core endgame is built from: a real analysis (here a
//! type checker; later the borrow checker, the trait solver) lives as verified Raven over
//! inductively-defined syntax, with a soundness theorem the kernel checks — so the
//! analysis's verdict is *trustworthy by proof*, not by trusting hand-written Rust. And
//! because the checker **computes**, soundness is usable by **reflection**: for any
//! concrete program, `ok e` reduces to `true`, the certificate `ok e = true` is just
//! `refl`, and `ok_sound e refl` *produces the typing derivation by running the checker*.
//! An ill-typed program reduces `ok e` to `false`, so no `refl` certificate exists and no
//! derivation can be forged — soundness in both directions.

use crate::verify::Session;

/// The self-contained prelude this module needs: logical scaffolding (`True`/`False`/
/// `Eq` with `subst`), `Bool` with `and` and its no-confusion, `Nat`, the object types
/// `Ty`, and the type-equality decider `tyeq` with its soundness no-confusion lemmas.
pub const PRELUDE: &str = include_str!("raven/typedlang_prelude.rvk");

/// The object language: an `Exp` AST, the typing **relation** `HasTy`, and the type
/// **checker** (`synth` + `ok`) — all in surface Raven, on top of [`PRELUDE`].
pub const LANG: &str = include_str!("raven/typedlang_lang.rvk");

/// A session with the prelude and the typed object language + checker + soundness proof
/// all loaded and kernel-checked.
pub fn session() -> Result<Session, String> {
    let mut s = Session::new();
    s.run(PRELUDE)?;
    s.run(LANG)?;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Everything — including the **soundness theorem** `ok_sound` — elaborates and is
    /// checked by the kernel on the way in.
    #[test]
    fn lang_and_soundness_check() {
        let s = session().expect("prelude + language + soundness proof should check");
        for n in ["Exp", "Ty", "HasTy", "synth", "ok", "tyeq_sound", "ok_sound"] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// The checker **computes**: `synth` infers `tnat` for `2 + 3`, and `ok` accepts it.
    #[test]
    fn checker_accepts_well_typed() {
        let mut s = session().unwrap();
        s.run(
            "def good : Exp := \
               Exp.eadd(Exp.enat(Nat.succ(Nat.succ(Nat.zero))), \
                        Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))",
        )
        .unwrap();
        s.run("def good_ty : Ty := synth(good)").unwrap();
        s.run("def good_ok : Bool := ok(good)").unwrap();
        assert_eq!(s.run_entry("good_ty").unwrap(), "Ty.tnat");
        assert_eq!(s.run_entry("good_ok").unwrap(), "Bool.true");
    }

    /// The checker **rejects** ill-typed terms: `true + 0` adds a boolean, so `ok` is
    /// `false`.
    #[test]
    fn checker_rejects_ill_typed() {
        let mut s = session().unwrap();
        s.run("def bad : Exp := Exp.eadd(Exp.ebool(Bool.true), Exp.enat(Nat.zero))").unwrap();
        s.run("def bad_ok : Bool := ok(bad)").unwrap();
        assert_eq!(s.run_entry("bad_ok").unwrap(), "Bool.false");
    }

    /// **Type checking by reflection.** For a concrete well-typed program the checker
    /// reduces `ok e` to `true`, so the certificate is just `refl`, and `ok_sound e refl`
    /// *produces the typing derivation by running the checker* — a kernel-checked
    /// `HasTy e (synth e)` with no hand proof.
    #[test]
    fn reflective_typing_derivation() {
        let mut s = session().unwrap();
        s.run(
            "def derivation : HasTy (Exp.eadd (Exp.enat Nat.zero) (Exp.enat Nat.zero)) Ty.tnat := \
               ok_sound (Exp.eadd (Exp.enat Nat.zero) (Exp.enat Nat.zero)) \
                 (Eq.refl.{1} Bool Bool.true)",
        )
        .expect("reflective derivation should check");
        assert!(s.k.env().contains("derivation"));
    }

    /// **Completeness checks.** The agreement theorems `synth_complete` (the checker's
    /// inferred type matches the relation) and `ok_complete` (the checker accepts every
    /// well-typed term) elaborate and are kernel-checked.
    #[test]
    fn completeness_theorems_check() {
        let s = session().unwrap();
        for n in ["synth_complete", "ok_complete", "ok_false_not_welltyped"] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// **Rejection is decisive.** Because `ok bad` reduces to `false`, the completeness
    /// theorem gives a *refutation function* `HasTy bad T → False`: the ill-typed term has
    /// no typing in the relation, for any `T`. The certificate is `refl : ok bad = false`,
    /// which type-checks only because the checker actually computes `false`.
    #[test]
    fn rejected_term_is_genuinely_untypable() {
        let mut s = session().unwrap();
        s.run("def bad : Exp := Exp.eadd(Exp.ebool(Bool.true), Exp.enat(Nat.zero))").unwrap();
        s.run(
            "def bad_untypable (T : Ty) : HasTy bad T -> False := \
               ok_false_not_welltyped bad T (Eq.refl.{1} Bool Bool.false)",
        )
        .expect("a rejected term must be provably untypable");
        assert!(s.k.env().contains("bad_untypable"));
    }

    /// **Soundness has teeth.** An ill-typed program cannot be certified: `ok bad` reduces
    /// to `false`, so the `refl : ok bad = true` certificate does not type-check and the
    /// derivation is rejected by the kernel. No false typing can be forged.
    #[test]
    fn ill_typed_cannot_be_certified() {
        let mut s = session().unwrap();
        let r = s.run(
            "def forged : HasTy (Exp.eadd (Exp.ebool Bool.true) (Exp.enat Nat.zero)) Ty.tnat := \
               ok_sound (Exp.eadd (Exp.ebool Bool.true) (Exp.enat Nat.zero)) \
                 (Eq.refl.{1} Bool Bool.true)",
        );
        assert!(r.is_err(), "an ill-typed term must not be certifiable by reflection");
    }
}
