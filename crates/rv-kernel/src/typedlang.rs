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
pub const PRELUDE: &str = r#"
    -- Logical scaffolding.
    inductive True  : Prop | intro : True
    inductive False : Prop
    inductive Eq.{u} (A : Sort u) (a : A) : A -> Prop | refl : Eq A a a

    def Eq.subst.{u} (A : Sort u) (P : A -> Prop) (a : A) (b : A) (h : Eq A a b) (pa : P a)
      : P b := Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => P x) pa b h
    def Eq.symm.{u} (A : Sort u) (a : A) (b : A) (h : Eq A a b) : Eq A b a :=
      Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => Eq A x a) (Eq.refl.{u} A a) b h
    def Eq.trans.{u} (A : Sort u) (a : A) (b : A) (c : A) (h1 : Eq A a b) (h2 : Eq A b c)
      : Eq A a c := Eq.subst.{u} A (fun (x : A) => Eq A a x) b c h2 h1

    -- Booleans and conjunction-as-computation.
    inductive Bool : Type | false : Bool | true : Bool

    fn and(x: Bool, y: Bool) -> Bool {
        match x { | Bool.true => y | Bool.false => Bool.false }
    }

    -- Bool no-confusion: false and true are distinct (the kernel proves this via the
    -- recursor; we need it to discharge the impossible branches of the soundness proof).
    def isFalseProp (b : Bool) : Prop := Bool.rec.{1} (fun (_ : Bool) => Prop) True False b
    def ff_ne_tt (h : Eq.{1} Bool Bool.false Bool.true) : False :=
      Eq.rec.{1, 0} Bool Bool.false
        (fun (b : Bool) (_ : Eq.{1} Bool Bool.false b) => isFalseProp b)
        True.intro Bool.true h

    -- And-elimination, both projections (used to take apart the checker's conjunctions).
    def and_left (x : Bool) (y : Bool) : Eq.{1} Bool (and x y) Bool.true -> Eq.{1} Bool x Bool.true :=
      match x {
        | Bool.true  => fun (h : Eq.{1} Bool (and Bool.true y) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Bool.false => fun (h : Eq.{1} Bool (and Bool.false y) Bool.true) => h
      }
    def and_right (x : Bool) (y : Bool) : Eq.{1} Bool (and x y) Bool.true -> Eq.{1} Bool y Bool.true :=
      match x {
        | Bool.true  => fun (h : Eq.{1} Bool (and Bool.true y) Bool.true) => h
        | Bool.false => fun (h : Eq.{1} Bool (and Bool.false y) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Bool y Bool.true) (ff_ne_tt h)
      }
    -- And-introduction (used by completeness to assemble the checker's conjunction).
    def and_true (x : Bool) (y : Bool)
      : Eq.{1} Bool x Bool.true -> Eq.{1} Bool y Bool.true -> Eq.{1} Bool (and x y) Bool.true :=
      match x {
        | Bool.true  => fun (hx : Eq.{1} Bool Bool.true Bool.true)
                            (hy : Eq.{1} Bool y Bool.true) => hy
        | Bool.false => fun (hx : Eq.{1} Bool Bool.false Bool.true)
                            (hy : Eq.{1} Bool y Bool.true) => hx
      }

    -- Naturals (literals for the object language).
    inductive Nat : Type | zero : Nat | succ : Nat -> Nat

    -- The object-language types and their decidable equality.
    inductive Ty : Type | tnat : Ty | tbool : Ty

    def isTnatProp (t : Ty) : Prop := Ty.rec.{1} (fun (_ : Ty) => Prop) True False t
    def tnat_ne_tbool (h : Eq.{1} Ty Ty.tnat Ty.tbool) : False :=
      Eq.rec.{1, 0} Ty Ty.tnat
        (fun (t : Ty) (_ : Eq.{1} Ty Ty.tnat t) => isTnatProp t)
        True.intro Ty.tbool h
    def isTboolProp (t : Ty) : Prop := Ty.rec.{1} (fun (_ : Ty) => Prop) False True t
    def tbool_ne_tnat (h : Eq.{1} Ty Ty.tbool Ty.tnat) : False :=
      Eq.rec.{1, 0} Ty Ty.tbool
        (fun (t : Ty) (_ : Eq.{1} Ty Ty.tbool t) => isTboolProp t)
        True.intro Ty.tnat h

    fn tyeq(x: Ty, y: Ty) -> Bool {
        match x {
          | Ty.tnat  => match y { | Ty.tnat => Bool.true  | Ty.tbool => Bool.false }
          | Ty.tbool => match y { | Ty.tnat => Bool.false | Ty.tbool => Bool.true  }
        }
    }

    -- `tyeq` is a sound decider for `Ty` equality: tyeq x y = true → x = y. The two
    -- mismatched cases are impossible (tyeq computes to false), discharged by no-confusion.
    def tyeq_sound (x : Ty) (y : Ty) : Eq.{1} Bool (tyeq x y) Bool.true -> Eq.{1} Ty x y :=
      match x {
        | Ty.tnat => match y {
            | Ty.tnat  => fun (h : Eq.{1} Bool (tyeq Ty.tnat Ty.tnat) Bool.true) =>
                Eq.refl.{1} Ty Ty.tnat
            | Ty.tbool => fun (h : Eq.{1} Bool (tyeq Ty.tnat Ty.tbool) Bool.true) =>
                False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tnat Ty.tbool) (ff_ne_tt h)
          }
        | Ty.tbool => match y {
            | Ty.tnat  => fun (h : Eq.{1} Bool (tyeq Ty.tbool Ty.tnat) Bool.true) =>
                False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tbool Ty.tnat) (ff_ne_tt h)
            | Ty.tbool => fun (h : Eq.{1} Bool (tyeq Ty.tbool Ty.tbool) Bool.true) =>
                Eq.refl.{1} Ty Ty.tbool
          }
      }

    -- Converse fact for completeness: if a type *is* `tnat`, the decider says so.
    def tyeq_true_of (t : Ty) (h : Eq.{1} Ty t Ty.tnat) : Eq.{1} Bool (tyeq t Ty.tnat) Bool.true :=
      Eq.subst.{1} Ty (fun (s : Ty) => Eq.{1} Bool (tyeq s Ty.tnat) Bool.true) Ty.tnat t
        (Eq.symm.{1} Ty t Ty.tnat h) (Eq.refl.{1} Bool Bool.true)
"#;

/// The object language: an `Exp` AST, the typing **relation** `HasTy`, and the type
/// **checker** (`synth` + `ok`) — all in surface Raven, on top of [`PRELUDE`].
pub const LANG: &str = r#"
    -- A tiny typed expression language: numeric and boolean literals, and addition
    -- (which requires both operands to be numeric). `eadd` is the one former that can
    -- be ill-typed — addition of a boolean is a type error.
    inductive Exp : Type
      | enat  : Nat -> Exp
      | ebool : Bool -> Exp
      | eadd  : Exp -> Exp -> Exp

    -- The typing RELATION — the specification of "well typed", as an inductive judgment.
    -- `HasTy e T` is inhabited exactly when `e` has type `T`.
    inductive HasTy : Exp -> Ty -> Prop
      | tnat  : (n : Nat)  -> HasTy (Exp.enat n) Ty.tnat
      | tbool : (b : Bool) -> HasTy (Exp.ebool b) Ty.tbool
      | tadd  : (a : Exp) -> (b : Exp)
                  -> HasTy a Ty.tnat -> HasTy b Ty.tnat
                  -> HasTy (Exp.eadd a b) Ty.tnat

    -- The CHECKER, part 1: the inferred type (junk-free on well-typed terms; on an
    -- ill-typed `eadd` it still says `tnat`, but `ok` below will reject it).
    fn synth(e: Exp) -> Ty {
        match e {
          | Exp.enat(n)    => Ty.tnat
          | Exp.ebool(b)   => Ty.tbool
          | Exp.eadd(a, b) => Ty.tnat
        }
    }

    -- The CHECKER, part 2: the well-typedness decision. An `eadd` is well typed iff both
    -- subterms are well typed AND both synthesize `tnat`.
    fn ok(e: Exp) -> Bool {
        match e {
          | Exp.enat(n)    => Bool.true
          | Exp.ebool(b)   => Bool.true
          | Exp.eadd(a, b) =>
              and(and(ok(a), ok(b)),
                  and(tyeq(synth(a), Ty.tnat), tyeq(synth(b), Ty.tnat)))
        }
    }

    -- THE SOUNDNESS THEOREM, proved in Raven by structural recursion on `e`:
    --   ok e = true  →  HasTy e (synth e).
    -- The checker's verdict implies a real typing derivation in the independent relation.
    -- Each `eadd` step takes the conjunction `ok` produced apart with `and_left`/
    -- `and_right`, turns the `tyeq … = true` facts into type equalities with `tyeq_sound`,
    -- applies the induction hypotheses (`ok_sound(a)`, `ok_sound(b)`) to type the
    -- subterms, and transports them to `tnat` with `Eq.subst` to build `HasTy.tadd`.
    fn ok_sound(e: Exp) -> (Eq.{1} Bool (ok(e)) Bool.true -> HasTy e (synth(e))) {
        match e {
          | Exp.enat(n)  => fun (h : Eq.{1} Bool (ok(Exp.enat(n))) Bool.true) => HasTy.tnat n
          | Exp.ebool(b) => fun (h : Eq.{1} Bool (ok(Exp.ebool(b))) Bool.true) => HasTy.tbool b
          | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (ok(Exp.eadd(a, b))) Bool.true) =>
              HasTy.tadd a b
                (Eq.subst.{1} Ty (fun (T : Ty) => HasTy a T) (synth(a)) Ty.tnat
                   (tyeq_sound (synth(a)) Ty.tnat
                      (and_left (tyeq(synth(a), Ty.tnat)) (tyeq(synth(b), Ty.tnat))
                         (and_right (and(ok(a), ok(b)))
                                    (and(tyeq(synth(a), Ty.tnat), tyeq(synth(b), Ty.tnat))) h)))
                   (ok_sound(a)
                      (and_left (ok(a)) (ok(b))
                         (and_left (and(ok(a), ok(b)))
                                   (and(tyeq(synth(a), Ty.tnat), tyeq(synth(b), Ty.tnat))) h))))
                (Eq.subst.{1} Ty (fun (T : Ty) => HasTy b T) (synth(b)) Ty.tnat
                   (tyeq_sound (synth(b)) Ty.tnat
                      (and_right (tyeq(synth(a), Ty.tnat)) (tyeq(synth(b), Ty.tnat))
                         (and_right (and(ok(a), ok(b)))
                                    (and(tyeq(synth(a), Ty.tnat), tyeq(synth(b), Ty.tnat))) h)))
                   (ok_sound(b)
                      (and_right (ok(a)) (ok(b))
                         (and_left (and(ok(a), ok(b)))
                                   (and(tyeq(synth(a), Ty.tnat), tyeq(synth(b), Ty.tnat))) h))))
        }
    }

    -- COMPLETENESS, part 1: the checker's inferred type AGREES with the relation. Proved
    -- by induction on the typing DERIVATION (matching on `d`): every constructor pins the
    -- type, so each case is `refl`.
    def synth_complete (e : Exp) (T : Ty) (d : HasTy e T) : Eq.{1} Ty (synth(e)) T :=
      match d {
        | HasTy.tnat(n)            => Eq.refl.{1} Ty Ty.tnat
        | HasTy.tbool(b)           => Eq.refl.{1} Ty Ty.tbool
        | HasTy.tadd(a, b, da, db) => Eq.refl.{1} Ty Ty.tnat
      }

    -- COMPLETENESS, part 2: anything the relation accepts, the checker accepts —
    --   HasTy e T → ok e = true,
    -- by induction on the derivation. The `tadd` case reassembles the conjunction `ok`
    -- computes from the induction hypotheses (`da.rec`, `db.rec` give `ok a`/`ok b = true`)
    -- and `synth_complete` (each subterm really does synthesize `tnat`).
    def ok_complete (e : Exp) (T : Ty) (d : HasTy e T) : Eq.{1} Bool (ok(e)) Bool.true :=
      match d {
        | HasTy.tnat(n)  => Eq.refl.{1} Bool Bool.true
        | HasTy.tbool(b) => Eq.refl.{1} Bool Bool.true
        | HasTy.tadd(a, b, da, db) =>
            and_true (and(ok(a), ok(b)))
                     (and(tyeq(synth(a), Ty.tnat), tyeq(synth(b), Ty.tnat)))
              (and_true (ok(a)) (ok(b)) da.rec db.rec)
              (and_true (tyeq(synth(a), Ty.tnat)) (tyeq(synth(b), Ty.tnat))
                 (tyeq_true_of (synth(a)) (synth_complete a Ty.tnat da))
                 (tyeq_true_of (synth(b)) (synth_complete b Ty.tnat db)))
      }

    -- The headline completeness statement, contrapositive form: a term the checker
    -- REJECTS (`ok e = false`) is genuinely untypable — it has NO typing in the relation,
    -- for any type. (`ok e = true` from `ok_complete` would contradict `ok e = false`.)
    def ok_false_not_welltyped (e : Exp) (T : Ty)
        (hf : Eq.{1} Bool (ok(e)) Bool.false) (d : HasTy e T) : False :=
      ff_ne_tt (Eq.trans.{1} Bool Bool.false (ok(e)) Bool.true
                  (Eq.symm.{1} Bool (ok(e)) Bool.false hf)
                  (ok_complete e T d))
"#;

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
