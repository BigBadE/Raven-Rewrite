//! **A verified type checker for a simply-typed λ-calculus** — the type checker of
//! [`crate::typedlang`] grown all the way up to **function types, λ-abstraction, and
//! application**, on top of de Bruijn variables, a `let` binder, and a typing context.
//!
//! This is the real thing: an analysis (a type checker) over a language with binders and
//! a structured (recursive) type grammar, with a machine-checked soundness theorem against
//! an independent typing relation — exactly the shape the kernel-and-core endgame uses for
//! the borrow checker and trait solver. Everything is verified Raven checked by the kernel:
//!
//!  * **Spec** — the typing relation `HasTy : Ctx → Exp → Ty → Prop` (with `tlam`/`tapp`
//!    for functions) and the de Bruijn lookup relation `Lookup : Ctx → Nat → Ty → Prop`.
//!  * **Implementation** — the checker as curried, context-threading Raven functions
//!    `synth : Exp → Ctx → Ty` and `ok : Exp → Ctx → Bool`, with a **recursive** type
//!    decider `tyeq` (arrows compared structurally) and arrow destructors
//!    `isArrow`/`domOf`/`codOf`.
//!  * **Bridge** — `tyeq_sound` (structural induction on the recursive type), the variable
//!    lemma `lookup_sound`, arrow inversion `arrow_inv`, and the soundness theorem
//!    ```text
//!    ok_sound : ∀ e Γ, ok e Γ = true → HasTy Γ e (synth e Γ),
//!    ```
//!    whose `eapp` case is the heart of it: it inverts the synthesized function type to an
//!    arrow, rewrites its domain to the argument's type, and applies `tapp`.

use crate::verify::Session;

/// Logic + booleans + naturals + the (recursive) object types with a decidable equality
/// and arrow destructors + the typing context with lookup/scope and the `Lookup` relation.
pub const PRELUDE: &str = r#"
    -- Logic.
    inductive True  : Prop | intro : True
    inductive False : Prop
    inductive Eq.{u} (A : Sort u) (a : A) : A -> Prop | refl : Eq A a a
    def Eq.subst.{u} (A : Sort u) (P : A -> Prop) (a : A) (b : A) (h : Eq A a b) (pa : P a)
      : P b := Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => P x) pa b h
    def Eq.symm.{u} (A : Sort u) (a : A) (b : A) (h : Eq A a b) : Eq A b a :=
      Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => Eq A x a) (Eq.refl.{u} A a) b h
    def Eq.trans.{u} (A : Sort u) (a : A) (b : A) (c : A) (h1 : Eq A a b) (h2 : Eq A b c)
      : Eq A a c := Eq.subst.{u} A (fun (x : A) => Eq A a x) b c h2 h1

    -- Booleans + conjunction-as-computation + no-confusion + And-elim.
    inductive Bool : Type | false : Bool | true : Bool
    fn and(x: Bool, y: Bool) -> Bool {
        match x { | Bool.true => y | Bool.false => Bool.false }
    }
    def isFalseProp (b : Bool) : Prop := Bool.rec.{1} (fun (_ : Bool) => Prop) True False b
    def ff_ne_tt (h : Eq.{1} Bool Bool.false Bool.true) : False :=
      Eq.rec.{1, 0} Bool Bool.false
        (fun (b : Bool) (_ : Eq.{1} Bool Bool.false b) => isFalseProp b)
        True.intro Bool.true h
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
    def and_true (x : Bool) (y : Bool)
      : Eq.{1} Bool x Bool.true -> Eq.{1} Bool y Bool.true -> Eq.{1} Bool (and x y) Bool.true :=
      match x {
        | Bool.true  => fun (hx : Eq.{1} Bool Bool.true Bool.true) (hy : Eq.{1} Bool y Bool.true) => hy
        | Bool.false => fun (hx : Eq.{1} Bool Bool.false Bool.true) (hy : Eq.{1} Bool y Bool.true) => hx
      }

    -- Naturals (de Bruijn indices and literals).
    inductive Nat : Type | zero : Nat | succ : Nat -> Nat

    -- The object types: now RECURSIVE — base types plus a function arrow.
    inductive Ty : Type
      | tnat   : Ty
      | tbool  : Ty
      | tarrow : Ty -> Ty -> Ty
      | tprod  : Ty -> Ty -> Ty
      | tsum   : Ty -> Ty -> Ty

    -- Arrow destructors (junk = tnat on a non-arrow) and the arrow test.
    fn isArrow(t: Ty) -> Bool {
        match t { | Ty.tnat => Bool.false | Ty.tbool => Bool.false | Ty.tarrow(d, c) => Bool.true | Ty.tprod(a, b) => Bool.false | Ty.tsum(a, b) => Bool.false }
    }
    fn domOf(t: Ty) -> Ty {
        match t { | Ty.tnat => Ty.tnat | Ty.tbool => Ty.tnat | Ty.tarrow(d, c) => d | Ty.tprod(a, b) => Ty.tnat | Ty.tsum(a, b) => Ty.tnat }
    }
    fn codOf(t: Ty) -> Ty {
        match t { | Ty.tnat => Ty.tnat | Ty.tbool => Ty.tnat | Ty.tarrow(d, c) => c | Ty.tprod(a, b) => Ty.tnat | Ty.tsum(a, b) => Ty.tnat }
    }
    -- Product destructors (junk = tnat on a non-product) and the product test.
    fn isProd(t: Ty) -> Bool {
        match t { | Ty.tnat => Bool.false | Ty.tbool => Bool.false | Ty.tarrow(d, c) => Bool.false | Ty.tprod(a, b) => Bool.true | Ty.tsum(a, b) => Bool.false }
    }
    fn fstTy(t: Ty) -> Ty {
        match t { | Ty.tnat => Ty.tnat | Ty.tbool => Ty.tnat | Ty.tarrow(d, c) => Ty.tnat | Ty.tprod(a, b) => a | Ty.tsum(a, b) => Ty.tnat }
    }
    fn sndTy(t: Ty) -> Ty {
        match t { | Ty.tnat => Ty.tnat | Ty.tbool => Ty.tnat | Ty.tarrow(d, c) => Ty.tnat | Ty.tprod(a, b) => b | Ty.tsum(a, b) => Ty.tnat }
    }
    -- Sum destructors (junk = tnat on a non-sum) and the sum test.
    fn isSum(t: Ty) -> Bool {
        match t { | Ty.tnat => Bool.false | Ty.tbool => Bool.false | Ty.tarrow(d, c) => Bool.false | Ty.tprod(a, b) => Bool.false | Ty.tsum(a, b) => Bool.true }
    }
    fn fstSum(t: Ty) -> Ty {
        match t { | Ty.tnat => Ty.tnat | Ty.tbool => Ty.tnat | Ty.tarrow(d, c) => Ty.tnat | Ty.tprod(a, b) => Ty.tnat | Ty.tsum(a, b) => a }
    }
    fn sndSum(t: Ty) -> Ty {
        match t { | Ty.tnat => Ty.tnat | Ty.tbool => Ty.tnat | Ty.tarrow(d, c) => Ty.tnat | Ty.tprod(a, b) => Ty.tnat | Ty.tsum(a, b) => b }
    }

    -- Decidable type equality, RECURSIVE on the structure (arrows compared componentwise).
    fn tyeq(x: Ty) -> (Ty -> Bool) {
        match x {
          | Ty.tnat  => fun (y : Ty) =>
              match y { | Ty.tnat => Bool.true | Ty.tbool => Bool.false | Ty.tarrow(d, c) => Bool.false | Ty.tprod(a, b) => Bool.false | Ty.tsum(a, b) => Bool.false }
          | Ty.tbool => fun (y : Ty) =>
              match y { | Ty.tnat => Bool.false | Ty.tbool => Bool.true | Ty.tarrow(d, c) => Bool.false | Ty.tprod(a, b) => Bool.false | Ty.tsum(a, b) => Bool.false }
          | Ty.tarrow(xd, xc) => fun (y : Ty) =>
              match y {
                | Ty.tnat  => Bool.false
                | Ty.tbool => Bool.false
                | Ty.tarrow(yd, yc) => and(tyeq(xd)(yd), tyeq(xc)(yc))
                | Ty.tprod(a, b) => Bool.false
                | Ty.tsum(a, b) => Bool.false
              }
          | Ty.tprod(xa, xb) => fun (y : Ty) =>
              match y {
                | Ty.tnat  => Bool.false
                | Ty.tbool => Bool.false
                | Ty.tarrow(d, c) => Bool.false
                | Ty.tprod(ya, yb) => and(tyeq(xa)(ya), tyeq(xb)(yb))
                | Ty.tsum(a, b) => Bool.false
              }
          | Ty.tsum(xa, xb) => fun (y : Ty) =>
              match y {
                | Ty.tnat  => Bool.false
                | Ty.tbool => Bool.false
                | Ty.tarrow(d, c) => Bool.false
                | Ty.tprod(a, b) => Bool.false
                | Ty.tsum(ya, yb) => and(tyeq(xa)(ya), tyeq(xb)(yb))
              }
        }
    }

    -- Congruence for the arrow constructor (used by `tyeq_sound`'s arrow case).
    def tarrow_cong (xd : Ty) (yd : Ty) (xc : Ty) (yc : Ty)
        (ed : Eq.{1} Ty xd yd) (ec : Eq.{1} Ty xc yc)
        : Eq.{1} Ty (Ty.tarrow xd xc) (Ty.tarrow yd yc) :=
      Eq.subst.{1} Ty (fun (c : Ty) => Eq.{1} Ty (Ty.tarrow xd xc) (Ty.tarrow yd c)) xc yc ec
        (Eq.subst.{1} Ty (fun (d : Ty) => Eq.{1} Ty (Ty.tarrow xd xc) (Ty.tarrow d xc)) xd yd ed
          (Eq.refl.{1} Ty (Ty.tarrow xd xc)))

    -- Congruence for the product constructor (used by `tyeq_sound`'s product case).
    def tprod_cong (xa : Ty) (ya : Ty) (xb : Ty) (yb : Ty)
        (ea : Eq.{1} Ty xa ya) (eb : Eq.{1} Ty xb yb)
        : Eq.{1} Ty (Ty.tprod xa xb) (Ty.tprod ya yb) :=
      Eq.subst.{1} Ty (fun (c : Ty) => Eq.{1} Ty (Ty.tprod xa xb) (Ty.tprod ya c)) xb yb eb
        (Eq.subst.{1} Ty (fun (d : Ty) => Eq.{1} Ty (Ty.tprod xa xb) (Ty.tprod d xb)) xa ya ea
          (Eq.refl.{1} Ty (Ty.tprod xa xb)))

    -- Congruence for the sum constructor (used by `tyeq_sound`'s sum case).
    def tsum_cong (xa : Ty) (ya : Ty) (xb : Ty) (yb : Ty)
        (ea : Eq.{1} Ty xa ya) (eb : Eq.{1} Ty xb yb)
        : Eq.{1} Ty (Ty.tsum xa xb) (Ty.tsum ya yb) :=
      Eq.subst.{1} Ty (fun (c : Ty) => Eq.{1} Ty (Ty.tsum xa xb) (Ty.tsum ya c)) xb yb eb
        (Eq.subst.{1} Ty (fun (d : Ty) => Eq.{1} Ty (Ty.tsum xa xb) (Ty.tsum d xb)) xa ya ea
          (Eq.refl.{1} Ty (Ty.tsum xa xb)))

    -- `tyeq` is a sound decider, by structural induction on the (recursive) type `x`.
    fn tyeq_sound(x: Ty) -> ((y : Ty) -> Eq.{1} Bool (tyeq(x)(y)) Bool.true -> Eq.{1} Ty x y) {
        match x {
          | Ty.tnat => fun (y : Ty) =>
              match y {
                | Ty.tnat  => fun (h : Eq.{1} Bool (tyeq(Ty.tnat)(Ty.tnat)) Bool.true) => Eq.refl.{1} Ty Ty.tnat
                | Ty.tbool => fun (h : Eq.{1} Bool (tyeq(Ty.tnat)(Ty.tbool)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tnat Ty.tbool) (ff_ne_tt h)
                | Ty.tarrow(d, c) => fun (h : Eq.{1} Bool (tyeq(Ty.tnat)(Ty.tarrow d c)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tnat (Ty.tarrow d c)) (ff_ne_tt h)
                | Ty.tprod(a, b) => fun (h : Eq.{1} Bool (tyeq(Ty.tnat)(Ty.tprod a b)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tnat (Ty.tprod a b)) (ff_ne_tt h)
                | Ty.tsum(a, b) => fun (h : Eq.{1} Bool (tyeq(Ty.tnat)(Ty.tsum a b)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tnat (Ty.tsum a b)) (ff_ne_tt h)
              }
          | Ty.tbool => fun (y : Ty) =>
              match y {
                | Ty.tnat  => fun (h : Eq.{1} Bool (tyeq(Ty.tbool)(Ty.tnat)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tbool Ty.tnat) (ff_ne_tt h)
                | Ty.tbool => fun (h : Eq.{1} Bool (tyeq(Ty.tbool)(Ty.tbool)) Bool.true) => Eq.refl.{1} Ty Ty.tbool
                | Ty.tarrow(d, c) => fun (h : Eq.{1} Bool (tyeq(Ty.tbool)(Ty.tarrow d c)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tbool (Ty.tarrow d c)) (ff_ne_tt h)
                | Ty.tprod(a, b) => fun (h : Eq.{1} Bool (tyeq(Ty.tbool)(Ty.tprod a b)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tbool (Ty.tprod a b)) (ff_ne_tt h)
                | Ty.tsum(a, b) => fun (h : Eq.{1} Bool (tyeq(Ty.tbool)(Ty.tsum a b)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tbool (Ty.tsum a b)) (ff_ne_tt h)
              }
          | Ty.tarrow(xd, xc) => fun (y : Ty) =>
              match y {
                | Ty.tnat  => fun (h : Eq.{1} Bool (tyeq(Ty.tarrow xd xc)(Ty.tnat)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tarrow xd xc) Ty.tnat) (ff_ne_tt h)
                | Ty.tbool => fun (h : Eq.{1} Bool (tyeq(Ty.tarrow xd xc)(Ty.tbool)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tarrow xd xc) Ty.tbool) (ff_ne_tt h)
                | Ty.tarrow(yd, yc) => fun (h : Eq.{1} Bool (tyeq(Ty.tarrow xd xc)(Ty.tarrow yd yc)) Bool.true) =>
                    tarrow_cong xd yd xc yc
                      (tyeq_sound(xd)(yd) (and_left (tyeq(xd)(yd)) (tyeq(xc)(yc)) h))
                      (tyeq_sound(xc)(yc) (and_right (tyeq(xd)(yd)) (tyeq(xc)(yc)) h))
                | Ty.tprod(a, b) => fun (h : Eq.{1} Bool (tyeq(Ty.tarrow xd xc)(Ty.tprod a b)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tarrow xd xc) (Ty.tprod a b)) (ff_ne_tt h)
                | Ty.tsum(a, b) => fun (h : Eq.{1} Bool (tyeq(Ty.tarrow xd xc)(Ty.tsum a b)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tarrow xd xc) (Ty.tsum a b)) (ff_ne_tt h)
              }
          | Ty.tprod(xa, xb) => fun (y : Ty) =>
              match y {
                | Ty.tnat  => fun (h : Eq.{1} Bool (tyeq(Ty.tprod xa xb)(Ty.tnat)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tprod xa xb) Ty.tnat) (ff_ne_tt h)
                | Ty.tbool => fun (h : Eq.{1} Bool (tyeq(Ty.tprod xa xb)(Ty.tbool)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tprod xa xb) Ty.tbool) (ff_ne_tt h)
                | Ty.tarrow(d, c) => fun (h : Eq.{1} Bool (tyeq(Ty.tprod xa xb)(Ty.tarrow d c)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tprod xa xb) (Ty.tarrow d c)) (ff_ne_tt h)
                | Ty.tprod(ya, yb) => fun (h : Eq.{1} Bool (tyeq(Ty.tprod xa xb)(Ty.tprod ya yb)) Bool.true) =>
                    tprod_cong xa ya xb yb
                      (tyeq_sound(xa)(ya) (and_left (tyeq(xa)(ya)) (tyeq(xb)(yb)) h))
                      (tyeq_sound(xb)(yb) (and_right (tyeq(xa)(ya)) (tyeq(xb)(yb)) h))
                | Ty.tsum(a, b) => fun (h : Eq.{1} Bool (tyeq(Ty.tprod xa xb)(Ty.tsum a b)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tprod xa xb) (Ty.tsum a b)) (ff_ne_tt h)
              }
          | Ty.tsum(xa, xb) => fun (y : Ty) =>
              match y {
                | Ty.tnat  => fun (h : Eq.{1} Bool (tyeq(Ty.tsum xa xb)(Ty.tnat)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tsum xa xb) Ty.tnat) (ff_ne_tt h)
                | Ty.tbool => fun (h : Eq.{1} Bool (tyeq(Ty.tsum xa xb)(Ty.tbool)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tsum xa xb) Ty.tbool) (ff_ne_tt h)
                | Ty.tarrow(d, c) => fun (h : Eq.{1} Bool (tyeq(Ty.tsum xa xb)(Ty.tarrow d c)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tsum xa xb) (Ty.tarrow d c)) (ff_ne_tt h)
                | Ty.tprod(a, b) => fun (h : Eq.{1} Bool (tyeq(Ty.tsum xa xb)(Ty.tprod a b)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tsum xa xb) (Ty.tprod a b)) (ff_ne_tt h)
                | Ty.tsum(ya, yb) => fun (h : Eq.{1} Bool (tyeq(Ty.tsum xa xb)(Ty.tsum ya yb)) Bool.true) =>
                    tsum_cong xa ya xb yb
                      (tyeq_sound(xa)(ya) (and_left (tyeq(xa)(ya)) (tyeq(xb)(yb)) h))
                      (tyeq_sound(xb)(yb) (and_right (tyeq(xa)(ya)) (tyeq(xb)(yb)) h))
              }
        }
    }

    -- `tyeq` is reflexive (a type equals itself), by structural induction.
    fn tyeq_refl(t: Ty) -> Eq.{1} Bool (tyeq(t)(t)) Bool.true {
        match t {
          | Ty.tnat  => Eq.refl.{1} Bool Bool.true
          | Ty.tbool => Eq.refl.{1} Bool Bool.true
          | Ty.tarrow(d, c) => and_true (tyeq(d)(d)) (tyeq(c)(c)) (tyeq_refl(d)) (tyeq_refl(c))
          | Ty.tprod(a, b) => and_true (tyeq(a)(a)) (tyeq(b)(b)) (tyeq_refl(a)) (tyeq_refl(b))
          | Ty.tsum(a, b) => and_true (tyeq(a)(a)) (tyeq(b)(b)) (tyeq_refl(a)) (tyeq_refl(b))
        }
    }
    -- ...so equal types are accepted by the decider (the converse of `tyeq_sound`).
    def tyeq_of_eq (x : Ty) (y : Ty) (h : Eq.{1} Ty x y) : Eq.{1} Bool (tyeq(x)(y)) Bool.true :=
      Eq.subst.{1} Ty (fun (z : Ty) => Eq.{1} Bool (tyeq(z)(y)) Bool.true) y x
        (Eq.symm.{1} Ty x y h) (tyeq_refl(y))

    -- Arrow inversion: if a type tests as an arrow, it really is `tarrow (domOf t) (codOf t)`.
    fn arrow_inv(t: Ty)
      -> (Eq.{1} Bool (isArrow(t)) Bool.true -> Eq.{1} Ty t (Ty.tarrow (domOf(t)) (codOf(t)))) {
        match t {
          | Ty.tnat => fun (h : Eq.{1} Bool (isArrow(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tnat (Ty.tarrow (domOf(Ty.tnat)) (codOf(Ty.tnat)))) (ff_ne_tt h)
          | Ty.tbool => fun (h : Eq.{1} Bool (isArrow(Ty.tbool)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tbool (Ty.tarrow (domOf(Ty.tbool)) (codOf(Ty.tbool)))) (ff_ne_tt h)
          | Ty.tarrow(d, c) => fun (h : Eq.{1} Bool (isArrow(Ty.tarrow d c)) Bool.true) =>
              Eq.refl.{1} Ty (Ty.tarrow d c)
          | Ty.tprod(a, b) => fun (h : Eq.{1} Bool (isArrow(Ty.tprod a b)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tprod a b) (Ty.tarrow (domOf(Ty.tprod a b)) (codOf(Ty.tprod a b)))) (ff_ne_tt h)
          | Ty.tsum(a, b) => fun (h : Eq.{1} Bool (isArrow(Ty.tsum a b)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tsum a b) (Ty.tarrow (domOf(Ty.tsum a b)) (codOf(Ty.tsum a b)))) (ff_ne_tt h)
        }
    }
    -- Product inversion: if a type tests as a product, it really is `tprod (fstTy t) (sndTy t)`.
    fn prod_inv(t: Ty)
      -> (Eq.{1} Bool (isProd(t)) Bool.true -> Eq.{1} Ty t (Ty.tprod (fstTy(t)) (sndTy(t)))) {
        match t {
          | Ty.tnat => fun (h : Eq.{1} Bool (isProd(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tnat (Ty.tprod (fstTy(Ty.tnat)) (sndTy(Ty.tnat)))) (ff_ne_tt h)
          | Ty.tbool => fun (h : Eq.{1} Bool (isProd(Ty.tbool)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tbool (Ty.tprod (fstTy(Ty.tbool)) (sndTy(Ty.tbool)))) (ff_ne_tt h)
          | Ty.tarrow(d, c) => fun (h : Eq.{1} Bool (isProd(Ty.tarrow d c)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tarrow d c) (Ty.tprod (fstTy(Ty.tarrow d c)) (sndTy(Ty.tarrow d c)))) (ff_ne_tt h)
          | Ty.tprod(a, b) => fun (h : Eq.{1} Bool (isProd(Ty.tprod a b)) Bool.true) =>
              Eq.refl.{1} Ty (Ty.tprod a b)
          | Ty.tsum(a, b) => fun (h : Eq.{1} Bool (isProd(Ty.tsum a b)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tsum a b) (Ty.tprod (fstTy(Ty.tsum a b)) (sndTy(Ty.tsum a b)))) (ff_ne_tt h)
        }
    }
    -- Sum inversion: if a type tests as a sum, it really is `tsum (fstSum t) (sndSum t)`.
    fn sum_inv(t: Ty)
      -> (Eq.{1} Bool (isSum(t)) Bool.true -> Eq.{1} Ty t (Ty.tsum (fstSum(t)) (sndSum(t)))) {
        match t {
          | Ty.tnat => fun (h : Eq.{1} Bool (isSum(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tnat (Ty.tsum (fstSum(Ty.tnat)) (sndSum(Ty.tnat)))) (ff_ne_tt h)
          | Ty.tbool => fun (h : Eq.{1} Bool (isSum(Ty.tbool)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty Ty.tbool (Ty.tsum (fstSum(Ty.tbool)) (sndSum(Ty.tbool)))) (ff_ne_tt h)
          | Ty.tarrow(d, c) => fun (h : Eq.{1} Bool (isSum(Ty.tarrow d c)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tarrow d c) (Ty.tsum (fstSum(Ty.tarrow d c)) (sndSum(Ty.tarrow d c)))) (ff_ne_tt h)
          | Ty.tprod(a, b) => fun (h : Eq.{1} Bool (isSum(Ty.tprod a b)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty (Ty.tprod a b) (Ty.tsum (fstSum(Ty.tprod a b)) (sndSum(Ty.tprod a b)))) (ff_ne_tt h)
          | Ty.tsum(a, b) => fun (h : Eq.{1} Bool (isSum(Ty.tsum a b)) Bool.true) =>
              Eq.refl.{1} Ty (Ty.tsum a b)
        }
    }

    -- The typing CONTEXT and de Bruijn lookup / scope check.
    inductive Ctx : Type | nil : Ctx | cons : Ty -> Ctx -> Ctx
    fn lookup(G: Ctx) -> (Nat -> Ty) {
        match G {
          | Ctx.nil         => fun (n : Nat) => Ty.tnat
          | Ctx.cons(T, G2) => fun (n : Nat) =>
              match n { | Nat.zero => T | Nat.succ(m) => lookup(G2)(m) }
        }
    }
    fn inScope(G: Ctx) -> (Nat -> Bool) {
        match G {
          | Ctx.nil         => fun (n : Nat) => Bool.false
          | Ctx.cons(T, G2) => fun (n : Nat) =>
              match n { | Nat.zero => Bool.true | Nat.succ(m) => inScope(G2)(m) }
        }
    }
    inductive Lookup : Ctx -> Nat -> Ty -> Prop
      | here  : (T : Ty) -> (G : Ctx) -> Lookup (Ctx.cons T G) Nat.zero T
      | there : (T : Ty) -> (U : Ty) -> (G : Ctx) -> (n : Nat)
                  -> Lookup G n T -> Lookup (Ctx.cons U G) (Nat.succ n) T
    fn lookup_sound(G: Ctx)
      -> ((n : Nat) -> Eq.{1} Bool (inScope(G)(n)) Bool.true -> Lookup G n (lookup(G)(n))) {
        match G {
          | Ctx.nil => fun (n : Nat) (h : Eq.{1} Bool (inScope(Ctx.nil)(n)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Lookup Ctx.nil n (lookup(Ctx.nil)(n))) (ff_ne_tt h)
          | Ctx.cons(T, G2) => fun (n : Nat) =>
              match n {
                | Nat.zero => fun (h : Eq.{1} Bool (inScope(Ctx.cons(T, G2))(Nat.zero)) Bool.true) =>
                    Lookup.here T G2
                | Nat.succ(m) => fun (h : Eq.{1} Bool (inScope(Ctx.cons(T, G2))(Nat.succ(m))) Bool.true) =>
                    Lookup.there (lookup(G2)(m)) T G2 m (lookup_sound(G2)(m)(h))
              }
        }
    }

    -- Converse facts for completeness, by induction on the `Lookup` DERIVATION: a bound
    -- variable really is in scope and the lookup function returns its type.
    def lookup_complete (G : Ctx) (n : Nat) (T : Ty) (lk : Lookup G n T)
        : Eq.{1} Ty (lookup(G)(n)) T :=
      match lk {
        | Lookup.here(T2, G2)               => Eq.refl.{1} Ty T2
        | Lookup.there(T2, U2, G2, n2, lk2) => lk2.rec
      }
    def inScope_complete (G : Ctx) (n : Nat) (T : Ty) (lk : Lookup G n T)
        : Eq.{1} Bool (inScope(G)(n)) Bool.true :=
      match lk {
        | Lookup.here(T2, G2)               => Eq.refl.{1} Bool Bool.true
        | Lookup.there(T2, U2, G2, n2, lk2) => lk2.rec
      }
"#;

/// The simply-typed λ-calculus (`Exp` with variables, `let`, λ, and application), the
/// typing relation `HasTy`, the checker, and the soundness theorem.
pub const LANG: &str = r#"
    -- A simply-typed expression language: variables, literals, addition, `let`, and now
    -- λ-abstraction (with an annotated parameter type) and application.
    inductive Exp : Type
      | evar : Nat -> Exp
      | enat : Nat -> Exp
      | ebool : Bool -> Exp
      | eadd : Exp -> Exp -> Exp
      | elet : Exp -> Exp -> Exp
      | elam : Ty -> Exp -> Exp            -- λ (_ : A). body     : tarrow A (type of body)
      | eapp : Exp -> Exp -> Exp           -- f a                 : codomain of f's type
      | eif  : Exp -> Exp -> Exp -> Exp    -- if cnd then thn else els (branches same type)
      | efix : Ty -> Exp -> Exp            -- fix (self : A). body : A  (self is de Bruijn 0)
      | epair : Exp -> Exp -> Exp          -- (a, b)              : tprod (type a) (type b)
      | efst : Exp -> Exp                  -- fst p               : first component's type
      | esnd : Exp -> Exp                  -- snd p               : second component's type
      | einl : Ty -> Exp -> Exp            -- inl[B] v            : tsum (type v) B
      | einr : Ty -> Exp -> Exp            -- inr[A] v            : tsum A (type v)
      | ecase : Exp -> Exp -> Exp -> Exp   -- case s of l | r  (l,r each bind the payload at 0)

    -- The typing RELATION (the specification).
    inductive HasTy : Ctx -> Exp -> Ty -> Prop
      | tvar  : (G : Ctx) -> (n : Nat) -> (T : Ty)
                  -> Lookup G n T -> HasTy G (Exp.evar n) T
      | tnat  : (G : Ctx) -> (n : Nat) -> HasTy G (Exp.enat n) Ty.tnat
      | tbool : (G : Ctx) -> (b : Bool) -> HasTy G (Exp.ebool b) Ty.tbool
      | tadd  : (G : Ctx) -> (a : Exp) -> (b : Exp)
                  -> HasTy G a Ty.tnat -> HasTy G b Ty.tnat
                  -> HasTy G (Exp.eadd a b) Ty.tnat
      | tlet  : (G : Ctx) -> (a : Exp) -> (body : Exp) -> (A : Ty) -> (B : Ty)
                  -> HasTy G a A -> HasTy (Ctx.cons A G) body B
                  -> HasTy G (Exp.elet a body) B
      | tlam  : (G : Ctx) -> (A : Ty) -> (body : Exp) -> (B : Ty)
                  -> HasTy (Ctx.cons A G) body B
                  -> HasTy G (Exp.elam A body) (Ty.tarrow A B)
      | tapp  : (G : Ctx) -> (f : Exp) -> (a : Exp) -> (A : Ty) -> (B : Ty)
                  -> HasTy G f (Ty.tarrow A B) -> HasTy G a A
                  -> HasTy G (Exp.eapp f a) B
      | tif   : (G : Ctx) -> (cnd : Exp) -> (thn : Exp) -> (els : Exp) -> (T : Ty)
                  -> HasTy G cnd Ty.tbool -> HasTy G thn T -> HasTy G els T
                  -> HasTy G (Exp.eif cnd thn els) T
      | tfix  : (G : Ctx) -> (A : Ty) -> (body : Exp)
                  -> HasTy (Ctx.cons A G) body A
                  -> HasTy G (Exp.efix A body) A
      | tpair : (G : Ctx) -> (a : Exp) -> (b : Exp) -> (A : Ty) -> (B : Ty)
                  -> HasTy G a A -> HasTy G b B
                  -> HasTy G (Exp.epair a b) (Ty.tprod A B)
      | tfst  : (G : Ctx) -> (p : Exp) -> (A : Ty) -> (B : Ty)
                  -> HasTy G p (Ty.tprod A B)
                  -> HasTy G (Exp.efst p) A
      | tsnd  : (G : Ctx) -> (p : Exp) -> (A : Ty) -> (B : Ty)
                  -> HasTy G p (Ty.tprod A B)
                  -> HasTy G (Exp.esnd p) B
      | tinl  : (G : Ctx) -> (B : Ty) -> (v : Exp) -> (A : Ty)
                  -> HasTy G v A
                  -> HasTy G (Exp.einl B v) (Ty.tsum A B)
      | tinr  : (G : Ctx) -> (A : Ty) -> (v : Exp) -> (B : Ty)
                  -> HasTy G v B
                  -> HasTy G (Exp.einr A v) (Ty.tsum A B)
      | tcase : (G : Ctx) -> (s : Exp) -> (l : Exp) -> (r : Exp) -> (A : Ty) -> (B : Ty) -> (C : Ty)
                  -> HasTy G s (Ty.tsum A B) -> HasTy (Ctx.cons A G) l C -> HasTy (Ctx.cons B G) r C
                  -> HasTy G (Exp.ecase s l r) C

    -- The checker: synthesize the type, threading the context. `elam` builds an arrow;
    -- `eapp` returns the codomain of the function's (synthesized) type.
    fn synth(e: Exp) -> (Ctx -> Ty) {
        match e {
          | Exp.evar(n)       => fun (G : Ctx) => lookup(G)(n)
          | Exp.enat(n)       => fun (G : Ctx) => Ty.tnat
          | Exp.ebool(b)      => fun (G : Ctx) => Ty.tbool
          | Exp.eadd(a, b)    => fun (G : Ctx) => Ty.tnat
          | Exp.elet(a, body) => fun (G : Ctx) => synth(body)(Ctx.cons(synth(a)(G), G))
          | Exp.elam(A, body) => fun (G : Ctx) => Ty.tarrow A (synth(body)(Ctx.cons(A, G)))
          | Exp.eapp(f, a)    => fun (G : Ctx) => codOf(synth(f)(G))
          | Exp.eif(cnd, thn, els) => fun (G : Ctx) => synth(thn)(G)
          | Exp.efix(A, body) => fun (G : Ctx) => A
          | Exp.epair(a, b) => fun (G : Ctx) => Ty.tprod (synth(a)(G)) (synth(b)(G))
          | Exp.efst(p) => fun (G : Ctx) => fstTy(synth(p)(G))
          | Exp.esnd(p) => fun (G : Ctx) => sndTy(synth(p)(G))
          | Exp.einl(B, v) => fun (G : Ctx) => Ty.tsum (synth(v)(G)) B
          | Exp.einr(A, v) => fun (G : Ctx) => Ty.tsum A (synth(v)(G))
          | Exp.ecase(s, l, r) => fun (G : Ctx) => synth(l)(Ctx.cons(fstSum(synth(s)(G)), G))
        }
    }
    -- The well-typedness decision. `eapp` is well typed iff both parts are, the function
    -- synthesizes an arrow, and that arrow's domain matches the argument's type.
    fn ok(e: Exp) -> (Ctx -> Bool) {
        match e {
          | Exp.evar(n)    => fun (G : Ctx) => inScope(G)(n)
          | Exp.enat(n)    => fun (G : Ctx) => Bool.true
          | Exp.ebool(b)   => fun (G : Ctx) => Bool.true
          | Exp.eadd(a, b) => fun (G : Ctx) =>
              and(and(ok(a)(G), ok(b)(G)),
                  and(tyeq(synth(a)(G))(Ty.tnat), tyeq(synth(b)(G))(Ty.tnat)))
          | Exp.elet(a, body) => fun (G : Ctx) =>
              and(ok(a)(G), ok(body)(Ctx.cons(synth(a)(G), G)))
          | Exp.elam(A, body) => fun (G : Ctx) => ok(body)(Ctx.cons(A, G))
          | Exp.eapp(f, a) => fun (G : Ctx) =>
              and(and(ok(f)(G), ok(a)(G)),
                  and(isArrow(synth(f)(G)), tyeq(domOf(synth(f)(G)))(synth(a)(G))))
          | Exp.eif(cnd, thn, els) => fun (G : Ctx) =>
              and(and(ok(cnd)(G), and(ok(thn)(G), ok(els)(G))),
                  and(tyeq(synth(cnd)(G))(Ty.tbool), tyeq(synth(thn)(G))(synth(els)(G))))
          | Exp.efix(A, body) => fun (G : Ctx) =>
              and(ok(body)(Ctx.cons(A, G)), tyeq(synth(body)(Ctx.cons(A, G)))(A))
          | Exp.epair(a, b) => fun (G : Ctx) => and(ok(a)(G), ok(b)(G))
          | Exp.efst(p) => fun (G : Ctx) => and(ok(p)(G), isProd(synth(p)(G)))
          | Exp.esnd(p) => fun (G : Ctx) => and(ok(p)(G), isProd(synth(p)(G)))
          | Exp.einl(B, v) => fun (G : Ctx) => ok(v)(G)
          | Exp.einr(A, v) => fun (G : Ctx) => ok(v)(G)
          | Exp.ecase(s, l, r) => fun (G : Ctx) =>
              and(and(ok(s)(G), isSum(synth(s)(G))),
                  and(ok(l)(Ctx.cons(fstSum(synth(s)(G)), G)),
                      and(ok(r)(Ctx.cons(sndSum(synth(s)(G)), G)),
                          tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G))))))
        }
    }

    -- THE SOUNDNESS THEOREM for the simply-typed calculus:
    --   ok e Γ = true → HasTy Γ e (synth e Γ),
    -- by structural recursion on `e`. The `eapp` case inverts the synthesized function
    -- type to an arrow (`arrow_inv`), rewrites its domain to the argument's type
    -- (`tyeq_sound` + `Eq.subst`), and applies `tapp`.
    fn ok_sound(e: Exp)
      -> ((G : Ctx) -> Eq.{1} Bool (ok(e)(G)) Bool.true -> HasTy G e (synth(e)(G))) {
        match e {
          | Exp.evar(n) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.evar(n))(G)) Bool.true) =>
              HasTy.tvar G n (lookup(G)(n)) (lookup_sound(G)(n)(h))
          | Exp.enat(n) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.enat(n))(G)) Bool.true) =>
              HasTy.tnat G n
          | Exp.ebool(b) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.ebool(b))(G)) Bool.true) =>
              HasTy.tbool G b
          | Exp.eadd(a, b) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.eadd(a, b))(G)) Bool.true) =>
              HasTy.tadd G a b
                (Eq.subst.{1} Ty (fun (T : Ty) => HasTy G a T) (synth(a)(G)) Ty.tnat
                   (tyeq_sound(synth(a)(G))(Ty.tnat)
                      (and_left (tyeq(synth(a)(G))(Ty.tnat)) (tyeq(synth(b)(G))(Ty.tnat))
                         (and_right (and(ok(a)(G), ok(b)(G)))
                                    (and(tyeq(synth(a)(G))(Ty.tnat), tyeq(synth(b)(G))(Ty.tnat))) h)))
                   (ok_sound(a)(G)
                      (and_left (ok(a)(G)) (ok(b)(G))
                         (and_left (and(ok(a)(G), ok(b)(G)))
                                   (and(tyeq(synth(a)(G))(Ty.tnat), tyeq(synth(b)(G))(Ty.tnat))) h))))
                (Eq.subst.{1} Ty (fun (T : Ty) => HasTy G b T) (synth(b)(G)) Ty.tnat
                   (tyeq_sound(synth(b)(G))(Ty.tnat)
                      (and_right (tyeq(synth(a)(G))(Ty.tnat)) (tyeq(synth(b)(G))(Ty.tnat))
                         (and_right (and(ok(a)(G), ok(b)(G)))
                                    (and(tyeq(synth(a)(G))(Ty.tnat), tyeq(synth(b)(G))(Ty.tnat))) h)))
                   (ok_sound(b)(G)
                      (and_right (ok(a)(G)) (ok(b)(G))
                         (and_left (and(ok(a)(G), ok(b)(G)))
                                   (and(tyeq(synth(a)(G))(Ty.tnat), tyeq(synth(b)(G))(Ty.tnat))) h))))
          | Exp.elet(a, body) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.elet(a, body))(G)) Bool.true) =>
              HasTy.tlet G a body (synth(a)(G)) (synth(body)(Ctx.cons(synth(a)(G), G)))
                (ok_sound(a)(G)
                   (and_left (ok(a)(G)) (ok(body)(Ctx.cons(synth(a)(G), G))) h))
                (ok_sound(body)(Ctx.cons(synth(a)(G), G))
                   (and_right (ok(a)(G)) (ok(body)(Ctx.cons(synth(a)(G), G))) h))
          | Exp.elam(A, body) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.elam(A, body))(G)) Bool.true) =>
              HasTy.tlam G A body (synth(body)(Ctx.cons(A, G)))
                (ok_sound(body)(Ctx.cons(A, G)) h)
          | Exp.eapp(f, a) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.eapp(f, a))(G)) Bool.true) =>
              HasTy.tapp G f a (synth(a)(G)) (codOf(synth(f)(G)))
                (Eq.subst.{1} Ty
                   (fun (d : Ty) => HasTy G f (Ty.tarrow d (codOf(synth(f)(G)))))
                   (domOf(synth(f)(G))) (synth(a)(G))
                   (tyeq_sound(domOf(synth(f)(G)))(synth(a)(G))
                      (and_right (isArrow(synth(f)(G))) (tyeq(domOf(synth(f)(G)))(synth(a)(G)))
                         (and_right (and(ok(f)(G), ok(a)(G)))
                                    (and(isArrow(synth(f)(G)), tyeq(domOf(synth(f)(G)))(synth(a)(G)))) h)))
                   (Eq.subst.{1} Ty (fun (t : Ty) => HasTy G f t)
                      (synth(f)(G)) (Ty.tarrow (domOf(synth(f)(G))) (codOf(synth(f)(G))))
                      (arrow_inv(synth(f)(G))
                         (and_left (isArrow(synth(f)(G))) (tyeq(domOf(synth(f)(G)))(synth(a)(G)))
                            (and_right (and(ok(f)(G), ok(a)(G)))
                                       (and(isArrow(synth(f)(G)), tyeq(domOf(synth(f)(G)))(synth(a)(G)))) h)))
                      (ok_sound(f)(G)
                         (and_left (ok(f)(G)) (ok(a)(G))
                            (and_left (and(ok(f)(G), ok(a)(G)))
                                      (and(isArrow(synth(f)(G)), tyeq(domOf(synth(f)(G)))(synth(a)(G)))) h)))))
                (ok_sound(a)(G)
                   (and_right (ok(f)(G)) (ok(a)(G))
                      (and_left (and(ok(f)(G), ok(a)(G)))
                                (and(isArrow(synth(f)(G)), tyeq(domOf(synth(f)(G)))(synth(a)(G)))) h)))
          | Exp.eif(cnd, thn, els) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.eif(cnd, thn, els))(G)) Bool.true) =>
              HasTy.tif G cnd thn els (synth(thn)(G))
                (Eq.subst.{1} Ty (fun (T : Ty) => HasTy G cnd T) (synth(cnd)(G)) Ty.tbool
                   (tyeq_sound(synth(cnd)(G))(Ty.tbool)
                      (and_left (tyeq(synth(cnd)(G))(Ty.tbool)) (tyeq(synth(thn)(G))(synth(els)(G)))
                         (and_right (and(ok(cnd)(G), and(ok(thn)(G), ok(els)(G))))
                                    (and(tyeq(synth(cnd)(G))(Ty.tbool), tyeq(synth(thn)(G))(synth(els)(G)))) h)))
                   (ok_sound(cnd)(G)
                      (and_left (ok(cnd)(G)) (and(ok(thn)(G), ok(els)(G)))
                         (and_left (and(ok(cnd)(G), and(ok(thn)(G), ok(els)(G))))
                                   (and(tyeq(synth(cnd)(G))(Ty.tbool), tyeq(synth(thn)(G))(synth(els)(G)))) h))))
                (ok_sound(thn)(G)
                   (and_left (ok(thn)(G)) (ok(els)(G))
                      (and_right (ok(cnd)(G)) (and(ok(thn)(G), ok(els)(G)))
                         (and_left (and(ok(cnd)(G), and(ok(thn)(G), ok(els)(G))))
                                   (and(tyeq(synth(cnd)(G))(Ty.tbool), tyeq(synth(thn)(G))(synth(els)(G)))) h))))
                (Eq.subst.{1} Ty (fun (T : Ty) => HasTy G els T) (synth(els)(G)) (synth(thn)(G))
                   (Eq.symm.{1} Ty (synth(thn)(G)) (synth(els)(G))
                      (tyeq_sound(synth(thn)(G))(synth(els)(G))
                         (and_right (tyeq(synth(cnd)(G))(Ty.tbool)) (tyeq(synth(thn)(G))(synth(els)(G)))
                            (and_right (and(ok(cnd)(G), and(ok(thn)(G), ok(els)(G))))
                                       (and(tyeq(synth(cnd)(G))(Ty.tbool), tyeq(synth(thn)(G))(synth(els)(G)))) h))))
                   (ok_sound(els)(G)
                      (and_right (ok(thn)(G)) (ok(els)(G))
                         (and_right (ok(cnd)(G)) (and(ok(thn)(G), ok(els)(G)))
                            (and_left (and(ok(cnd)(G), and(ok(thn)(G), ok(els)(G))))
                                      (and(tyeq(synth(cnd)(G))(Ty.tbool), tyeq(synth(thn)(G))(synth(els)(G)))) h)))))
          | Exp.efix(A, body) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.efix(A, body))(G)) Bool.true) =>
              HasTy.tfix G A body
                (Eq.subst.{1} Ty (fun (X : Ty) => HasTy (Ctx.cons A G) body X) (synth(body)(Ctx.cons(A, G))) A
                   (tyeq_sound(synth(body)(Ctx.cons(A, G)))(A)
                      (and_right (ok(body)(Ctx.cons(A, G))) (tyeq(synth(body)(Ctx.cons(A, G)))(A)) h))
                   (ok_sound(body)(Ctx.cons(A, G))
                      (and_left (ok(body)(Ctx.cons(A, G))) (tyeq(synth(body)(Ctx.cons(A, G)))(A)) h)))
          | Exp.epair(a, b) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.epair(a, b))(G)) Bool.true) =>
              HasTy.tpair G a b (synth(a)(G)) (synth(b)(G))
                (ok_sound(a)(G) (and_left (ok(a)(G)) (ok(b)(G)) h))
                (ok_sound(b)(G) (and_right (ok(a)(G)) (ok(b)(G)) h))
          | Exp.efst(p) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.efst(p))(G)) Bool.true) =>
              HasTy.tfst G p (fstTy(synth(p)(G))) (sndTy(synth(p)(G)))
                (Eq.subst.{1} Ty (fun (t : Ty) => HasTy G p t)
                   (synth(p)(G)) (Ty.tprod (fstTy(synth(p)(G))) (sndTy(synth(p)(G))))
                   (prod_inv(synth(p)(G)) (and_right (ok(p)(G)) (isProd(synth(p)(G))) h))
                   (ok_sound(p)(G) (and_left (ok(p)(G)) (isProd(synth(p)(G))) h)))
          | Exp.esnd(p) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.esnd(p))(G)) Bool.true) =>
              HasTy.tsnd G p (fstTy(synth(p)(G))) (sndTy(synth(p)(G)))
                (Eq.subst.{1} Ty (fun (t : Ty) => HasTy G p t)
                   (synth(p)(G)) (Ty.tprod (fstTy(synth(p)(G))) (sndTy(synth(p)(G))))
                   (prod_inv(synth(p)(G)) (and_right (ok(p)(G)) (isProd(synth(p)(G))) h))
                   (ok_sound(p)(G) (and_left (ok(p)(G)) (isProd(synth(p)(G))) h)))
          | Exp.einl(B, v) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.einl(B, v))(G)) Bool.true) =>
              HasTy.tinl G B v (synth(v)(G)) (ok_sound(v)(G) h)
          | Exp.einr(A, v) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.einr(A, v))(G)) Bool.true) =>
              HasTy.tinr G A v (synth(v)(G)) (ok_sound(v)(G) h)
          | Exp.ecase(s, l, r) => fun (G : Ctx) (h : Eq.{1} Bool (ok(Exp.ecase(s, l, r))(G)) Bool.true) =>
              HasTy.tcase G s l r (fstSum(synth(s)(G))) (sndSum(synth(s)(G))) (synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))
                (Eq.subst.{1} Ty (fun (t : Ty) => HasTy G s t)
                   (synth(s)(G)) (Ty.tsum (fstSum(synth(s)(G))) (sndSum(synth(s)(G))))
                   (sum_inv(synth(s)(G))
                      (and_right (ok(s)(G)) (isSum(synth(s)(G)))
                         (and_left (and(ok(s)(G), isSum(synth(s)(G))))
                                   (and(ok(l)(Ctx.cons(fstSum(synth(s)(G)), G)), and(ok(r)(Ctx.cons(sndSum(synth(s)(G)), G)), tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))))) h)))
                   (ok_sound(s)(G)
                      (and_left (ok(s)(G)) (isSum(synth(s)(G)))
                         (and_left (and(ok(s)(G), isSum(synth(s)(G))))
                                   (and(ok(l)(Ctx.cons(fstSum(synth(s)(G)), G)), and(ok(r)(Ctx.cons(sndSum(synth(s)(G)), G)), tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))))) h))))
                (ok_sound(l)(Ctx.cons(fstSum(synth(s)(G)), G))
                   (and_left (ok(l)(Ctx.cons(fstSum(synth(s)(G)), G))) (and(ok(r)(Ctx.cons(sndSum(synth(s)(G)), G)), tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))))
                      (and_right (and(ok(s)(G), isSum(synth(s)(G))))
                                 (and(ok(l)(Ctx.cons(fstSum(synth(s)(G)), G)), and(ok(r)(Ctx.cons(sndSum(synth(s)(G)), G)), tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))))) h)))
                (Eq.subst.{1} Ty (fun (t : Ty) => HasTy (Ctx.cons(sndSum(synth(s)(G)), G)) r t)
                   (synth(r)(Ctx.cons(sndSum(synth(s)(G)), G))) (synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))
                   (Eq.symm.{1} Ty (synth(l)(Ctx.cons(fstSum(synth(s)(G)), G))) (synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))
                      (tyeq_sound(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))
                         (and_right (ok(r)(Ctx.cons(sndSum(synth(s)(G)), G))) (tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G))))
                            (and_right (ok(l)(Ctx.cons(fstSum(synth(s)(G)), G))) (and(ok(r)(Ctx.cons(sndSum(synth(s)(G)), G)), tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))))
                               (and_right (and(ok(s)(G), isSum(synth(s)(G))))
                                          (and(ok(l)(Ctx.cons(fstSum(synth(s)(G)), G)), and(ok(r)(Ctx.cons(sndSum(synth(s)(G)), G)), tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))))) h)))))
                   (ok_sound(r)(Ctx.cons(sndSum(synth(s)(G)), G))
                      (and_left (ok(r)(Ctx.cons(sndSum(synth(s)(G)), G))) (tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G))))
                         (and_right (ok(l)(Ctx.cons(fstSum(synth(s)(G)), G))) (and(ok(r)(Ctx.cons(sndSum(synth(s)(G)), G)), tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))))
                            (and_right (and(ok(s)(G), isSum(synth(s)(G))))
                                       (and(ok(l)(Ctx.cons(fstSum(synth(s)(G)), G)), and(ok(r)(Ctx.cons(sndSum(synth(s)(G)), G)), tyeq(synth(l)(Ctx.cons(fstSum(synth(s)(G)), G)))(synth(r)(Ctx.cons(sndSum(synth(s)(G)), G)))))) h)))))
        }
    }

    -- COMPLETENESS, part 1: the synthesized type agrees with the relation, by induction
    -- on the typing DERIVATION (every rule pins the type, modulo lookups, IHs, and the
    -- arrow/codomain computations).
    def synth_complete (G : Ctx) (e : Exp) (T : Ty) (d : HasTy G e T) : Eq.{1} Ty (synth(e)(G)) T :=
      match d {
        | HasTy.tvar(G2, n2, T2, lk2) => lookup_complete G2 n2 T2 lk2
        | HasTy.tnat(G2, n2)          => Eq.refl.{1} Ty Ty.tnat
        | HasTy.tbool(G2, b2)         => Eq.refl.{1} Ty Ty.tbool
        | HasTy.tadd(G2, a2, b2, da, db) => Eq.refl.{1} Ty Ty.tnat
        | HasTy.tlet(G2, a2, body2, A2, B2, da, dbody) =>
            Eq.subst.{1} Ty (fun (X : Ty) => Eq.{1} Ty (synth(body2)(Ctx.cons(X, G2))) B2)
              A2 (synth(a2)(G2)) (Eq.symm.{1} Ty (synth(a2)(G2)) A2 da.rec) dbody.rec
        | HasTy.tlam(G2, A2, body2, B2, dbody) =>
            tarrow_cong A2 A2 (synth(body2)(Ctx.cons(A2, G2))) B2 (Eq.refl.{1} Ty A2) dbody.rec
        | HasTy.tapp(G2, f2, a2, A2, B2, df, da) =>
            Eq.subst.{1} Ty (fun (t : Ty) => Eq.{1} Ty (codOf(t)) B2)
              (Ty.tarrow A2 B2) (synth(f2)(G2))
              (Eq.symm.{1} Ty (synth(f2)(G2)) (Ty.tarrow A2 B2) df.rec)
              (Eq.refl.{1} Ty B2)
        | HasTy.tif(G2, cnd2, thn2, els2, T2, dc, dt, de) => dt.rec
        | HasTy.tfix(G2, A2, body2, dbody) => Eq.refl.{1} Ty A2
        | HasTy.tpair(G2, a2, b2, A2, B2, da, db) =>
            tprod_cong (synth(a2)(G2)) A2 (synth(b2)(G2)) B2 da.rec db.rec
        | HasTy.tfst(G2, p2, A2, B2, dp) =>
            Eq.subst.{1} Ty (fun (t : Ty) => Eq.{1} Ty (fstTy(t)) A2)
              (Ty.tprod A2 B2) (synth(p2)(G2))
              (Eq.symm.{1} Ty (synth(p2)(G2)) (Ty.tprod A2 B2) dp.rec)
              (Eq.refl.{1} Ty A2)
        | HasTy.tsnd(G2, p2, A2, B2, dp) =>
            Eq.subst.{1} Ty (fun (t : Ty) => Eq.{1} Ty (sndTy(t)) B2)
              (Ty.tprod A2 B2) (synth(p2)(G2))
              (Eq.symm.{1} Ty (synth(p2)(G2)) (Ty.tprod A2 B2) dp.rec)
              (Eq.refl.{1} Ty B2)
        | HasTy.tinl(G2, B2, v2, A2, dv) =>
            tsum_cong (synth(v2)(G2)) A2 B2 B2 dv.rec (Eq.refl.{1} Ty B2)
        | HasTy.tinr(G2, A2, v2, B2, dv) =>
            tsum_cong A2 A2 (synth(v2)(G2)) B2 (Eq.refl.{1} Ty A2) dv.rec
        | HasTy.tcase(G2, s2, l2, r2, A2, B2, C2, ds, dl, dr) =>
            Eq.subst.{1} Ty (fun (X : Ty) => Eq.{1} Ty (synth(l2)(Ctx.cons(fstSum(X), G2))) C2)
              (Ty.tsum A2 B2) (synth(s2)(G2))
              (Eq.symm.{1} Ty (synth(s2)(G2)) (Ty.tsum A2 B2) ds.rec)
              dl.rec
      }

    -- COMPLETENESS, part 2: the checker accepts everything the relation accepts —
    --   HasTy Γ e T → ok e Γ = true — by induction on the derivation. Each conjunct of
    -- `ok` is discharged from the induction hypotheses (`<field>.rec`) and `synth_complete`
    -- (every subterm synthesizes the type the relation assigns it), reassembled with
    -- `and_true` and `tyeq_of_eq`.
    def ok_complete (G : Ctx) (e : Exp) (T : Ty) (d : HasTy G e T) : Eq.{1} Bool (ok(e)(G)) Bool.true :=
      match d {
        | HasTy.tvar(G2, n2, T2, lk2) => inScope_complete G2 n2 T2 lk2
        | HasTy.tnat(G2, n2)          => Eq.refl.{1} Bool Bool.true
        | HasTy.tbool(G2, b2)         => Eq.refl.{1} Bool Bool.true
        | HasTy.tadd(G2, a2, b2, da, db) =>
            and_true (and(ok(a2)(G2), ok(b2)(G2)))
                     (and(tyeq(synth(a2)(G2))(Ty.tnat), tyeq(synth(b2)(G2))(Ty.tnat)))
              (and_true (ok(a2)(G2)) (ok(b2)(G2)) da.rec db.rec)
              (and_true (tyeq(synth(a2)(G2))(Ty.tnat)) (tyeq(synth(b2)(G2))(Ty.tnat))
                 (tyeq_of_eq (synth(a2)(G2)) Ty.tnat (synth_complete G2 a2 Ty.tnat da))
                 (tyeq_of_eq (synth(b2)(G2)) Ty.tnat (synth_complete G2 b2 Ty.tnat db)))
        | HasTy.tlet(G2, a2, body2, A2, B2, da, dbody) =>
            and_true (ok(a2)(G2)) (ok(body2)(Ctx.cons(synth(a2)(G2), G2)))
              da.rec
              (Eq.subst.{1} Ty (fun (X : Ty) => Eq.{1} Bool (ok(body2)(Ctx.cons(X, G2))) Bool.true)
                 A2 (synth(a2)(G2)) (Eq.symm.{1} Ty (synth(a2)(G2)) A2 (synth_complete G2 a2 A2 da))
                 dbody.rec)
        | HasTy.tlam(G2, A2, body2, B2, dbody) => dbody.rec
        | HasTy.tapp(G2, f2, a2, A2, B2, df, da) =>
            and_true (and(ok(f2)(G2), ok(a2)(G2)))
                     (and(isArrow(synth(f2)(G2)), tyeq(domOf(synth(f2)(G2)))(synth(a2)(G2))))
              (and_true (ok(f2)(G2)) (ok(a2)(G2)) df.rec da.rec)
              (and_true (isArrow(synth(f2)(G2))) (tyeq(domOf(synth(f2)(G2)))(synth(a2)(G2)))
                 (Eq.subst.{1} Ty (fun (t : Ty) => Eq.{1} Bool (isArrow(t)) Bool.true)
                    (Ty.tarrow A2 B2) (synth(f2)(G2))
                    (Eq.symm.{1} Ty (synth(f2)(G2)) (Ty.tarrow A2 B2) (synth_complete G2 f2 (Ty.tarrow A2 B2) df))
                    (Eq.refl.{1} Bool Bool.true))
                 (tyeq_of_eq (domOf(synth(f2)(G2))) (synth(a2)(G2))
                    (Eq.trans.{1} Ty (domOf(synth(f2)(G2))) A2 (synth(a2)(G2))
                       (Eq.subst.{1} Ty (fun (t : Ty) => Eq.{1} Ty (domOf(t)) A2)
                          (Ty.tarrow A2 B2) (synth(f2)(G2))
                          (Eq.symm.{1} Ty (synth(f2)(G2)) (Ty.tarrow A2 B2) (synth_complete G2 f2 (Ty.tarrow A2 B2) df))
                          (Eq.refl.{1} Ty A2))
                       (Eq.symm.{1} Ty (synth(a2)(G2)) A2 (synth_complete G2 a2 A2 da)))))
        | HasTy.tif(G2, cnd2, thn2, els2, T2, dc, dt, de) =>
            and_true (and(ok(cnd2)(G2), and(ok(thn2)(G2), ok(els2)(G2))))
                     (and(tyeq(synth(cnd2)(G2))(Ty.tbool), tyeq(synth(thn2)(G2))(synth(els2)(G2))))
              (and_true (ok(cnd2)(G2)) (and(ok(thn2)(G2), ok(els2)(G2)))
                 dc.rec
                 (and_true (ok(thn2)(G2)) (ok(els2)(G2)) dt.rec de.rec))
              (and_true (tyeq(synth(cnd2)(G2))(Ty.tbool)) (tyeq(synth(thn2)(G2))(synth(els2)(G2)))
                 (tyeq_of_eq (synth(cnd2)(G2)) Ty.tbool (synth_complete G2 cnd2 Ty.tbool dc))
                 (tyeq_of_eq (synth(thn2)(G2)) (synth(els2)(G2))
                    (Eq.trans.{1} Ty (synth(thn2)(G2)) T2 (synth(els2)(G2))
                       (synth_complete G2 thn2 T2 dt)
                       (Eq.symm.{1} Ty (synth(els2)(G2)) T2 (synth_complete G2 els2 T2 de)))))
        | HasTy.tfix(G2, A2, body2, dbody) =>
            and_true (ok(body2)(Ctx.cons(A2, G2))) (tyeq(synth(body2)(Ctx.cons(A2, G2)))(A2))
              dbody.rec
              (tyeq_of_eq (synth(body2)(Ctx.cons(A2, G2))) A2
                 (synth_complete (Ctx.cons A2 G2) body2 A2 dbody))
        | HasTy.tpair(G2, a2, b2, A2, B2, da, db) =>
            and_true (ok(a2)(G2)) (ok(b2)(G2)) da.rec db.rec
        | HasTy.tfst(G2, p2, A2, B2, dp) =>
            and_true (ok(p2)(G2)) (isProd(synth(p2)(G2)))
              dp.rec
              (Eq.subst.{1} Ty (fun (t : Ty) => Eq.{1} Bool (isProd(t)) Bool.true)
                 (Ty.tprod A2 B2) (synth(p2)(G2))
                 (Eq.symm.{1} Ty (synth(p2)(G2)) (Ty.tprod A2 B2) (synth_complete G2 p2 (Ty.tprod A2 B2) dp))
                 (Eq.refl.{1} Bool Bool.true))
        | HasTy.tsnd(G2, p2, A2, B2, dp) =>
            and_true (ok(p2)(G2)) (isProd(synth(p2)(G2)))
              dp.rec
              (Eq.subst.{1} Ty (fun (t : Ty) => Eq.{1} Bool (isProd(t)) Bool.true)
                 (Ty.tprod A2 B2) (synth(p2)(G2))
                 (Eq.symm.{1} Ty (synth(p2)(G2)) (Ty.tprod A2 B2) (synth_complete G2 p2 (Ty.tprod A2 B2) dp))
                 (Eq.refl.{1} Bool Bool.true))
        | HasTy.tinl(G2, B2, v2, A2, dv) => dv.rec
        | HasTy.tinr(G2, A2, v2, B2, dv) => dv.rec
        | HasTy.tcase(G2, s2, l2, r2, A2, B2, C2, ds, dl, dr) =>
            Eq.subst.{1} Ty
              (fun (X : Ty) => Eq.{1} Bool
                (and(and(ok(s2)(G2), isSum(X)),
                     and(ok(l2)(Ctx.cons(fstSum(X), G2)),
                         and(ok(r2)(Ctx.cons(sndSum(X), G2)),
                             tyeq(synth(l2)(Ctx.cons(fstSum(X), G2)))(synth(r2)(Ctx.cons(sndSum(X), G2))))))) Bool.true)
              (Ty.tsum A2 B2) (synth(s2)(G2))
              (Eq.symm.{1} Ty (synth(s2)(G2)) (Ty.tsum A2 B2) (synth_complete G2 s2 (Ty.tsum A2 B2) ds))
              (and_true (and(ok(s2)(G2), isSum(Ty.tsum A2 B2)))
                        (and(ok(l2)(Ctx.cons(fstSum(Ty.tsum A2 B2), G2)), and(ok(r2)(Ctx.cons(sndSum(Ty.tsum A2 B2), G2)), tyeq(synth(l2)(Ctx.cons(fstSum(Ty.tsum A2 B2), G2)))(synth(r2)(Ctx.cons(sndSum(Ty.tsum A2 B2), G2))))))
                 (and_true (ok(s2)(G2)) (isSum(Ty.tsum A2 B2)) ds.rec (Eq.refl.{1} Bool Bool.true))
                 (and_true (ok(l2)(Ctx.cons(fstSum(Ty.tsum A2 B2), G2))) (and(ok(r2)(Ctx.cons(sndSum(Ty.tsum A2 B2), G2)), tyeq(synth(l2)(Ctx.cons(fstSum(Ty.tsum A2 B2), G2)))(synth(r2)(Ctx.cons(sndSum(Ty.tsum A2 B2), G2)))))
                    dl.rec
                    (and_true (ok(r2)(Ctx.cons(sndSum(Ty.tsum A2 B2), G2))) (tyeq(synth(l2)(Ctx.cons(fstSum(Ty.tsum A2 B2), G2)))(synth(r2)(Ctx.cons(sndSum(Ty.tsum A2 B2), G2))))
                       dr.rec
                       (tyeq_of_eq (synth(l2)(Ctx.cons(fstSum(Ty.tsum A2 B2), G2))) (synth(r2)(Ctx.cons(sndSum(Ty.tsum A2 B2), G2)))
                          (Eq.trans.{1} Ty (synth(l2)(Ctx.cons(fstSum(Ty.tsum A2 B2), G2))) C2 (synth(r2)(Ctx.cons(sndSum(Ty.tsum A2 B2), G2)))
                             (synth_complete (Ctx.cons A2 G2) l2 C2 dl)
                             (Eq.symm.{1} Ty (synth(r2)(Ctx.cons(sndSum(Ty.tsum A2 B2), G2))) C2 (synth_complete (Ctx.cons B2 G2) r2 C2 dr)))))))
      }

    -- The headline: a term the checker REJECTS is genuinely untypable (no `HasTy`, any
    -- context, any type). Soundness + completeness ⇒ `ok` exactly DECIDES typability.
    def ok_false_not_welltyped (G : Ctx) (e : Exp) (T : Ty)
        (hf : Eq.{1} Bool (ok(e)(G)) Bool.false) (d : HasTy G e T) : False :=
      ff_ne_tt (Eq.trans.{1} Bool Bool.false (ok(e)(G)) Bool.true
                  (Eq.symm.{1} Bool (ok(e)(G)) Bool.false hf)
                  (ok_complete G e T d))
"#;

/// The **operational semantics**: a call-by-value, substitution-based small-step
/// evaluator (`isValue`, de Bruijn `shift`/`subst`, `step`, and a fuel-driven `run`).
/// This is what lets the language *run* — concrete typed programs reduce to values, and
/// the kernel computes the result. (Type *safety* relating this to the checker — progress
/// + preservation — is the next layer.)
pub const DYNAMICS: &str = r#"
    -- Nat helpers for de Bruijn index arithmetic and the `eadd` reduction.
    fn pred(n: Nat) -> Nat { match n { | Nat.zero => Nat.zero | Nat.succ(k) => k } }
    fn addN(m: Nat) -> (Nat -> Nat) {
        match m { | Nat.zero => fun (n : Nat) => n | Nat.succ(k) => fun (n : Nat) => Nat.succ(addN(k)(n)) }
    }
    fn nat_eqb(m: Nat) -> (Nat -> Bool) {
        match m {
          | Nat.zero    => fun (n : Nat) => match n { | Nat.zero => Bool.true  | Nat.succ(k) => Bool.false }
          | Nat.succ(j) => fun (n : Nat) => match n { | Nat.zero => Bool.false | Nat.succ(k) => nat_eqb(j)(k) }
        }
    }
    fn nat_ltb(m: Nat) -> (Nat -> Bool) {
        match m {
          | Nat.zero    => fun (n : Nat) => match n { | Nat.zero => Bool.false | Nat.succ(k) => Bool.true }
          | Nat.succ(j) => fun (n : Nat) => match n { | Nat.zero => Bool.false | Nat.succ(k) => nat_ltb(j)(k) }
        }
    }

    -- The value predicate (literals and λ are values).
    fn isValue(e: Exp) -> Bool {
        match e {
          | Exp.evar(n)            => Bool.false
          | Exp.enat(n)            => Bool.true
          | Exp.ebool(b)           => Bool.true
          | Exp.eadd(a, b)         => Bool.false
          | Exp.elet(a, body)      => Bool.false
          | Exp.elam(A, body)      => Bool.true
          | Exp.eapp(f, a)         => Bool.false
          | Exp.eif(cnd, thn, els) => Bool.false
          | Exp.efix(A, body)      => Bool.false
          | Exp.epair(a, b)        => Bool.true
          | Exp.efst(p)            => Bool.false
          | Exp.esnd(p)            => Bool.false
          | Exp.einl(B, v)         => Bool.true
          | Exp.einr(A, v)         => Bool.true
          | Exp.ecase(s, l, r)     => Bool.false
        }
    }

    -- de Bruijn index shift (recursive form, so its laws hold definitionally):
    -- shiftIdx k n = n if n < k, else succ n.
    fn shiftIdx(k: Nat) -> (Nat -> Nat) {
        match k {
          | Nat.zero    => fun (n : Nat) => Nat.succ(n)
          | Nat.succ(k2) => fun (n : Nat) =>
              match n { | Nat.zero => Nat.zero | Nat.succ(n2) => Nat.succ(shiftIdx(k2)(n2)) }
        }
    }

    -- de Bruijn shift: lift free variables (index ≥ cutoff) by one, under binders.
    fn shift(e: Exp) -> (Nat -> Exp) {
        match e {
          | Exp.evar(n) => fun (c : Nat) => Exp.evar(shiftIdx(c)(n))
          | Exp.enat(n)  => fun (c : Nat) => Exp.enat(n)
          | Exp.ebool(b) => fun (c : Nat) => Exp.ebool(b)
          | Exp.eadd(a, b) => fun (c : Nat) => Exp.eadd(shift(a)(c), shift(b)(c))
          | Exp.elet(a, body) => fun (c : Nat) => Exp.elet(shift(a)(c), shift(body)(Nat.succ(c)))
          | Exp.elam(A, body) => fun (c : Nat) => Exp.elam(A, shift(body)(Nat.succ(c)))
          | Exp.eapp(f, a) => fun (c : Nat) => Exp.eapp(shift(f)(c), shift(a)(c))
          | Exp.eif(cnd, thn, els) => fun (c : Nat) => Exp.eif(shift(cnd)(c), shift(thn)(c), shift(els)(c))
          | Exp.efix(A, body) => fun (c : Nat) => Exp.efix(A, shift(body)(Nat.succ(c)))
          | Exp.epair(a, b) => fun (c : Nat) => Exp.epair(shift(a)(c), shift(b)(c))
          | Exp.efst(p) => fun (c : Nat) => Exp.efst(shift(p)(c))
          | Exp.esnd(p) => fun (c : Nat) => Exp.esnd(shift(p)(c))
          | Exp.einl(B, v) => fun (c : Nat) => Exp.einl(B, shift(v)(c))
          | Exp.einr(A, v) => fun (c : Nat) => Exp.einr(A, shift(v)(c))
          | Exp.ecase(s, l, r) => fun (c : Nat) => Exp.ecase(shift(s)(c), shift(l)(Nat.succ(c)), shift(r)(Nat.succ(c)))
        }
    }

    -- **Parallel substitution.** A substitution is a function `Nat -> Exp` (an assignment
    -- to every free variable). `applySub` applies it, lifting under binders. Single-variable
    -- substitution is the special case `subst e j v = applySub e (atSubj j v)`. Phrasing the
    -- substitution operation this way is what makes the typed substitution lemma provable
    -- over the *original* (matchable) context (see `PRESERVATION`).
    def liftSub (s : Nat -> Exp) (n : Nat) : Exp :=
      match n { | Nat.zero => Exp.evar(Nat.zero) | Nat.succ(m) => shift(s(m))(Nat.zero) }
    fn applySub(e: Exp) -> ((Nat -> Exp) -> Exp) {
        match e {
          | Exp.evar(n)  => fun (s : Nat -> Exp) => s(n)
          | Exp.enat(n)  => fun (s : Nat -> Exp) => Exp.enat(n)
          | Exp.ebool(b) => fun (s : Nat -> Exp) => Exp.ebool(b)
          | Exp.eadd(a, b) => fun (s : Nat -> Exp) => Exp.eadd(applySub(a)(s), applySub(b)(s))
          | Exp.elet(a, body) => fun (s : Nat -> Exp) => Exp.elet(applySub(a)(s), applySub(body)(liftSub(s)))
          | Exp.elam(A, body) => fun (s : Nat -> Exp) => Exp.elam(A, applySub(body)(liftSub(s)))
          | Exp.eapp(f, a) => fun (s : Nat -> Exp) => Exp.eapp(applySub(f)(s), applySub(a)(s))
          | Exp.eif(cnd, thn, els) => fun (s : Nat -> Exp) => Exp.eif(applySub(cnd)(s), applySub(thn)(s), applySub(els)(s))
          | Exp.efix(A, body) => fun (s : Nat -> Exp) => Exp.efix(A, applySub(body)(liftSub(s)))
          | Exp.epair(a, b) => fun (s : Nat -> Exp) => Exp.epair(applySub(a)(s), applySub(b)(s))
          | Exp.efst(p) => fun (s : Nat -> Exp) => Exp.efst(applySub(p)(s))
          | Exp.esnd(p) => fun (s : Nat -> Exp) => Exp.esnd(applySub(p)(s))
          | Exp.einl(B, v) => fun (s : Nat -> Exp) => Exp.einl(B, applySub(v)(s))
          | Exp.einr(A, v) => fun (s : Nat -> Exp) => Exp.einr(A, applySub(v)(s))
          | Exp.ecase(sc, l, r) => fun (s : Nat -> Exp) => Exp.ecase(applySub(sc)(s), applySub(l)(liftSub(s)), applySub(r)(liftSub(s)))
        }
    }
    -- The single-substitution assignment: variable `j` ↦ `v`, decrement above, identity below.
    def atSubj (j : Nat) (v : Exp) (n : Nat) : Exp :=
      match nat_eqb(n)(j) {
        | Bool.true  => v
        | Bool.false => match nat_ltb(j)(n) { | Bool.true => Exp.evar(pred(n)) | Bool.false => Exp.evar(n) }
      }
    def subst (e : Exp) (j : Nat) (v : Exp) : Exp := applySub(e)(atSubj(j)(v))

    -- A step result: either a reduced term or "no step" (a value or a stuck term).
    inductive OExp : Type | onone : OExp | osome : Exp -> OExp
    def omap (f : Exp -> Exp) (o : OExp) : OExp :=
      match o { | OExp.onone => OExp.onone | OExp.osome(e) => OExp.osome(f e) }

    -- Call-by-value small-step reduction.
    fn step(e: Exp) -> OExp {
        match e {
          | Exp.evar(n)  => OExp.onone
          | Exp.enat(n)  => OExp.onone
          | Exp.ebool(b) => OExp.onone
          | Exp.elam(A, body) => OExp.onone
          | Exp.eadd(a, b) =>
              match isValue(a) {
                | Bool.false => omap(fun (a2 : Exp) => Exp.eadd(a2, b))(step(a))
                | Bool.true  => match isValue(b) {
                    | Bool.false => omap(fun (b2 : Exp) => Exp.eadd(a, b2))(step(b))
                    | Bool.true  => match a {
                        | Exp.enat(m) => match b { | Exp.enat(n) => OExp.osome(Exp.enat(addN(m)(n))) | _ => OExp.onone }
                        | _ => OExp.onone
                      }
                  }
              }
          | Exp.elet(a, body) =>
              match isValue(a) {
                | Bool.false => omap(fun (a2 : Exp) => Exp.elet(a2, body))(step(a))
                | Bool.true  => OExp.osome(subst(body)(Nat.zero)(a))
              }
          | Exp.eapp(f, a) =>
              match isValue(f) {
                | Bool.false => omap(fun (f2 : Exp) => Exp.eapp(f2, a))(step(f))
                | Bool.true  => match isValue(a) {
                    | Bool.false => omap(fun (a2 : Exp) => Exp.eapp(f, a2))(step(a))
                    | Bool.true  => match f { | Exp.elam(A, body) => OExp.osome(subst(body)(Nat.zero)(a)) | _ => OExp.onone }
                  }
              }
          | Exp.eif(cnd, thn, els) =>
              match isValue(cnd) {
                | Bool.false => omap(fun (c2 : Exp) => Exp.eif(c2, thn, els))(step(cnd))
                | Bool.true  => match cnd {
                    | Exp.ebool(b) => match b { | Bool.true => OExp.osome(thn) | Bool.false => OExp.osome(els) }
                    | _ => OExp.onone
                  }
              }
          | Exp.efix(A, body) => OExp.osome(subst(body)(Nat.zero)(Exp.efix(A, body)))
          | Exp.epair(a, b) => OExp.onone
          | Exp.efst(p) =>
              match isValue(p) {
                | Bool.false => omap(fun (p2 : Exp) => Exp.efst(p2))(step(p))
                | Bool.true  => match p { | Exp.epair(a, b) => OExp.osome(a) | _ => OExp.onone }
              }
          | Exp.esnd(p) =>
              match isValue(p) {
                | Bool.false => omap(fun (p2 : Exp) => Exp.esnd(p2))(step(p))
                | Bool.true  => match p { | Exp.epair(a, b) => OExp.osome(b) | _ => OExp.onone }
              }
          | Exp.einl(B, v) => OExp.onone
          | Exp.einr(A, v) => OExp.onone
          | Exp.ecase(s, l, r) =>
              match isValue(s) {
                | Bool.false => omap(fun (s2 : Exp) => Exp.ecase(s2, l, r))(step(s))
                | Bool.true  => match s {
                    | Exp.einl(B, v) => OExp.osome(subst(l)(Nat.zero)(v))
                    | Exp.einr(A, v) => OExp.osome(subst(r)(Nat.zero)(v))
                    | _ => OExp.onone
                  }
              }
        }
    }

    -- Run to a value (or stuck term) within a fuel budget — the evaluator's driver.
    fn run(fuel: Nat) -> (Exp -> Exp) {
        match fuel {
          | Nat.zero    => fun (e : Exp) => e
          | Nat.succ(k) => fun (e : Exp) =>
              match step(e) { | OExp.onone => e | OExp.osome(e2) => run(k)(e2) }
        }
    }
"#;

/// A session with the prelude and the simply-typed λ-calculus + checker + soundness all
/// loaded and kernel-checked.
pub fn session() -> Result<Session, String> {
    let mut s = Session::new();
    s.run(PRELUDE)?;
    s.run(LANG)?;
    Ok(s)
}

/// A session that additionally loads the [`DYNAMICS`] (the evaluator), so programs can be
/// *run*, not just type-checked.
pub fn runnable_session() -> Result<Session, String> {
    let mut s = session()?;
    s.run(DYNAMICS)?;
    Ok(s)
}

/// **Type-safety scaffolding**: the structural predicates, value/term inversions, and the
/// **canonical forms** lemmas that `progress` is built from — all verified Raven.
///
/// Canonical forms (`canon_arrow`/`canon_nat`/`canon_bool`) say a well-typed *value* has
/// the shape its type dictates. They're stated with the value/type side-conditions as
/// hypotheses in the *return type* (so each constructor case specialises them via the
/// motive) — that sidesteps needing dependent inversion on concrete indices.
pub const SAFETY_SCAFFOLD: &str = r#"
    inductive Or (a : Prop) (b : Prop) : Prop | inl : a -> Or a b | inr : b -> Or a b

    -- Boolean disjunction + the elimination we need (left-false ⇒ right-true).
    fn orB(x: Bool) -> (Bool -> Bool) {
        match x { | Bool.true => fun (y : Bool) => Bool.true | Bool.false => fun (y : Bool) => y }
    }
    def orB_false_left (x : Bool) (y : Bool)
        : Eq.{1} Bool (orB(x)(y)) Bool.true -> Eq.{1} Bool x Bool.false -> Eq.{1} Bool y Bool.true :=
      match x {
        | Bool.true  => fun (h : Eq.{1} Bool (orB(Bool.true)(y)) Bool.true) (hxf : Eq.{1} Bool Bool.true Bool.false) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Bool y Bool.true)
              (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false hxf))
        | Bool.false => fun (h : Eq.{1} Bool (orB(Bool.false)(y)) Bool.true) (hxf : Eq.{1} Bool Bool.false Bool.false) => h
      }

    -- Case analysis on an (opaque) Bool, as a disjunction of equations.
    def bool_cases (b : Bool) : Or (Eq.{1} Bool b Bool.true) (Eq.{1} Bool b Bool.false) :=
      match b {
        | Bool.true  => Or.inl (Eq.{1} Bool Bool.true Bool.true) (Eq.{1} Bool Bool.true Bool.false) (Eq.refl.{1} Bool Bool.true)
        | Bool.false => Or.inr (Eq.{1} Bool Bool.false Bool.true) (Eq.{1} Bool Bool.false Bool.false) (Eq.refl.{1} Bool Bool.false)
      }

    -- Structural predicates used by canonical forms / progress.
    fn isNil(G: Ctx) -> Bool { match G { | Ctx.nil => Bool.true | _ => Bool.false } }
    fn isLam(e: Exp) -> Bool { match e { | Exp.elam(A, body) => Bool.true | _ => Bool.false } }
    fn isNatLit(e: Exp) -> Bool { match e { | Exp.enat(n) => Bool.true | _ => Bool.false } }
    fn isBoolLit(e: Exp) -> Bool { match e { | Exp.ebool(b) => Bool.true | _ => Bool.false } }
    fn isPair(e: Exp) -> Bool { match e { | Exp.epair(a, b) => Bool.true | _ => Bool.false } }
    fn isInl(e: Exp) -> Bool { match e { | Exp.einl(B, v) => Bool.true | _ => Bool.false } }
    fn isInr(e: Exp) -> Bool { match e { | Exp.einr(A, v) => Bool.true | _ => Bool.false } }
    fn isTnat(t: Ty) -> Bool { match t { | Ty.tnat => Bool.true | _ => Bool.false } }
    fn isTbool(t: Ty) -> Bool { match t { | Ty.tbool => Bool.true | _ => Bool.false } }
    fn isSome(o: OExp) -> Bool { match o { | OExp.osome(e) => Bool.true | _ => Bool.false } }

    -- `omap` preserves some/none, so it preserves "can step".
    def isSome_omap (f : Exp -> Exp) (o : OExp) : Eq.{1} Bool (isSome(omap f o)) (isSome(o)) :=
      match o {
        | OExp.onone    => Eq.refl.{1} Bool Bool.false
        | OExp.osome(e) => Eq.refl.{1} Bool Bool.true
      }

    -- Extractors + value inversions: a term that tests as a literal/λ really is one.
    fn natOf(e: Exp) -> Nat { match e { | Exp.enat(n) => n | _ => Nat.zero } }
    fn boolOf(e: Exp) -> Bool { match e { | Exp.ebool(b) => b | _ => Bool.false } }
    fn lamTyOf(e: Exp) -> Ty { match e { | Exp.elam(A, body) => A | _ => Ty.tnat } }
    fn lamBodyOf(e: Exp) -> Exp { match e { | Exp.elam(A, body) => body | _ => Exp.enat(Nat.zero) } }
    fn fstOf(e: Exp) -> Exp { match e { | Exp.epair(a, b) => a | _ => Exp.enat(Nat.zero) } }
    fn sndOf(e: Exp) -> Exp { match e { | Exp.epair(a, b) => b | _ => Exp.enat(Nat.zero) } }
    fn inlTyOf(e: Exp) -> Ty { match e { | Exp.einl(B, v) => B | _ => Ty.tnat } }
    fn inlValOf(e: Exp) -> Exp { match e { | Exp.einl(B, v) => v | _ => Exp.enat(Nat.zero) } }
    fn inrTyOf(e: Exp) -> Ty { match e { | Exp.einr(A, v) => A | _ => Ty.tnat } }
    fn inrValOf(e: Exp) -> Exp { match e { | Exp.einr(A, v) => v | _ => Exp.enat(Nat.zero) } }
    def natlit_inv (e : Exp) : Eq.{1} Bool (isNatLit(e)) Bool.true -> Eq.{1} Exp e (Exp.enat (natOf(e))) :=
      match e {
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isNatLit(Exp.enat(n))) Bool.true) => Eq.refl.{1} Exp (Exp.enat n)
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isNatLit(Exp.evar(n))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.evar n) (Exp.enat (natOf(Exp.evar(n))))) (ff_ne_tt h)
        | Exp.ebool(b) => fun (h : Eq.{1} Bool (isNatLit(Exp.ebool(b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ebool b) (Exp.enat (natOf(Exp.ebool(b))))) (ff_ne_tt h)
        | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (isNatLit(Exp.eadd(a, b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eadd a b) (Exp.enat (natOf(Exp.eadd(a, b))))) (ff_ne_tt h)
        | Exp.elet(a, body) => fun (h : Eq.{1} Bool (isNatLit(Exp.elet(a, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elet a body) (Exp.enat (natOf(Exp.elet(a, body))))) (ff_ne_tt h)
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isNatLit(Exp.elam(A, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elam A body) (Exp.enat (natOf(Exp.elam(A, body))))) (ff_ne_tt h)
        | Exp.eapp(f, a) => fun (h : Eq.{1} Bool (isNatLit(Exp.eapp(f, a))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eapp f a) (Exp.enat (natOf(Exp.eapp(f, a))))) (ff_ne_tt h)
        | Exp.eif(cnd, thn, els) => fun (h : Eq.{1} Bool (isNatLit(Exp.eif(cnd, thn, els))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eif cnd thn els) (Exp.enat (natOf(Exp.eif(cnd, thn, els))))) (ff_ne_tt h)
        | Exp.efix(A, body) => fun (h : Eq.{1} Bool (isNatLit(Exp.efix(A, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efix A body) (Exp.enat (natOf(Exp.efix(A, body))))) (ff_ne_tt h)
        | Exp.epair(a, b) => fun (h : Eq.{1} Bool (isNatLit(Exp.epair(a, b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.epair a b) (Exp.enat (natOf(Exp.epair(a, b))))) (ff_ne_tt h)
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isNatLit(Exp.efst(p))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efst p) (Exp.enat (natOf(Exp.efst(p))))) (ff_ne_tt h)
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isNatLit(Exp.esnd(p))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.esnd p) (Exp.enat (natOf(Exp.esnd(p))))) (ff_ne_tt h)
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isNatLit(Exp.einl(B, v))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einl B v) (Exp.enat (natOf(Exp.einl(B, v))))) (ff_ne_tt h)
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isNatLit(Exp.einr(A, v))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einr A v) (Exp.enat (natOf(Exp.einr(A, v))))) (ff_ne_tt h)
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isNatLit(Exp.ecase(s, l, r))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ecase s l r) (Exp.enat (natOf(Exp.ecase(s, l, r))))) (ff_ne_tt h)
      }
    def boollit_inv (e : Exp) : Eq.{1} Bool (isBoolLit(e)) Bool.true -> Eq.{1} Exp e (Exp.ebool (boolOf(e))) :=
      match e {
        | Exp.ebool(b) => fun (h : Eq.{1} Bool (isBoolLit(Exp.ebool(b))) Bool.true) => Eq.refl.{1} Exp (Exp.ebool b)
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isBoolLit(Exp.evar(n))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.evar n) (Exp.ebool (boolOf(Exp.evar(n))))) (ff_ne_tt h)
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isBoolLit(Exp.enat(n))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.enat n) (Exp.ebool (boolOf(Exp.enat(n))))) (ff_ne_tt h)
        | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (isBoolLit(Exp.eadd(a, b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eadd a b) (Exp.ebool (boolOf(Exp.eadd(a, b))))) (ff_ne_tt h)
        | Exp.elet(a, body) => fun (h : Eq.{1} Bool (isBoolLit(Exp.elet(a, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elet a body) (Exp.ebool (boolOf(Exp.elet(a, body))))) (ff_ne_tt h)
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isBoolLit(Exp.elam(A, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elam A body) (Exp.ebool (boolOf(Exp.elam(A, body))))) (ff_ne_tt h)
        | Exp.eapp(f, a) => fun (h : Eq.{1} Bool (isBoolLit(Exp.eapp(f, a))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eapp f a) (Exp.ebool (boolOf(Exp.eapp(f, a))))) (ff_ne_tt h)
        | Exp.eif(cnd, thn, els) => fun (h : Eq.{1} Bool (isBoolLit(Exp.eif(cnd, thn, els))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eif cnd thn els) (Exp.ebool (boolOf(Exp.eif(cnd, thn, els))))) (ff_ne_tt h)
        | Exp.efix(A, body) => fun (h : Eq.{1} Bool (isBoolLit(Exp.efix(A, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efix A body) (Exp.ebool (boolOf(Exp.efix(A, body))))) (ff_ne_tt h)
        | Exp.epair(a, b) => fun (h : Eq.{1} Bool (isBoolLit(Exp.epair(a, b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.epair a b) (Exp.ebool (boolOf(Exp.epair(a, b))))) (ff_ne_tt h)
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isBoolLit(Exp.efst(p))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efst p) (Exp.ebool (boolOf(Exp.efst(p))))) (ff_ne_tt h)
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isBoolLit(Exp.esnd(p))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.esnd p) (Exp.ebool (boolOf(Exp.esnd(p))))) (ff_ne_tt h)
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isBoolLit(Exp.einl(B, v))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einl B v) (Exp.ebool (boolOf(Exp.einl(B, v))))) (ff_ne_tt h)
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isBoolLit(Exp.einr(A, v))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einr A v) (Exp.ebool (boolOf(Exp.einr(A, v))))) (ff_ne_tt h)
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isBoolLit(Exp.ecase(s, l, r))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ecase s l r) (Exp.ebool (boolOf(Exp.ecase(s, l, r))))) (ff_ne_tt h)
      }
    def lam_inv (e : Exp) : Eq.{1} Bool (isLam(e)) Bool.true -> Eq.{1} Exp e (Exp.elam (lamTyOf(e)) (lamBodyOf(e))) :=
      match e {
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isLam(Exp.elam(A, body))) Bool.true) => Eq.refl.{1} Exp (Exp.elam A body)
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isLam(Exp.evar(n))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.evar n) (Exp.elam (lamTyOf(Exp.evar(n))) (lamBodyOf(Exp.evar(n))))) (ff_ne_tt h)
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isLam(Exp.enat(n))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.enat n) (Exp.elam (lamTyOf(Exp.enat(n))) (lamBodyOf(Exp.enat(n))))) (ff_ne_tt h)
        | Exp.ebool(b) => fun (h : Eq.{1} Bool (isLam(Exp.ebool(b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ebool b) (Exp.elam (lamTyOf(Exp.ebool(b))) (lamBodyOf(Exp.ebool(b))))) (ff_ne_tt h)
        | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (isLam(Exp.eadd(a, b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eadd a b) (Exp.elam (lamTyOf(Exp.eadd(a, b))) (lamBodyOf(Exp.eadd(a, b))))) (ff_ne_tt h)
        | Exp.elet(a, body) => fun (h : Eq.{1} Bool (isLam(Exp.elet(a, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elet a body) (Exp.elam (lamTyOf(Exp.elet(a, body))) (lamBodyOf(Exp.elet(a, body))))) (ff_ne_tt h)
        | Exp.eapp(f, a) => fun (h : Eq.{1} Bool (isLam(Exp.eapp(f, a))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eapp f a) (Exp.elam (lamTyOf(Exp.eapp(f, a))) (lamBodyOf(Exp.eapp(f, a))))) (ff_ne_tt h)
        | Exp.eif(cnd, thn, els) => fun (h : Eq.{1} Bool (isLam(Exp.eif(cnd, thn, els))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eif cnd thn els) (Exp.elam (lamTyOf(Exp.eif(cnd, thn, els))) (lamBodyOf(Exp.eif(cnd, thn, els))))) (ff_ne_tt h)
        | Exp.efix(A, body) => fun (h : Eq.{1} Bool (isLam(Exp.efix(A, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efix A body) (Exp.elam (lamTyOf(Exp.efix(A, body))) (lamBodyOf(Exp.efix(A, body))))) (ff_ne_tt h)
        | Exp.epair(a, b) => fun (h : Eq.{1} Bool (isLam(Exp.epair(a, b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.epair a b) (Exp.elam (lamTyOf(Exp.epair(a, b))) (lamBodyOf(Exp.epair(a, b))))) (ff_ne_tt h)
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isLam(Exp.efst(p))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efst p) (Exp.elam (lamTyOf(Exp.efst(p))) (lamBodyOf(Exp.efst(p))))) (ff_ne_tt h)
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isLam(Exp.esnd(p))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.esnd p) (Exp.elam (lamTyOf(Exp.esnd(p))) (lamBodyOf(Exp.esnd(p))))) (ff_ne_tt h)
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isLam(Exp.einl(B, v))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einl B v) (Exp.elam (lamTyOf(Exp.einl(B, v))) (lamBodyOf(Exp.einl(B, v))))) (ff_ne_tt h)
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isLam(Exp.einr(A, v))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einr A v) (Exp.elam (lamTyOf(Exp.einr(A, v))) (lamBodyOf(Exp.einr(A, v))))) (ff_ne_tt h)
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isLam(Exp.ecase(s, l, r))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ecase s l r) (Exp.elam (lamTyOf(Exp.ecase(s, l, r))) (lamBodyOf(Exp.ecase(s, l, r))))) (ff_ne_tt h)
      }

    def pair_inv (e : Exp) : Eq.{1} Bool (isPair(e)) Bool.true -> Eq.{1} Exp e (Exp.epair (fstOf(e)) (sndOf(e))) :=
      match e {
        | Exp.epair(a, b) => fun (h : Eq.{1} Bool (isPair(Exp.epair(a, b))) Bool.true) => Eq.refl.{1} Exp (Exp.epair a b)
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isPair(Exp.evar(n))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.evar n) (Exp.epair (fstOf(Exp.evar(n))) (sndOf(Exp.evar(n))))) (ff_ne_tt h)
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isPair(Exp.enat(n))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.enat n) (Exp.epair (fstOf(Exp.enat(n))) (sndOf(Exp.enat(n))))) (ff_ne_tt h)
        | Exp.ebool(b) => fun (h : Eq.{1} Bool (isPair(Exp.ebool(b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ebool b) (Exp.epair (fstOf(Exp.ebool(b))) (sndOf(Exp.ebool(b))))) (ff_ne_tt h)
        | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (isPair(Exp.eadd(a, b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eadd a b) (Exp.epair (fstOf(Exp.eadd(a, b))) (sndOf(Exp.eadd(a, b))))) (ff_ne_tt h)
        | Exp.elet(a, b) => fun (h : Eq.{1} Bool (isPair(Exp.elet(a, b))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elet a b) (Exp.epair (fstOf(Exp.elet(a, b))) (sndOf(Exp.elet(a, b))))) (ff_ne_tt h)
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isPair(Exp.elam(A, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elam A body) (Exp.epair (fstOf(Exp.elam(A, body))) (sndOf(Exp.elam(A, body))))) (ff_ne_tt h)
        | Exp.eapp(f, a) => fun (h : Eq.{1} Bool (isPair(Exp.eapp(f, a))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eapp f a) (Exp.epair (fstOf(Exp.eapp(f, a))) (sndOf(Exp.eapp(f, a))))) (ff_ne_tt h)
        | Exp.eif(cnd, thn, els) => fun (h : Eq.{1} Bool (isPair(Exp.eif(cnd, thn, els))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eif cnd thn els) (Exp.epair (fstOf(Exp.eif(cnd, thn, els))) (sndOf(Exp.eif(cnd, thn, els))))) (ff_ne_tt h)
        | Exp.efix(A, body) => fun (h : Eq.{1} Bool (isPair(Exp.efix(A, body))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efix A body) (Exp.epair (fstOf(Exp.efix(A, body))) (sndOf(Exp.efix(A, body))))) (ff_ne_tt h)
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isPair(Exp.efst(p))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efst p) (Exp.epair (fstOf(Exp.efst(p))) (sndOf(Exp.efst(p))))) (ff_ne_tt h)
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isPair(Exp.esnd(p))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.esnd p) (Exp.epair (fstOf(Exp.esnd(p))) (sndOf(Exp.esnd(p))))) (ff_ne_tt h)
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isPair(Exp.einl(B, v))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einl B v) (Exp.epair (fstOf(Exp.einl(B, v))) (sndOf(Exp.einl(B, v))))) (ff_ne_tt h)
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isPair(Exp.einr(A, v))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einr A v) (Exp.epair (fstOf(Exp.einr(A, v))) (sndOf(Exp.einr(A, v))))) (ff_ne_tt h)
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isPair(Exp.ecase(s, l, r))) Bool.true) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ecase s l r) (Exp.epair (fstOf(Exp.ecase(s, l, r))) (sndOf(Exp.ecase(s, l, r))))) (ff_ne_tt h)
      }
    def inl_inv (e : Exp) : Eq.{1} Bool (isInl(e)) Bool.true -> Eq.{1} Exp e (Exp.einl (inlTyOf(e)) (inlValOf(e))) :=
      match e {
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isInl(Exp.einl(B, v))) Bool.true) => Eq.refl.{1} Exp (Exp.einl B v)
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isInl(Exp.evar(n))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.evar n) (Exp.einl (inlTyOf(Exp.evar(n))) (inlValOf(Exp.evar(n))))) (ff_ne_tt h)
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isInl(Exp.enat(n))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.enat n) (Exp.einl (inlTyOf(Exp.enat(n))) (inlValOf(Exp.enat(n))))) (ff_ne_tt h)
        | Exp.ebool(b) => fun (h : Eq.{1} Bool (isInl(Exp.ebool(b))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ebool b) (Exp.einl (inlTyOf(Exp.ebool(b))) (inlValOf(Exp.ebool(b))))) (ff_ne_tt h)
        | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (isInl(Exp.eadd(a, b))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eadd a b) (Exp.einl (inlTyOf(Exp.eadd(a, b))) (inlValOf(Exp.eadd(a, b))))) (ff_ne_tt h)
        | Exp.elet(a, b) => fun (h : Eq.{1} Bool (isInl(Exp.elet(a, b))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elet a b) (Exp.einl (inlTyOf(Exp.elet(a, b))) (inlValOf(Exp.elet(a, b))))) (ff_ne_tt h)
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isInl(Exp.elam(A, body))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elam A body) (Exp.einl (inlTyOf(Exp.elam(A, body))) (inlValOf(Exp.elam(A, body))))) (ff_ne_tt h)
        | Exp.eapp(f, a) => fun (h : Eq.{1} Bool (isInl(Exp.eapp(f, a))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eapp f a) (Exp.einl (inlTyOf(Exp.eapp(f, a))) (inlValOf(Exp.eapp(f, a))))) (ff_ne_tt h)
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isInl(Exp.eif(c, t, el))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eif c t el) (Exp.einl (inlTyOf(Exp.eif(c, t, el))) (inlValOf(Exp.eif(c, t, el))))) (ff_ne_tt h)
        | Exp.efix(A, body) => fun (h : Eq.{1} Bool (isInl(Exp.efix(A, body))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efix A body) (Exp.einl (inlTyOf(Exp.efix(A, body))) (inlValOf(Exp.efix(A, body))))) (ff_ne_tt h)
        | Exp.epair(a, b) => fun (h : Eq.{1} Bool (isInl(Exp.epair(a, b))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.epair a b) (Exp.einl (inlTyOf(Exp.epair(a, b))) (inlValOf(Exp.epair(a, b))))) (ff_ne_tt h)
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isInl(Exp.efst(p))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efst p) (Exp.einl (inlTyOf(Exp.efst(p))) (inlValOf(Exp.efst(p))))) (ff_ne_tt h)
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isInl(Exp.esnd(p))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.esnd p) (Exp.einl (inlTyOf(Exp.esnd(p))) (inlValOf(Exp.esnd(p))))) (ff_ne_tt h)
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isInl(Exp.einr(A, v))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einr A v) (Exp.einl (inlTyOf(Exp.einr(A, v))) (inlValOf(Exp.einr(A, v))))) (ff_ne_tt h)
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isInl(Exp.ecase(s, l, r))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ecase s l r) (Exp.einl (inlTyOf(Exp.ecase(s, l, r))) (inlValOf(Exp.ecase(s, l, r))))) (ff_ne_tt h)
      }
    def inr_inv (e : Exp) : Eq.{1} Bool (isInr(e)) Bool.true -> Eq.{1} Exp e (Exp.einr (inrTyOf(e)) (inrValOf(e))) :=
      match e {
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isInr(Exp.einr(A, v))) Bool.true) => Eq.refl.{1} Exp (Exp.einr A v)
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isInr(Exp.evar(n))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.evar n) (Exp.einr (inrTyOf(Exp.evar(n))) (inrValOf(Exp.evar(n))))) (ff_ne_tt h)
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isInr(Exp.enat(n))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.enat n) (Exp.einr (inrTyOf(Exp.enat(n))) (inrValOf(Exp.enat(n))))) (ff_ne_tt h)
        | Exp.ebool(b) => fun (h : Eq.{1} Bool (isInr(Exp.ebool(b))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ebool b) (Exp.einr (inrTyOf(Exp.ebool(b))) (inrValOf(Exp.ebool(b))))) (ff_ne_tt h)
        | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (isInr(Exp.eadd(a, b))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eadd a b) (Exp.einr (inrTyOf(Exp.eadd(a, b))) (inrValOf(Exp.eadd(a, b))))) (ff_ne_tt h)
        | Exp.elet(a, b) => fun (h : Eq.{1} Bool (isInr(Exp.elet(a, b))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elet a b) (Exp.einr (inrTyOf(Exp.elet(a, b))) (inrValOf(Exp.elet(a, b))))) (ff_ne_tt h)
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isInr(Exp.elam(A, body))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.elam A body) (Exp.einr (inrTyOf(Exp.elam(A, body))) (inrValOf(Exp.elam(A, body))))) (ff_ne_tt h)
        | Exp.eapp(f, a) => fun (h : Eq.{1} Bool (isInr(Exp.eapp(f, a))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eapp f a) (Exp.einr (inrTyOf(Exp.eapp(f, a))) (inrValOf(Exp.eapp(f, a))))) (ff_ne_tt h)
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isInr(Exp.eif(c, t, el))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.eif c t el) (Exp.einr (inrTyOf(Exp.eif(c, t, el))) (inrValOf(Exp.eif(c, t, el))))) (ff_ne_tt h)
        | Exp.efix(A, body) => fun (h : Eq.{1} Bool (isInr(Exp.efix(A, body))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efix A body) (Exp.einr (inrTyOf(Exp.efix(A, body))) (inrValOf(Exp.efix(A, body))))) (ff_ne_tt h)
        | Exp.epair(a, b) => fun (h : Eq.{1} Bool (isInr(Exp.epair(a, b))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.epair a b) (Exp.einr (inrTyOf(Exp.epair(a, b))) (inrValOf(Exp.epair(a, b))))) (ff_ne_tt h)
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isInr(Exp.efst(p))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.efst p) (Exp.einr (inrTyOf(Exp.efst(p))) (inrValOf(Exp.efst(p))))) (ff_ne_tt h)
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isInr(Exp.esnd(p))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.esnd p) (Exp.einr (inrTyOf(Exp.esnd(p))) (inrValOf(Exp.esnd(p))))) (ff_ne_tt h)
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isInr(Exp.einl(B, v))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.einl B v) (Exp.einr (inrTyOf(Exp.einl(B, v))) (inrValOf(Exp.einl(B, v))))) (ff_ne_tt h)
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isInr(Exp.ecase(s, l, r))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Exp (Exp.ecase s l r) (Exp.einr (inrTyOf(Exp.ecase(s, l, r))) (inrValOf(Exp.ecase(s, l, r))))) (ff_ne_tt h)
      }

    -- A variable cannot be looked up in the empty context (by induction on the lookup).
    def nilLookupFalse (G : Ctx) (n : Nat) (T : Ty) (lk : Lookup G n T)
        : Eq.{1} Bool (isNil(G)) Bool.true -> False :=
      match lk {
        | Lookup.here(T2, G2) => fun (h : Eq.{1} Bool (isNil(Ctx.cons T2 G2)) Bool.true) => ff_ne_tt h
        | Lookup.there(T2, U2, G2, n2, lk2) => fun (h : Eq.{1} Bool (isNil(Ctx.cons U2 G2)) Bool.true) => ff_ne_tt h
      }

    -- CANONICAL FORMS: a well-typed value of arrow / nat / bool type is a λ / nat / bool.
    fn canon_arrow(G: Ctx, e: Exp, ty: Ty, d: HasTy G e ty)
      -> (Eq.{1} Bool (isValue(e)) Bool.true -> Eq.{1} Bool (isArrow(ty)) Bool.true -> Eq.{1} Bool (isLam(e)) Bool.true) {
        match d {
          | HasTy.tvar(G2, n2, T2, lk2) => fun (h1 : Eq.{1} Bool (isValue(Exp.evar(n2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.evar(n2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tnat(G2, n2) => fun (h1 : Eq.{1} Bool (isValue(Exp.enat(n2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.enat(n2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tbool(G2, b2) => fun (h1 : Eq.{1} Bool (isValue(Exp.ebool(b2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(Ty.tbool)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.ebool(b2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tadd(G2, a2, b2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.eadd(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.eadd(a2, b2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tlet(G2, a2, body2, A2, B2, da, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elet(a2, body2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.elet(a2, body2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tlam(G2, A2, body2, B2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elam(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(Ty.tarrow A2 B2)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | HasTy.tapp(G2, f2, a2, A2, B2, df, da) => fun (h1 : Eq.{1} Bool (isValue(Exp.eapp(f2, a2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.eapp(f2, a2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tif(G2, cnd2, thn2, els2, T2, dc, dt, de) => fun (h1 : Eq.{1} Bool (isValue(Exp.eif(cnd2, thn2, els2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.eif(cnd2, thn2, els2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tfix(G2, A2, body2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.efix(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.efix(A2, body2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tpair(G2, a2, b2, A2, B2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.epair(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(Ty.tprod A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.epair(a2, b2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tfst(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.efst(p2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.efst(p2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tsnd(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.esnd(p2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.esnd(p2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tinl(G2, B2, v2, A2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einl(B2, v2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(Ty.tsum A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.einl(B2, v2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tinr(G2, A2, v2, B2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einr(A2, v2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(Ty.tsum A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.einr(A2, v2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tcase(G2, s2, l2, r2, A2, B2, C2, ds, dl, dr) => fun (h1 : Eq.{1} Bool (isValue(Exp.ecase(s2, l2, r2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(C2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(Exp.ecase(s2, l2, r2))) Bool.true) (ff_ne_tt h1)
        }
    }
    fn canon_nat(G: Ctx, e: Exp, ty: Ty, d: HasTy G e ty)
      -> (Eq.{1} Bool (isValue(e)) Bool.true -> Eq.{1} Bool (isTnat(ty)) Bool.true -> Eq.{1} Bool (isNatLit(e)) Bool.true) {
        match d {
          | HasTy.tvar(G2, n2, T2, lk2) => fun (h1 : Eq.{1} Bool (isValue(Exp.evar(n2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.evar(n2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tnat(G2, n2) => fun (h1 : Eq.{1} Bool (isValue(Exp.enat(n2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(Ty.tnat)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | HasTy.tbool(G2, b2) => fun (h1 : Eq.{1} Bool (isValue(Exp.ebool(b2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(Ty.tbool)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.ebool(b2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tadd(G2, a2, b2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.eadd(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.eadd(a2, b2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tlet(G2, a2, body2, A2, B2, da, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elet(a2, body2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.elet(a2, body2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tlam(G2, A2, body2, B2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elam(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(Ty.tarrow A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.elam(A2, body2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tapp(G2, f2, a2, A2, B2, df, da) => fun (h1 : Eq.{1} Bool (isValue(Exp.eapp(f2, a2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.eapp(f2, a2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tif(G2, cnd2, thn2, els2, T2, dc, dt, de) => fun (h1 : Eq.{1} Bool (isValue(Exp.eif(cnd2, thn2, els2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.eif(cnd2, thn2, els2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tfix(G2, A2, body2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.efix(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.efix(A2, body2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tpair(G2, a2, b2, A2, B2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.epair(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(Ty.tprod A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.epair(a2, b2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tfst(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.efst(p2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.efst(p2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tsnd(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.esnd(p2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.esnd(p2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tinl(G2, B2, v2, A2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einl(B2, v2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(Ty.tsum A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.einl(B2, v2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tinr(G2, A2, v2, B2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einr(A2, v2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(Ty.tsum A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.einr(A2, v2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tcase(G2, s2, l2, r2, A2, B2, C2, ds, dl, dr) => fun (h1 : Eq.{1} Bool (isValue(Exp.ecase(s2, l2, r2))) Bool.true) (h2 : Eq.{1} Bool (isTnat(C2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isNatLit(Exp.ecase(s2, l2, r2))) Bool.true) (ff_ne_tt h1)
        }
    }
    fn canon_bool(G: Ctx, e: Exp, ty: Ty, d: HasTy G e ty)
      -> (Eq.{1} Bool (isValue(e)) Bool.true -> Eq.{1} Bool (isTbool(ty)) Bool.true -> Eq.{1} Bool (isBoolLit(e)) Bool.true) {
        match d {
          | HasTy.tvar(G2, n2, T2, lk2) => fun (h1 : Eq.{1} Bool (isValue(Exp.evar(n2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.evar(n2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tnat(G2, n2) => fun (h1 : Eq.{1} Bool (isValue(Exp.enat(n2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.enat(n2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tbool(G2, b2) => fun (h1 : Eq.{1} Bool (isValue(Exp.ebool(b2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(Ty.tbool)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | HasTy.tadd(G2, a2, b2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.eadd(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.eadd(a2, b2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tlet(G2, a2, body2, A2, B2, da, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elet(a2, body2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.elet(a2, body2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tlam(G2, A2, body2, B2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elam(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(Ty.tarrow A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.elam(A2, body2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tapp(G2, f2, a2, A2, B2, df, da) => fun (h1 : Eq.{1} Bool (isValue(Exp.eapp(f2, a2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.eapp(f2, a2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tif(G2, cnd2, thn2, els2, T2, dc, dt, de) => fun (h1 : Eq.{1} Bool (isValue(Exp.eif(cnd2, thn2, els2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.eif(cnd2, thn2, els2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tfix(G2, A2, body2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.efix(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.efix(A2, body2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tpair(G2, a2, b2, A2, B2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.epair(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(Ty.tprod A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.epair(a2, b2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tfst(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.efst(p2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.efst(p2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tsnd(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.esnd(p2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.esnd(p2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tinl(G2, B2, v2, A2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einl(B2, v2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(Ty.tsum A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.einl(B2, v2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tinr(G2, A2, v2, B2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einr(A2, v2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(Ty.tsum A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.einr(A2, v2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tcase(G2, s2, l2, r2, A2, B2, C2, ds, dl, dr) => fun (h1 : Eq.{1} Bool (isValue(Exp.ecase(s2, l2, r2))) Bool.true) (h2 : Eq.{1} Bool (isTbool(C2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isBoolLit(Exp.ecase(s2, l2, r2))) Bool.true) (ff_ne_tt h1)
        }
    }
    -- A well-typed VALUE of sum type is an injection (canonical forms for sums).
    fn canon_sum(G: Ctx, e: Exp, ty: Ty, d: HasTy G e ty)
      -> (Eq.{1} Bool (isValue(e)) Bool.true -> Eq.{1} Bool (isSum(ty)) Bool.true -> Or (Eq.{1} Bool (isInl(e)) Bool.true) (Eq.{1} Bool (isInr(e)) Bool.true)) {
        match d {
          | HasTy.tvar(G2, n2, T2, lk2) => fun (h1 : Eq.{1} Bool (isValue(Exp.evar(n2))) Bool.true) (h2 : Eq.{1} Bool (isSum(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.evar(n2))) Bool.true) (Eq.{1} Bool (isInr(Exp.evar(n2))) Bool.true)) (ff_ne_tt h1)
          | HasTy.tnat(G2, n2) => fun (h1 : Eq.{1} Bool (isValue(Exp.enat(n2))) Bool.true) (h2 : Eq.{1} Bool (isSum(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.enat(n2))) Bool.true) (Eq.{1} Bool (isInr(Exp.enat(n2))) Bool.true)) (ff_ne_tt h2)
          | HasTy.tbool(G2, b2) => fun (h1 : Eq.{1} Bool (isValue(Exp.ebool(b2))) Bool.true) (h2 : Eq.{1} Bool (isSum(Ty.tbool)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.ebool(b2))) Bool.true) (Eq.{1} Bool (isInr(Exp.ebool(b2))) Bool.true)) (ff_ne_tt h2)
          | HasTy.tadd(G2, a2, b2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.eadd(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isSum(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.eadd(a2, b2))) Bool.true) (Eq.{1} Bool (isInr(Exp.eadd(a2, b2))) Bool.true)) (ff_ne_tt h1)
          | HasTy.tlet(G2, a2, body2, A2, B2, da, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elet(a2, body2))) Bool.true) (h2 : Eq.{1} Bool (isSum(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.elet(a2, body2))) Bool.true) (Eq.{1} Bool (isInr(Exp.elet(a2, body2))) Bool.true)) (ff_ne_tt h1)
          | HasTy.tlam(G2, A2, body2, B2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elam(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isSum(Ty.tarrow A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.elam(A2, body2))) Bool.true) (Eq.{1} Bool (isInr(Exp.elam(A2, body2))) Bool.true)) (ff_ne_tt h2)
          | HasTy.tapp(G2, f2, a2, A2, B2, df, da) => fun (h1 : Eq.{1} Bool (isValue(Exp.eapp(f2, a2))) Bool.true) (h2 : Eq.{1} Bool (isSum(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.eapp(f2, a2))) Bool.true) (Eq.{1} Bool (isInr(Exp.eapp(f2, a2))) Bool.true)) (ff_ne_tt h1)
          | HasTy.tif(G2, cnd2, thn2, els2, T2, dc, dt, de) => fun (h1 : Eq.{1} Bool (isValue(Exp.eif(cnd2, thn2, els2))) Bool.true) (h2 : Eq.{1} Bool (isSum(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.eif(cnd2, thn2, els2))) Bool.true) (Eq.{1} Bool (isInr(Exp.eif(cnd2, thn2, els2))) Bool.true)) (ff_ne_tt h1)
          | HasTy.tfix(G2, A2, body2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.efix(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isSum(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.efix(A2, body2))) Bool.true) (Eq.{1} Bool (isInr(Exp.efix(A2, body2))) Bool.true)) (ff_ne_tt h1)
          | HasTy.tpair(G2, a2, b2, A2, B2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.epair(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isSum(Ty.tprod A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.epair(a2, b2))) Bool.true) (Eq.{1} Bool (isInr(Exp.epair(a2, b2))) Bool.true)) (ff_ne_tt h2)
          | HasTy.tfst(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.efst(p2))) Bool.true) (h2 : Eq.{1} Bool (isSum(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.efst(p2))) Bool.true) (Eq.{1} Bool (isInr(Exp.efst(p2))) Bool.true)) (ff_ne_tt h1)
          | HasTy.tsnd(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.esnd(p2))) Bool.true) (h2 : Eq.{1} Bool (isSum(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.esnd(p2))) Bool.true) (Eq.{1} Bool (isInr(Exp.esnd(p2))) Bool.true)) (ff_ne_tt h1)
          | HasTy.tinl(G2, B2, v2, A2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einl(B2, v2))) Bool.true) (h2 : Eq.{1} Bool (isSum(Ty.tsum A2 B2)) Bool.true) =>
              Or.inl (Eq.{1} Bool (isInl(Exp.einl(B2, v2))) Bool.true) (Eq.{1} Bool (isInr(Exp.einl(B2, v2))) Bool.true) (Eq.refl.{1} Bool Bool.true)
          | HasTy.tinr(G2, A2, v2, B2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einr(A2, v2))) Bool.true) (h2 : Eq.{1} Bool (isSum(Ty.tsum A2 B2)) Bool.true) =>
              Or.inr (Eq.{1} Bool (isInl(Exp.einr(A2, v2))) Bool.true) (Eq.{1} Bool (isInr(Exp.einr(A2, v2))) Bool.true) (Eq.refl.{1} Bool Bool.true)
          | HasTy.tcase(G2, s2, l2, r2, A2, B2, C2, ds, dl, dr) => fun (h1 : Eq.{1} Bool (isValue(Exp.ecase(s2, l2, r2))) Bool.true) (h2 : Eq.{1} Bool (isSum(C2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Or (Eq.{1} Bool (isInl(Exp.ecase(s2, l2, r2))) Bool.true) (Eq.{1} Bool (isInr(Exp.ecase(s2, l2, r2))) Bool.true)) (ff_ne_tt h1)
        }
    }
    -- A well-typed VALUE of product type is a pair (canonical forms for products).
    fn canon_prod(G: Ctx, e: Exp, ty: Ty, d: HasTy G e ty)
      -> (Eq.{1} Bool (isValue(e)) Bool.true -> Eq.{1} Bool (isProd(ty)) Bool.true -> Eq.{1} Bool (isPair(e)) Bool.true) {
        match d {
          | HasTy.tvar(G2, n2, T2, lk2) => fun (h1 : Eq.{1} Bool (isValue(Exp.evar(n2))) Bool.true) (h2 : Eq.{1} Bool (isProd(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.evar(n2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tnat(G2, n2) => fun (h1 : Eq.{1} Bool (isValue(Exp.enat(n2))) Bool.true) (h2 : Eq.{1} Bool (isProd(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.enat(n2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tbool(G2, b2) => fun (h1 : Eq.{1} Bool (isValue(Exp.ebool(b2))) Bool.true) (h2 : Eq.{1} Bool (isProd(Ty.tbool)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.ebool(b2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tadd(G2, a2, b2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.eadd(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isProd(Ty.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.eadd(a2, b2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tlet(G2, a2, body2, A2, B2, da, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elet(a2, body2))) Bool.true) (h2 : Eq.{1} Bool (isProd(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.elet(a2, body2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tlam(G2, A2, body2, B2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.elam(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isProd(Ty.tarrow A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.elam(A2, body2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tapp(G2, f2, a2, A2, B2, df, da) => fun (h1 : Eq.{1} Bool (isValue(Exp.eapp(f2, a2))) Bool.true) (h2 : Eq.{1} Bool (isProd(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.eapp(f2, a2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tif(G2, cnd2, thn2, els2, T2, dc, dt, de) => fun (h1 : Eq.{1} Bool (isValue(Exp.eif(cnd2, thn2, els2))) Bool.true) (h2 : Eq.{1} Bool (isProd(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.eif(cnd2, thn2, els2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tfix(G2, A2, body2, dbody) => fun (h1 : Eq.{1} Bool (isValue(Exp.efix(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isProd(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.efix(A2, body2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tpair(G2, a2, b2, A2, B2, da, db) => fun (h1 : Eq.{1} Bool (isValue(Exp.epair(a2, b2))) Bool.true) (h2 : Eq.{1} Bool (isProd(Ty.tprod A2 B2)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | HasTy.tfst(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.efst(p2))) Bool.true) (h2 : Eq.{1} Bool (isProd(A2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.efst(p2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tsnd(G2, p2, A2, B2, dp) => fun (h1 : Eq.{1} Bool (isValue(Exp.esnd(p2))) Bool.true) (h2 : Eq.{1} Bool (isProd(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.esnd(p2))) Bool.true) (ff_ne_tt h1)
          | HasTy.tinl(G2, B2, v2, A2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einl(B2, v2))) Bool.true) (h2 : Eq.{1} Bool (isProd(Ty.tsum A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.einl(B2, v2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tinr(G2, A2, v2, B2, dv) => fun (h1 : Eq.{1} Bool (isValue(Exp.einr(A2, v2))) Bool.true) (h2 : Eq.{1} Bool (isProd(Ty.tsum A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.einr(A2, v2))) Bool.true) (ff_ne_tt h2)
          | HasTy.tcase(G2, s2, l2, r2, A2, B2, C2, ds, dl, dr) => fun (h1 : Eq.{1} Bool (isValue(Exp.ecase(s2, l2, r2))) Bool.true) (h2 : Eq.{1} Bool (isProd(C2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isPair(Exp.ecase(s2, l2, r2))) Bool.true) (ff_ne_tt h1)
        }
    }
"#;

/// **Step-characterization lemmas**: how `step` behaves on each non-value term, in terms
/// of stepping its reducible subterm (congruence) or producing a redex result. Each splits
/// on a single operand (values are concretised by canonical forms before these are used),
/// so each is an 8-way (or fewer) case analysis closed by `isSome_omap` or by computation.
pub const STEP_LEMMAS: &str = r#"
    fn canStep(e: Exp) -> Bool { isSome(step(e)) }

    -- eadd congruence on the (reducible) left operand.
    def step_eadd_l (a : Exp) (b : Exp)
      : Eq.{1} Bool (isValue(a)) Bool.false -> Eq.{1} Bool (isSome(step(Exp.eadd(a, b)))) (isSome(step(a))) :=
      match a {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eadd(a2, b)) (step(Exp.evar(n)))
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(n), b)))) (isSome(step(Exp.enat(n))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ebool(c) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(c))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.ebool(c), b)))) (isSome(step(Exp.ebool(c))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eadd(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(x, y))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eadd(a2, b)) (step(Exp.eadd(x, y)))
        | Exp.elet(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.elet(x, y))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eadd(a2, b)) (step(Exp.elet(x, y)))
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.elam(A, body))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.elam(A, body), b)))) (isSome(step(Exp.elam(A, body))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eapp(f, x) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(f, x))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eadd(a2, b)) (step(Exp.eapp(f, x)))
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eadd(a2, b)) (step(Exp.eif(c, t, el)))
        | Exp.efix(C, bd) => fun (h : Eq.{1} Bool (isValue(Exp.efix(C, bd))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eadd(a2, b)) (step(Exp.efix(C, bd)))
        | Exp.epair(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.epair(x, y))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.epair(x, y), b)))) (isSome(step(Exp.epair(x, y))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isValue(Exp.efst(p))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eadd(a2, b)) (step(Exp.efst(p)))
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(p))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eadd(a2, b)) (step(Exp.esnd(p)))
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(B, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.einl(B, v), b)))) (isSome(step(Exp.einl(B, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(A, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.einr(A, v), b)))) (isSome(step(Exp.einr(A, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eadd(a2, b)) (step(Exp.ecase(s, l, r)))
      }
    -- eadd congruence on the right operand (left already a nat literal).
    def step_eadd_enat_r (m : Nat) (b : Exp)
      : Eq.{1} Bool (isValue(b)) Bool.false -> Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(m), b)))) (isSome(step(b))) :=
      match b {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.false) => isSome_omap (fun (b2 : Exp) => Exp.eadd(Exp.enat(m), b2)) (step(Exp.evar(n)))
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(m), Exp.enat(n))))) (isSome(step(Exp.enat(n))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ebool(c) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(c))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(m), Exp.ebool(c))))) (isSome(step(Exp.ebool(c))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eadd(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(x, y))) Bool.false) => isSome_omap (fun (b2 : Exp) => Exp.eadd(Exp.enat(m), b2)) (step(Exp.eadd(x, y)))
        | Exp.elet(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.elet(x, y))) Bool.false) => isSome_omap (fun (b2 : Exp) => Exp.eadd(Exp.enat(m), b2)) (step(Exp.elet(x, y)))
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.elam(A, body))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(m), Exp.elam(A, body))))) (isSome(step(Exp.elam(A, body))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eapp(f, x) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(f, x))) Bool.false) => isSome_omap (fun (b2 : Exp) => Exp.eadd(Exp.enat(m), b2)) (step(Exp.eapp(f, x)))
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.false) => isSome_omap (fun (b2 : Exp) => Exp.eadd(Exp.enat(m), b2)) (step(Exp.eif(c, t, el)))
        | Exp.efix(C, bd) => fun (h : Eq.{1} Bool (isValue(Exp.efix(C, bd))) Bool.false) => isSome_omap (fun (b2 : Exp) => Exp.eadd(Exp.enat(m), b2)) (step(Exp.efix(C, bd)))
        | Exp.epair(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.epair(x, y))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(m), Exp.epair(x, y))))) (isSome(step(Exp.epair(x, y))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isValue(Exp.efst(p))) Bool.false) => isSome_omap (fun (b2 : Exp) => Exp.eadd(Exp.enat(m), b2)) (step(Exp.efst(p)))
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(p))) Bool.false) => isSome_omap (fun (b2 : Exp) => Exp.eadd(Exp.enat(m), b2)) (step(Exp.esnd(p)))
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(B, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(m), Exp.einl(B, v))))) (isSome(step(Exp.einl(B, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(A, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(m), Exp.einr(A, v))))) (isSome(step(Exp.einr(A, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.false) => isSome_omap (fun (b2 : Exp) => Exp.eadd(Exp.enat(m), b2)) (step(Exp.ecase(s, l, r)))
      }
    -- eadd of two literals reduces.
    def step_eadd_lit (m : Nat) (n : Nat) : Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(m), Exp.enat(n))))) Bool.true :=
      Eq.refl.{1} Bool Bool.true

    -- elet congruence on the bound expression, and the let-redex.
    def step_elet_a (a : Exp) (body : Exp)
      : Eq.{1} Bool (isValue(a)) Bool.false -> Eq.{1} Bool (isSome(step(Exp.elet(a, body)))) (isSome(step(a))) :=
      match a {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.elet(a2, body)) (step(Exp.evar(n)))
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.enat(n), body)))) (isSome(step(Exp.enat(n))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ebool(c) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(c))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.ebool(c), body)))) (isSome(step(Exp.ebool(c))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eadd(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(x, y))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.elet(a2, body)) (step(Exp.eadd(x, y)))
        | Exp.elet(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.elet(x, y))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.elet(a2, body)) (step(Exp.elet(x, y)))
        | Exp.elam(A, bd) => fun (h : Eq.{1} Bool (isValue(Exp.elam(A, bd))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.elam(A, bd), body)))) (isSome(step(Exp.elam(A, bd))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eapp(f, x) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(f, x))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.elet(a2, body)) (step(Exp.eapp(f, x)))
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.elet(a2, body)) (step(Exp.eif(c, t, el)))
        | Exp.efix(C, bd) => fun (h : Eq.{1} Bool (isValue(Exp.efix(C, bd))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.elet(a2, body)) (step(Exp.efix(C, bd)))
        | Exp.epair(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.epair(x, y))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.epair(x, y), body)))) (isSome(step(Exp.epair(x, y))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isValue(Exp.efst(p))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.elet(a2, body)) (step(Exp.efst(p)))
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(p))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.elet(a2, body)) (step(Exp.esnd(p)))
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(B, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.einl(B, v), body)))) (isSome(step(Exp.einl(B, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(A, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.einr(A, v), body)))) (isSome(step(Exp.einr(A, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.elet(a2, body)) (step(Exp.ecase(s, l, r)))
      }
    def step_elet_val (a : Exp) (body : Exp)
      : Eq.{1} Bool (isValue(a)) Bool.true -> Eq.{1} Bool (isSome(step(Exp.elet(a, body)))) Bool.true :=
      match a {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.evar(n), body)))) Bool.true) (ff_ne_tt h)
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.ebool(c) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(c))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.eadd(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(x, y))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.eadd(x, y), body)))) Bool.true) (ff_ne_tt h)
        | Exp.elet(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.elet(x, y))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.elet(x, y), body)))) Bool.true) (ff_ne_tt h)
        | Exp.elam(A, bd) => fun (h : Eq.{1} Bool (isValue(Exp.elam(A, bd))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.eapp(f, x) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(f, x))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.eapp(f, x), body)))) Bool.true) (ff_ne_tt h)
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.eif(c, t, el), body)))) Bool.true) (ff_ne_tt h)
        | Exp.efix(C, bd) => fun (h : Eq.{1} Bool (isValue(Exp.efix(C, bd))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.efix(C, bd), body)))) Bool.true) (ff_ne_tt h)
        | Exp.epair(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.epair(x, y))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isValue(Exp.efst(p))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.efst(p), body)))) Bool.true) (ff_ne_tt h)
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(p))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.esnd(p), body)))) Bool.true) (ff_ne_tt h)
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(B, v))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(A, v))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.elet(Exp.ecase(s, l, r), body)))) Bool.true) (ff_ne_tt h)
      }

    -- eif congruence on the condition, and the if-redex (condition a bool literal).
    def step_eif_c (cnd : Exp) (thn : Exp) (els : Exp)
      : Eq.{1} Bool (isValue(cnd)) Bool.false -> Eq.{1} Bool (isSome(step(Exp.eif(cnd, thn, els)))) (isSome(step(cnd))) :=
      match cnd {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.false) => isSome_omap (fun (c2 : Exp) => Exp.eif(c2, thn, els)) (step(Exp.evar(n)))
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eif(Exp.enat(n), thn, els)))) (isSome(step(Exp.enat(n))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ebool(c) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(c))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eif(Exp.ebool(c), thn, els)))) (isSome(step(Exp.ebool(c))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eadd(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(x, y))) Bool.false) => isSome_omap (fun (c2 : Exp) => Exp.eif(c2, thn, els)) (step(Exp.eadd(x, y)))
        | Exp.elet(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.elet(x, y))) Bool.false) => isSome_omap (fun (c2 : Exp) => Exp.eif(c2, thn, els)) (step(Exp.elet(x, y)))
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.elam(A, body))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eif(Exp.elam(A, body), thn, els)))) (isSome(step(Exp.elam(A, body))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eapp(f, x) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(f, x))) Bool.false) => isSome_omap (fun (c2 : Exp) => Exp.eif(c2, thn, els)) (step(Exp.eapp(f, x)))
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.false) => isSome_omap (fun (c2 : Exp) => Exp.eif(c2, thn, els)) (step(Exp.eif(c, t, el)))
        | Exp.efix(C, bd) => fun (h : Eq.{1} Bool (isValue(Exp.efix(C, bd))) Bool.false) => isSome_omap (fun (c2 : Exp) => Exp.eif(c2, thn, els)) (step(Exp.efix(C, bd)))
        | Exp.epair(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.epair(x, y))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eif(Exp.epair(x, y), thn, els)))) (isSome(step(Exp.epair(x, y))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isValue(Exp.efst(p))) Bool.false) => isSome_omap (fun (c2 : Exp) => Exp.eif(c2, thn, els)) (step(Exp.efst(p)))
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(p))) Bool.false) => isSome_omap (fun (c2 : Exp) => Exp.eif(c2, thn, els)) (step(Exp.esnd(p)))
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(B, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eif(Exp.einl(B, v), thn, els)))) (isSome(step(Exp.einl(B, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(A, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eif(Exp.einr(A, v), thn, els)))) (isSome(step(Exp.einr(A, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.false) => isSome_omap (fun (c2 : Exp) => Exp.eif(c2, thn, els)) (step(Exp.ecase(s, l, r)))
      }
    def step_eif_ebool (b : Bool) (thn : Exp) (els : Exp)
      : Eq.{1} Bool (isSome(step(Exp.eif(Exp.ebool(b), thn, els)))) Bool.true :=
      match b {
        | Bool.true  => Eq.refl.{1} Bool Bool.true
        | Bool.false => Eq.refl.{1} Bool Bool.true
      }

    -- eapp congruence on the function, congruence on the argument (function a λ), and beta.
    def step_eapp_l (f : Exp) (a : Exp)
      : Eq.{1} Bool (isValue(f)) Bool.false -> Eq.{1} Bool (isSome(step(Exp.eapp(f, a)))) (isSome(step(f))) :=
      match f {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.false) => isSome_omap (fun (f2 : Exp) => Exp.eapp(f2, a)) (step(Exp.evar(n)))
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.enat(n), a)))) (isSome(step(Exp.enat(n))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ebool(c) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(c))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.ebool(c), a)))) (isSome(step(Exp.ebool(c))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eadd(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(x, y))) Bool.false) => isSome_omap (fun (f2 : Exp) => Exp.eapp(f2, a)) (step(Exp.eadd(x, y)))
        | Exp.elet(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.elet(x, y))) Bool.false) => isSome_omap (fun (f2 : Exp) => Exp.eapp(f2, a)) (step(Exp.elet(x, y)))
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.elam(A, body))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), a)))) (isSome(step(Exp.elam(A, body))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eapp(g, x) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(g, x))) Bool.false) => isSome_omap (fun (f2 : Exp) => Exp.eapp(f2, a)) (step(Exp.eapp(g, x)))
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.false) => isSome_omap (fun (f2 : Exp) => Exp.eapp(f2, a)) (step(Exp.eif(c, t, el)))
        | Exp.efix(C, bd) => fun (h : Eq.{1} Bool (isValue(Exp.efix(C, bd))) Bool.false) => isSome_omap (fun (f2 : Exp) => Exp.eapp(f2, a)) (step(Exp.efix(C, bd)))
        | Exp.epair(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.epair(x, y))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.epair(x, y), a)))) (isSome(step(Exp.epair(x, y))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isValue(Exp.efst(p))) Bool.false) => isSome_omap (fun (f2 : Exp) => Exp.eapp(f2, a)) (step(Exp.efst(p)))
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(p))) Bool.false) => isSome_omap (fun (f2 : Exp) => Exp.eapp(f2, a)) (step(Exp.esnd(p)))
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(B, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.einl(B, v), a)))) (isSome(step(Exp.einl(B, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.einr(C, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(C, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.einr(C, v), a)))) (isSome(step(Exp.einr(C, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.false) => isSome_omap (fun (f2 : Exp) => Exp.eapp(f2, a)) (step(Exp.ecase(s, l, r)))
      }
    def step_eapp_elam_r (A : Ty) (body : Exp) (a : Exp)
      : Eq.{1} Bool (isValue(a)) Bool.false -> Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), a)))) (isSome(step(a))) :=
      match a {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eapp(Exp.elam(A, body), a2)) (step(Exp.evar(n)))
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.enat(n))))) (isSome(step(Exp.enat(n))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ebool(c) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(c))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.ebool(c))))) (isSome(step(Exp.ebool(c))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eadd(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(x, y))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eapp(Exp.elam(A, body), a2)) (step(Exp.eadd(x, y)))
        | Exp.elet(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.elet(x, y))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eapp(Exp.elam(A, body), a2)) (step(Exp.elet(x, y)))
        | Exp.elam(B, bd) => fun (h : Eq.{1} Bool (isValue(Exp.elam(B, bd))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.elam(B, bd))))) (isSome(step(Exp.elam(B, bd))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eapp(g, x) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(g, x))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eapp(Exp.elam(A, body), a2)) (step(Exp.eapp(g, x)))
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eapp(Exp.elam(A, body), a2)) (step(Exp.eif(c, t, el)))
        | Exp.efix(C, bd) => fun (h : Eq.{1} Bool (isValue(Exp.efix(C, bd))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eapp(Exp.elam(A, body), a2)) (step(Exp.efix(C, bd)))
        | Exp.epair(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.epair(x, y))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.epair(x, y))))) (isSome(step(Exp.epair(x, y))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isValue(Exp.efst(p))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eapp(Exp.elam(A, body), a2)) (step(Exp.efst(p)))
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(p))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eapp(Exp.elam(A, body), a2)) (step(Exp.esnd(p)))
        | Exp.einl(C, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(C, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.einl(C, v))))) (isSome(step(Exp.einl(C, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.einr(C, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(C, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.einr(C, v))))) (isSome(step(Exp.einr(C, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.false) => isSome_omap (fun (a2 : Exp) => Exp.eapp(Exp.elam(A, body), a2)) (step(Exp.ecase(s, l, r)))
      }
    def step_eapp_beta (A : Ty) (body : Exp) (a : Exp)
      : Eq.{1} Bool (isValue(a)) Bool.true -> Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), a)))) Bool.true :=
      match a {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.evar(n))))) Bool.true) (ff_ne_tt h)
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.ebool(c) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(c))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.eadd(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(x, y))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.eadd(x, y))))) Bool.true) (ff_ne_tt h)
        | Exp.elet(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.elet(x, y))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.elet(x, y))))) Bool.true) (ff_ne_tt h)
        | Exp.elam(B, bd) => fun (h : Eq.{1} Bool (isValue(Exp.elam(B, bd))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.eapp(g, x) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(g, x))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.eapp(g, x))))) Bool.true) (ff_ne_tt h)
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.eif(c, t, el))))) Bool.true) (ff_ne_tt h)
        | Exp.efix(C, bd) => fun (h : Eq.{1} Bool (isValue(Exp.efix(C, bd))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.efix(C, bd))))) Bool.true) (ff_ne_tt h)
        | Exp.epair(x, y) => fun (h : Eq.{1} Bool (isValue(Exp.epair(x, y))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.efst(p) => fun (h : Eq.{1} Bool (isValue(Exp.efst(p))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.efst(p))))) Bool.true) (ff_ne_tt h)
        | Exp.esnd(p) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(p))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.esnd(p))))) Bool.true) (ff_ne_tt h)
        | Exp.einl(C, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(C, v))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.einr(C, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(C, v))) Bool.true) => Eq.refl.{1} Bool Bool.true
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.true) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.eapp(Exp.elam(A, body), Exp.ecase(s, l, r))))) Bool.true) (ff_ne_tt h)
      }

    -- efst congruence on the (reducible) argument, and the fst-of-pair redex.
    def step_efst_l (p : Exp)
      : Eq.{1} Bool (isValue(p)) Bool.false -> Eq.{1} Bool (isSome(step(Exp.efst(p)))) (isSome(step(p))) :=
      match p {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.efst(p2)) (step(Exp.evar(n)))
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.efst(Exp.enat(n))))) (isSome(step(Exp.enat(n))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ebool(b) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(b))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.efst(Exp.ebool(b))))) (isSome(step(Exp.ebool(b))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(a, b))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.efst(p2)) (step(Exp.eadd(a, b)))
        | Exp.elet(a, b) => fun (h : Eq.{1} Bool (isValue(Exp.elet(a, b))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.efst(p2)) (step(Exp.elet(a, b)))
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.elam(A, body))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.efst(Exp.elam(A, body))))) (isSome(step(Exp.elam(A, body))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eapp(f, a) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(f, a))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.efst(p2)) (step(Exp.eapp(f, a)))
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.efst(p2)) (step(Exp.eif(c, t, el)))
        | Exp.efix(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.efix(A, body))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.efst(p2)) (step(Exp.efix(A, body)))
        | Exp.epair(a, b) => fun (h : Eq.{1} Bool (isValue(Exp.epair(a, b))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.efst(Exp.epair(a, b))))) (isSome(step(Exp.epair(a, b))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.efst(q) => fun (h : Eq.{1} Bool (isValue(Exp.efst(q))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.efst(p2)) (step(Exp.efst(q)))
        | Exp.esnd(q) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(q))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.efst(p2)) (step(Exp.esnd(q)))
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(B, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.efst(Exp.einl(B, v))))) (isSome(step(Exp.einl(B, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(A, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.efst(Exp.einr(A, v))))) (isSome(step(Exp.einr(A, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.efst(p2)) (step(Exp.ecase(s, l, r)))
      }
    def step_efst_pair (a : Exp) (b : Exp) : Eq.{1} Bool (isSome(step(Exp.efst(Exp.epair(a, b))))) Bool.true :=
      Eq.refl.{1} Bool Bool.true

    -- esnd congruence on the (reducible) argument, and the snd-of-pair redex.
    def step_esnd_l (p : Exp)
      : Eq.{1} Bool (isValue(p)) Bool.false -> Eq.{1} Bool (isSome(step(Exp.esnd(p)))) (isSome(step(p))) :=
      match p {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.esnd(p2)) (step(Exp.evar(n)))
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.esnd(Exp.enat(n))))) (isSome(step(Exp.enat(n))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ebool(b) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(b))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.esnd(Exp.ebool(b))))) (isSome(step(Exp.ebool(b))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(a, b))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.esnd(p2)) (step(Exp.eadd(a, b)))
        | Exp.elet(a, b) => fun (h : Eq.{1} Bool (isValue(Exp.elet(a, b))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.esnd(p2)) (step(Exp.elet(a, b)))
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.elam(A, body))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.esnd(Exp.elam(A, body))))) (isSome(step(Exp.elam(A, body))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eapp(f, a) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(f, a))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.esnd(p2)) (step(Exp.eapp(f, a)))
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.esnd(p2)) (step(Exp.eif(c, t, el)))
        | Exp.efix(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.efix(A, body))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.esnd(p2)) (step(Exp.efix(A, body)))
        | Exp.epair(a, b) => fun (h : Eq.{1} Bool (isValue(Exp.epair(a, b))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.esnd(Exp.epair(a, b))))) (isSome(step(Exp.epair(a, b))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.efst(q) => fun (h : Eq.{1} Bool (isValue(Exp.efst(q))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.esnd(p2)) (step(Exp.efst(q)))
        | Exp.esnd(q) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(q))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.esnd(p2)) (step(Exp.esnd(q)))
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(B, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.esnd(Exp.einl(B, v))))) (isSome(step(Exp.einl(B, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(A, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.esnd(Exp.einr(A, v))))) (isSome(step(Exp.einr(A, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ecase(s, l, r) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(s, l, r))) Bool.false) => isSome_omap (fun (p2 : Exp) => Exp.esnd(p2)) (step(Exp.ecase(s, l, r)))
      }
    def step_esnd_pair (a : Exp) (b : Exp) : Eq.{1} Bool (isSome(step(Exp.esnd(Exp.epair(a, b))))) Bool.true :=
      Eq.refl.{1} Bool Bool.true

    -- ecase congruence on the (reducible) scrutinee, and the case-of-injection redexes.
    def step_ecase_l (s : Exp) (l : Exp) (r : Exp)
      : Eq.{1} Bool (isValue(s)) Bool.false -> Eq.{1} Bool (isSome(step(Exp.ecase(s, l, r)))) (isSome(step(s))) :=
      match s {
        | Exp.evar(n) => fun (h : Eq.{1} Bool (isValue(Exp.evar(n))) Bool.false) => isSome_omap (fun (s2 : Exp) => Exp.ecase(s2, l, r)) (step(Exp.evar(n)))
        | Exp.enat(n) => fun (h : Eq.{1} Bool (isValue(Exp.enat(n))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.ecase(Exp.enat(n), l, r)))) (isSome(step(Exp.enat(n))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ebool(b) => fun (h : Eq.{1} Bool (isValue(Exp.ebool(b))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.ecase(Exp.ebool(b), l, r)))) (isSome(step(Exp.ebool(b))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eadd(a, b) => fun (h : Eq.{1} Bool (isValue(Exp.eadd(a, b))) Bool.false) => isSome_omap (fun (s2 : Exp) => Exp.ecase(s2, l, r)) (step(Exp.eadd(a, b)))
        | Exp.elet(a, b) => fun (h : Eq.{1} Bool (isValue(Exp.elet(a, b))) Bool.false) => isSome_omap (fun (s2 : Exp) => Exp.ecase(s2, l, r)) (step(Exp.elet(a, b)))
        | Exp.elam(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.elam(A, body))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.ecase(Exp.elam(A, body), l, r)))) (isSome(step(Exp.elam(A, body))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.eapp(f, a) => fun (h : Eq.{1} Bool (isValue(Exp.eapp(f, a))) Bool.false) => isSome_omap (fun (s2 : Exp) => Exp.ecase(s2, l, r)) (step(Exp.eapp(f, a)))
        | Exp.eif(c, t, el) => fun (h : Eq.{1} Bool (isValue(Exp.eif(c, t, el))) Bool.false) => isSome_omap (fun (s2 : Exp) => Exp.ecase(s2, l, r)) (step(Exp.eif(c, t, el)))
        | Exp.efix(A, body) => fun (h : Eq.{1} Bool (isValue(Exp.efix(A, body))) Bool.false) => isSome_omap (fun (s2 : Exp) => Exp.ecase(s2, l, r)) (step(Exp.efix(A, body)))
        | Exp.epair(a, b) => fun (h : Eq.{1} Bool (isValue(Exp.epair(a, b))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.ecase(Exp.epair(a, b), l, r)))) (isSome(step(Exp.epair(a, b))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.efst(q) => fun (h : Eq.{1} Bool (isValue(Exp.efst(q))) Bool.false) => isSome_omap (fun (s2 : Exp) => Exp.ecase(s2, l, r)) (step(Exp.efst(q)))
        | Exp.esnd(q) => fun (h : Eq.{1} Bool (isValue(Exp.esnd(q))) Bool.false) => isSome_omap (fun (s2 : Exp) => Exp.ecase(s2, l, r)) (step(Exp.esnd(q)))
        | Exp.einl(B, v) => fun (h : Eq.{1} Bool (isValue(Exp.einl(B, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.ecase(Exp.einl(B, v), l, r)))) (isSome(step(Exp.einl(B, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.einr(A, v) => fun (h : Eq.{1} Bool (isValue(Exp.einr(A, v))) Bool.false) => False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isSome(step(Exp.ecase(Exp.einr(A, v), l, r)))) (isSome(step(Exp.einr(A, v))))) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false h))
        | Exp.ecase(sc, l2, r2) => fun (h : Eq.{1} Bool (isValue(Exp.ecase(sc, l2, r2))) Bool.false) => isSome_omap (fun (s2 : Exp) => Exp.ecase(s2, l, r)) (step(Exp.ecase(sc, l2, r2)))
      }
    def step_ecase_inl (B : Ty) (v : Exp) (l : Exp) (r : Exp)
      : Eq.{1} Bool (isSome(step(Exp.ecase(Exp.einl(B, v), l, r)))) Bool.true :=
      Eq.refl.{1} Bool Bool.true
    def step_ecase_inr (A : Ty) (v : Exp) (l : Exp) (r : Exp)
      : Eq.{1} Bool (isSome(step(Exp.ecase(Exp.einr(A, v), l, r)))) Bool.true :=
      Eq.refl.{1} Bool Bool.true
"#;

/// **Progress** — *well-typed closed programs don't get stuck*: a closed (`isNil Γ`)
/// well-typed term is either a value or can take a step. Proved by induction on the typing
/// derivation; each non-value case concretises its value subterms with canonical forms and
/// concludes "it steps" from the step lemmas + the induction hypotheses.
pub const PROGRESS: &str = r#"
    fn progress(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> (Eq.{1} Bool (isNil(G)) Bool.true -> Eq.{1} Bool (orB(isValue(e))(canStep(e))) Bool.true) {
        match d {
          | HasTy.tvar(G2, n2, T2, lk2) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (orB(isValue(Exp.evar(n2)))(canStep(Exp.evar(n2)))) Bool.true) (nilLookupFalse G2 n2 T2 lk2 hnil)
          | HasTy.tnat(G2, n2) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) => Eq.refl.{1} Bool Bool.true
          | HasTy.tbool(G2, b2) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) => Eq.refl.{1} Bool Bool.true
          | HasTy.tlam(G2, A2, body2, B2, dbody) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) => Eq.refl.{1} Bool Bool.true
          | HasTy.tadd(G2, a2, b2, da, db) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              match bool_cases(isValue(a2)) {
                | Or.inl(eva) =>
                    match bool_cases(isValue(b2)) {
                      | Or.inl(evb) =>
                          Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Bool (isSome(step(Exp.eadd(x, b2)))) Bool.true)
                            (Exp.enat (natOf(a2))) a2
                            (Eq.symm.{1} Exp a2 (Exp.enat (natOf(a2))) (natlit_inv a2 (canon_nat G2 a2 Ty.tnat da eva (Eq.refl.{1} Bool Bool.true))))
                            (Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Bool (isSome(step(Exp.eadd(Exp.enat(natOf(a2)), x)))) Bool.true)
                               (Exp.enat (natOf(b2))) b2
                               (Eq.symm.{1} Exp b2 (Exp.enat (natOf(b2))) (natlit_inv b2 (canon_nat G2 b2 Ty.tnat db evb (Eq.refl.{1} Bool Bool.true))))
                               (step_eadd_lit (natOf(a2)) (natOf(b2))))
                      | Or.inr(evb) =>
                          Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Bool (isSome(step(Exp.eadd(x, b2)))) Bool.true)
                            (Exp.enat (natOf(a2))) a2
                            (Eq.symm.{1} Exp a2 (Exp.enat (natOf(a2))) (natlit_inv a2 (canon_nat G2 a2 Ty.tnat da eva (Eq.refl.{1} Bool Bool.true))))
                            (Eq.trans.{1} Bool (isSome(step(Exp.eadd(Exp.enat(natOf(a2)), b2)))) (isSome(step(b2))) Bool.true
                               (step_eadd_enat_r (natOf(a2)) b2 evb)
                               (orB_false_left (isValue(b2)) (canStep(b2)) (db.rec hnil) evb))
                    }
                | Or.inr(eva) =>
                    Eq.trans.{1} Bool (isSome(step(Exp.eadd(a2, b2)))) (isSome(step(a2))) Bool.true
                      (step_eadd_l a2 b2 eva)
                      (orB_false_left (isValue(a2)) (canStep(a2)) (da.rec hnil) eva)
              }
          | HasTy.tlet(G2, a2, body2, A2, B2, da, dbody) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              match bool_cases(isValue(a2)) {
                | Or.inl(eva) => step_elet_val a2 body2 eva
                | Or.inr(eva) =>
                    Eq.trans.{1} Bool (isSome(step(Exp.elet(a2, body2)))) (isSome(step(a2))) Bool.true
                      (step_elet_a a2 body2 eva)
                      (orB_false_left (isValue(a2)) (canStep(a2)) (da.rec hnil) eva)
              }
          | HasTy.tif(G2, cnd2, thn2, els2, T2, dc, dt, de) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              match bool_cases(isValue(cnd2)) {
                | Or.inl(evc) =>
                    Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Bool (isSome(step(Exp.eif(x, thn2, els2)))) Bool.true)
                      (Exp.ebool (boolOf(cnd2))) cnd2
                      (Eq.symm.{1} Exp cnd2 (Exp.ebool (boolOf(cnd2))) (boollit_inv cnd2 (canon_bool G2 cnd2 Ty.tbool dc evc (Eq.refl.{1} Bool Bool.true))))
                      (step_eif_ebool (boolOf(cnd2)) thn2 els2)
                | Or.inr(evc) =>
                    Eq.trans.{1} Bool (isSome(step(Exp.eif(cnd2, thn2, els2)))) (isSome(step(cnd2))) Bool.true
                      (step_eif_c cnd2 thn2 els2 evc)
                      (orB_false_left (isValue(cnd2)) (canStep(cnd2)) (dc.rec hnil) evc)
              }
          | HasTy.tapp(G2, f2, a2, A2, B2, df, da) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              match bool_cases(isValue(f2)) {
                | Or.inl(evf) =>
                    Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Bool (isSome(step(Exp.eapp(x, a2)))) Bool.true)
                      (Exp.elam (lamTyOf(f2)) (lamBodyOf(f2))) f2
                      (Eq.symm.{1} Exp f2 (Exp.elam (lamTyOf(f2)) (lamBodyOf(f2))) (lam_inv f2 (canon_arrow G2 f2 (Ty.tarrow A2 B2) df evf (Eq.refl.{1} Bool Bool.true))))
                      (match bool_cases(isValue(a2)) {
                        | Or.inl(eva) => step_eapp_beta (lamTyOf(f2)) (lamBodyOf(f2)) a2 eva
                        | Or.inr(eva) =>
                            Eq.trans.{1} Bool (isSome(step(Exp.eapp(Exp.elam(lamTyOf(f2), lamBodyOf(f2)), a2)))) (isSome(step(a2))) Bool.true
                              (step_eapp_elam_r (lamTyOf(f2)) (lamBodyOf(f2)) a2 eva)
                              (orB_false_left (isValue(a2)) (canStep(a2)) (da.rec hnil) eva)
                      })
                | Or.inr(evf) =>
                    Eq.trans.{1} Bool (isSome(step(Exp.eapp(f2, a2)))) (isSome(step(f2))) Bool.true
                      (step_eapp_l f2 a2 evf)
                      (orB_false_left (isValue(f2)) (canStep(f2)) (df.rec hnil) evf)
              }
          | HasTy.tfix(G2, A2, body2, dbody) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | HasTy.tpair(G2, a2, b2, A2, B2, da, db) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | HasTy.tfst(G2, p2, A2, B2, dp) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              match bool_cases(isValue(p2)) {
                | Or.inl(evp) =>
                    Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Bool (isSome(step(Exp.efst(x)))) Bool.true)
                      (Exp.epair (fstOf(p2)) (sndOf(p2))) p2
                      (Eq.symm.{1} Exp p2 (Exp.epair (fstOf(p2)) (sndOf(p2))) (pair_inv p2 (canon_prod G2 p2 (Ty.tprod A2 B2) dp evp (Eq.refl.{1} Bool Bool.true))))
                      (step_efst_pair (fstOf(p2)) (sndOf(p2)))
                | Or.inr(evp) =>
                    Eq.trans.{1} Bool (isSome(step(Exp.efst(p2)))) (isSome(step(p2))) Bool.true
                      (step_efst_l p2 evp)
                      (orB_false_left (isValue(p2)) (canStep(p2)) (dp.rec hnil) evp)
              }
          | HasTy.tsnd(G2, p2, A2, B2, dp) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              match bool_cases(isValue(p2)) {
                | Or.inl(evp) =>
                    Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Bool (isSome(step(Exp.esnd(x)))) Bool.true)
                      (Exp.epair (fstOf(p2)) (sndOf(p2))) p2
                      (Eq.symm.{1} Exp p2 (Exp.epair (fstOf(p2)) (sndOf(p2))) (pair_inv p2 (canon_prod G2 p2 (Ty.tprod A2 B2) dp evp (Eq.refl.{1} Bool Bool.true))))
                      (step_esnd_pair (fstOf(p2)) (sndOf(p2)))
                | Or.inr(evp) =>
                    Eq.trans.{1} Bool (isSome(step(Exp.esnd(p2)))) (isSome(step(p2))) Bool.true
                      (step_esnd_l p2 evp)
                      (orB_false_left (isValue(p2)) (canStep(p2)) (dp.rec hnil) evp)
              }
          | HasTy.tinl(G2, B2, v2, A2, dv) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | HasTy.tinr(G2, A2, v2, B2, dv) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | HasTy.tcase(G2, s2, l2, r2, A2, B2, C2, ds, dl, dr) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              match bool_cases(isValue(s2)) {
                | Or.inl(evs) =>
                    match canon_sum G2 s2 (Ty.tsum A2 B2) ds evs (Eq.refl.{1} Bool Bool.true) {
                      | Or.inl(hinl) =>
                          Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Bool (isSome(step(Exp.ecase(x, l2, r2)))) Bool.true)
                            (Exp.einl (inlTyOf(s2)) (inlValOf(s2))) s2
                            (Eq.symm.{1} Exp s2 (Exp.einl (inlTyOf(s2)) (inlValOf(s2))) (inl_inv s2 hinl))
                            (step_ecase_inl (inlTyOf(s2)) (inlValOf(s2)) l2 r2)
                      | Or.inr(hinr) =>
                          Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Bool (isSome(step(Exp.ecase(x, l2, r2)))) Bool.true)
                            (Exp.einr (inrTyOf(s2)) (inrValOf(s2))) s2
                            (Eq.symm.{1} Exp s2 (Exp.einr (inrTyOf(s2)) (inrValOf(s2))) (inr_inv s2 hinr))
                            (step_ecase_inr (inrTyOf(s2)) (inrValOf(s2)) l2 r2)
                    }
                | Or.inr(evs) =>
                    Eq.trans.{1} Bool (isSome(step(Exp.ecase(s2, l2, r2)))) (isSome(step(s2))) Bool.true
                      (step_ecase_l s2 l2 r2 evs)
                      (orB_false_left (isValue(s2)) (canStep(s2)) (ds.rec hnil) evs)
              }
        }
    }
"#;

/// A session that additionally loads the type-safety scaffolding ([`SAFETY_SCAFFOLD`]), the
/// step-characterization lemmas ([`STEP_LEMMAS`]), and the [`PROGRESS`] theorem.
pub fn safety_session() -> Result<Session, String> {
    let mut s = runnable_session()?;
    s.run(SAFETY_SCAFFOLD)?;
    s.run(STEP_LEMMAS)?;
    s.run(PROGRESS)?;
    Ok(s)
}

/// **Weakening foundation** for preservation: context insertion (`insertCtx`) and the
/// lookup-weakening lemma (a binding inserted anywhere in the context preserves every
/// existing lookup, at the shifted index). Proved by induction on the `Lookup` derivation;
/// the recursive `shiftIdx`'s laws hold definitionally, so the index arithmetic just
/// computes.
pub const PRESERVATION: &str = r#"
    -- Insert type `B` at de Bruijn position `k` in the context.
    fn insertCtx(k: Nat) -> (Ty -> Ctx -> Ctx) {
        match k {
          | Nat.zero    => fun (B : Ty) (G : Ctx) => Ctx.cons B G
          | Nat.succ(k2) => fun (B : Ty) (G : Ctx) =>
              match G { | Ctx.nil => Ctx.cons B Ctx.nil | Ctx.cons(T, G2) => Ctx.cons T (insertCtx(k2)(B)(G2)) }
        }
    }

    -- Lookup weakening: inserting a binding shifts every existing lookup index.
    fn lookup_weaken(G: Ctx, n: Nat, T: Ty, lk: Lookup G n T)
      -> ((k : Nat) -> (B : Ty) -> Lookup (insertCtx(k)(B)(G)) (shiftIdx(k)(n)) T) {
        match lk {
          | Lookup.here(T0, G0) => fun (k : Nat) (B : Ty) =>
              match k {
                | Nat.zero    => Lookup.there T0 B (Ctx.cons T0 G0) Nat.zero (Lookup.here T0 G0)
                | Nat.succ(k2) => Lookup.here T0 (insertCtx(k2)(B)(G0))
              }
          | Lookup.there(T0, U0, G0, n0, lk0) => fun (k : Nat) (B : Ty) =>
              match k {
                | Nat.zero    => Lookup.there T0 B (Ctx.cons U0 G0) (Nat.succ n0) (Lookup.there T0 U0 G0 n0 lk0)
                | Nat.succ(k2) => Lookup.there T0 U0 (insertCtx(k2)(B)(G0)) (shiftIdx(k2)(n0)) (lk0.rec k2 B)
              }
        }
    }

    -- Typing weakening: inserting a binding anywhere preserves typing (with the term
    -- shifted to match). By induction on the typing derivation; the variable case uses
    -- `lookup_weaken`, the binders increment the insertion point.
    fn HasTy_weaken(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((k : Nat) -> (A : Ty) -> HasTy (insertCtx(k)(A)(G)) (shift(e)(k)) T) {
        match d {
          | HasTy.tvar(G2, n2, T2, lk2) => fun (k : Nat) (A : Ty) =>
              HasTy.tvar (insertCtx(k)(A)(G2)) (shiftIdx(k)(n2)) T2 (lookup_weaken G2 n2 T2 lk2 k A)
          | HasTy.tnat(G2, n2) => fun (k : Nat) (A : Ty) => HasTy.tnat (insertCtx(k)(A)(G2)) n2
          | HasTy.tbool(G2, b2) => fun (k : Nat) (A : Ty) => HasTy.tbool (insertCtx(k)(A)(G2)) b2
          | HasTy.tadd(G2, a2, b2, da, db) => fun (k : Nat) (A : Ty) =>
              HasTy.tadd (insertCtx(k)(A)(G2)) (shift(a2)(k)) (shift(b2)(k)) (da.rec k A) (db.rec k A)
          | HasTy.tlet(G2, a2, body2, A2, B2, da, dbody) => fun (k : Nat) (A : Ty) =>
              HasTy.tlet (insertCtx(k)(A)(G2)) (shift(a2)(k)) (shift(body2)(Nat.succ(k))) A2 B2
                (da.rec k A) (dbody.rec (Nat.succ(k)) A)
          | HasTy.tlam(G2, A2, body2, B2, dbody) => fun (k : Nat) (A : Ty) =>
              HasTy.tlam (insertCtx(k)(A)(G2)) A2 (shift(body2)(Nat.succ(k))) B2 (dbody.rec (Nat.succ(k)) A)
          | HasTy.tapp(G2, f2, a2, A2, B2, df, da) => fun (k : Nat) (A : Ty) =>
              HasTy.tapp (insertCtx(k)(A)(G2)) (shift(f2)(k)) (shift(a2)(k)) A2 B2 (df.rec k A) (da.rec k A)
          | HasTy.tif(G2, cnd2, thn2, els2, T2, dc, dt, de) => fun (k : Nat) (A : Ty) =>
              HasTy.tif (insertCtx(k)(A)(G2)) (shift(cnd2)(k)) (shift(thn2)(k)) (shift(els2)(k)) T2
                (dc.rec k A) (dt.rec k A) (de.rec k A)
          | HasTy.tfix(G2, A2, body2, dbody) => fun (k : Nat) (A : Ty) =>
              HasTy.tfix (insertCtx(k)(A)(G2)) A2 (shift(body2)(Nat.succ(k))) (dbody.rec (Nat.succ(k)) A)
          | HasTy.tpair(G2, a2, b2, A2, B2, da, db) => fun (k : Nat) (A : Ty) =>
              HasTy.tpair (insertCtx(k)(A)(G2)) (shift(a2)(k)) (shift(b2)(k)) A2 B2 (da.rec k A) (db.rec k A)
          | HasTy.tfst(G2, p2, A2, B2, dp) => fun (k : Nat) (A : Ty) =>
              HasTy.tfst (insertCtx(k)(A)(G2)) (shift(p2)(k)) A2 B2 (dp.rec k A)
          | HasTy.tsnd(G2, p2, A2, B2, dp) => fun (k : Nat) (A : Ty) =>
              HasTy.tsnd (insertCtx(k)(A)(G2)) (shift(p2)(k)) A2 B2 (dp.rec k A)
          | HasTy.tinl(G2, B2, v2, A2, dv) => fun (k : Nat) (A : Ty) =>
              HasTy.tinl (insertCtx(k)(A)(G2)) B2 (shift(v2)(k)) A2 (dv.rec k A)
          | HasTy.tinr(G2, A2, v2, B2, dv) => fun (k : Nat) (A : Ty) =>
              HasTy.tinr (insertCtx(k)(A)(G2)) A2 (shift(v2)(k)) B2 (dv.rec k A)
          | HasTy.tcase(G2, s2, l2, r2, A2, B2, C2, ds, dl, dr) => fun (k : Nat) (A : Ty) =>
              HasTy.tcase (insertCtx(k)(A)(G2)) (shift(s2)(k)) (shift(l2)(Nat.succ(k))) (shift(r2)(Nat.succ(k))) A2 B2 C2
                (ds.rec k A) (dl.rec (Nat.succ(k)) A) (dr.rec (Nat.succ(k)) A)
        }
    }

    -- No-confusion / injectivity for Nat and Ctx (needed to invert lookups whose index is
    -- concrete — done by matching over a VARIABLE index with the concreteness supplied as
    -- equation hypotheses, then discharging impossible cases with these).
    def isZeroP (n : Nat) : Prop := Nat.rec.{1} (fun (_ : Nat) => Prop) True (fun (_ : Nat) (_ : Prop) => False) n
    def succ_ne_zero (n : Nat) (h : Eq.{1} Nat (Nat.succ n) Nat.zero) : False :=
      Eq.subst.{1} Nat isZeroP Nat.zero (Nat.succ n) (Eq.symm.{1} Nat (Nat.succ n) Nat.zero h) True.intro
    def succ_inj (n : Nat) (m : Nat) (h : Eq.{1} Nat (Nat.succ n) (Nat.succ m)) : Eq.{1} Nat n m :=
      Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Nat n (pred x)) (Nat.succ n) (Nat.succ m) h (Eq.refl.{1} Nat n)
    def headTy (G : Ctx) : Ty := Ctx.rec.{1} (fun (_ : Ctx) => Ty) Ty.tnat (fun (T : Ty) (G2 : Ctx) (_ : Ty) => T) G
    def tailCtx (G : Ctx) : Ctx := Ctx.rec.{1} (fun (_ : Ctx) => Ctx) Ctx.nil (fun (T : Ty) (G2 : Ctx) (_ : Ctx) => G2) G
    def cons_inj_head (X : Ty) (Y : Ctx) (X2 : Ty) (Y2 : Ctx) (h : Eq.{1} Ctx (Ctx.cons X Y) (Ctx.cons X2 Y2)) : Eq.{1} Ty X X2 :=
      Eq.subst.{1} Ctx (fun (G : Ctx) => Eq.{1} Ty X (headTy G)) (Ctx.cons X Y) (Ctx.cons X2 Y2) h (Eq.refl.{1} Ty X)
    def cons_inj_tail (X : Ty) (Y : Ctx) (X2 : Ty) (Y2 : Ctx) (h : Eq.{1} Ctx (Ctx.cons X Y) (Ctx.cons X2 Y2)) : Eq.{1} Ctx Y Y2 :=
      Eq.subst.{1} Ctx (fun (G : Ctx) => Eq.{1} Ctx Y (tailCtx G)) (Ctx.cons X Y) (Ctx.cons X2 Y2) h (Eq.refl.{1} Ctx Y)

    -- Lookup inversions: at index 0 the type is the head; at index succ m it is a lookup
    -- in the tail. Proved by matching the derivation over variable indices with the
    -- concreteness as equation hypotheses (impossible cases via succ_ne_zero).
    fn lookup_zero_inv(Gc: Ctx, n: Nat, U: Ty, lk: Lookup Gc n U)
      -> ((A : Ty) -> (G0 : Ctx) -> Eq.{1} Ctx Gc (Ctx.cons A G0) -> Eq.{1} Nat n Nat.zero -> Eq.{1} Ty U A) {
        match lk {
          | Lookup.here(T0, G00) => fun (A : Ty) (G0 : Ctx) (hG : Eq.{1} Ctx (Ctx.cons T0 G00) (Ctx.cons A G0)) (hn : Eq.{1} Nat Nat.zero Nat.zero) =>
              cons_inj_head T0 G00 A G0 hG
          | Lookup.there(T0, U0, G00, n0, lk0) => fun (A : Ty) (G0 : Ctx) (hG : Eq.{1} Ctx (Ctx.cons U0 G00) (Ctx.cons A G0)) (hn : Eq.{1} Nat (Nat.succ n0) Nat.zero) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Ty T0 A) (succ_ne_zero n0 hn)
        }
    }
    fn lookup_succ_inv(Gc: Ctx, n: Nat, U: Ty, lk: Lookup Gc n U)
      -> ((A : Ty) -> (G0 : Ctx) -> (m : Nat) -> Eq.{1} Ctx Gc (Ctx.cons A G0) -> Eq.{1} Nat n (Nat.succ m) -> Lookup G0 m U) {
        match lk {
          | Lookup.here(T0, G00) => fun (A : Ty) (G0 : Ctx) (m : Nat) (hG : Eq.{1} Ctx (Ctx.cons T0 G00) (Ctx.cons A G0)) (hn : Eq.{1} Nat Nat.zero (Nat.succ m)) =>
              False.rec.{0} (fun (_ : False) => Lookup G0 m T0) (succ_ne_zero m (Eq.symm.{1} Nat Nat.zero (Nat.succ m) hn))
          | Lookup.there(T0, U0, G00, n0, lk0) => fun (A : Ty) (G0 : Ctx) (m : Nat) (hG : Eq.{1} Ctx (Ctx.cons U0 G00) (Ctx.cons A G0)) (hn : Eq.{1} Nat (Nat.succ n0) (Nat.succ m)) =>
              Eq.subst.{1} Nat (fun (x : Nat) => Lookup G0 x T0) n0 m (succ_inj n0 m hn)
                (Eq.subst.{1} Ctx (fun (g : Ctx) => Lookup g n0 T0) G00 G0 (cons_inj_tail U0 G00 A G0 hG) lk0)
        }
    }

    -- Lifting a substitution preserves the "respects" relation: if σ maps G's lookups to
    -- well-typed terms in G', then liftSub σ maps (cons A G)'s lookups into (cons A G').
    -- The variable-0 case is the new binding; deeper variables go through σ + weakening.
    def liftSub_respects (A : Ty) (G : Ctx) (G' : Ctx) (s : Nat -> Exp)
        (resp : (n : Nat) -> (U : Ty) -> Lookup G n U -> HasTy G' (s n) U)
        (n : Nat) (U : Ty) : Lookup (Ctx.cons A G) n U -> HasTy (Ctx.cons A G') (liftSub(s)(n)) U :=
      match n {
        | Nat.zero => fun (lk : Lookup (Ctx.cons A G) Nat.zero U) =>
            Eq.subst.{1} Ty (fun (x : Ty) => HasTy (Ctx.cons A G') (Exp.evar(Nat.zero)) x) A U
              (Eq.symm.{1} Ty U A (lookup_zero_inv (Ctx.cons A G) Nat.zero U lk A G (Eq.refl.{1} Ctx (Ctx.cons A G)) (Eq.refl.{1} Nat Nat.zero)))
              (HasTy.tvar (Ctx.cons A G') Nat.zero A (Lookup.here A G'))
        | Nat.succ(m) => fun (lk : Lookup (Ctx.cons A G) (Nat.succ m) U) =>
            HasTy_weaken G' (s m) U
              (resp m U (lookup_succ_inv (Ctx.cons A G) (Nat.succ m) U lk A G m (Eq.refl.{1} Ctx (Ctx.cons A G)) (Eq.refl.{1} Nat (Nat.succ m))))
              Nat.zero A
      }

    -- THE SUBSTITUTION LEMMA (parallel form): a well-typed term stays well-typed under any
    -- substitution that maps the context's variables to well-typed terms in a target
    -- context. By induction on the typing derivation; binders extend the substitution with
    -- `liftSub` (typed by `liftSub_respects`). This is stated over the ORIGINAL context, so
    -- the variable case is just the "respects" hypothesis — no context-splice inversion.
    fn subst_lemma(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((G2 : Ctx) -> (s : Nat -> Exp)
            -> ((n : Nat) -> (U : Ty) -> Lookup G n U -> HasTy G2 (s n) U)
            -> HasTy G2 (applySub(e)(s)) T) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              resp n2 T2 lk2
          | HasTy.tnat(Gv, n2) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tnat G2 n2
          | HasTy.tbool(Gv, b2) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tbool G2 b2
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tadd G2 (applySub(a2)(s)) (applySub(b2)(s)) (da.rec G2 s resp) (db.rec G2 s resp)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tlet G2 (applySub(a2)(s)) (applySub(body2)(liftSub(s))) A2 B2
                (da.rec G2 s resp)
                (dbody.rec (Ctx.cons A2 G2) (liftSub(s)) (liftSub_respects A2 Gv G2 s resp))
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tlam G2 A2 (applySub(body2)(liftSub(s))) B2
                (dbody.rec (Ctx.cons A2 G2) (liftSub(s)) (liftSub_respects A2 Gv G2 s resp))
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tapp G2 (applySub(f2)(s)) (applySub(a2)(s)) A2 B2 (df.rec G2 s resp) (da.rec G2 s resp)
          | HasTy.tif(Gv, cnd2, thn2, els2, T2, dc, dt, de) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tif G2 (applySub(cnd2)(s)) (applySub(thn2)(s)) (applySub(els2)(s)) T2
                (dc.rec G2 s resp) (dt.rec G2 s resp) (de.rec G2 s resp)
          | HasTy.tfix(Gv, A2, body2, dbody) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tfix G2 A2 (applySub(body2)(liftSub(s)))
                (dbody.rec (Ctx.cons A2 G2) (liftSub(s)) (liftSub_respects A2 Gv G2 s resp))
          | HasTy.tpair(Gv, a2, b2, A2, B2, da, db) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tpair G2 (applySub(a2)(s)) (applySub(b2)(s)) A2 B2 (da.rec G2 s resp) (db.rec G2 s resp)
          | HasTy.tfst(Gv, p2, A2, B2, dp) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tfst G2 (applySub(p2)(s)) A2 B2 (dp.rec G2 s resp)
          | HasTy.tsnd(Gv, p2, A2, B2, dp) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tsnd G2 (applySub(p2)(s)) A2 B2 (dp.rec G2 s resp)
          | HasTy.tinl(Gv, B2, v2, A2, dv) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tinl G2 B2 (applySub(v2)(s)) A2 (dv.rec G2 s resp)
          | HasTy.tinr(Gv, A2, v2, B2, dv) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tinr G2 A2 (applySub(v2)(s)) B2 (dv.rec G2 s resp)
          | HasTy.tcase(Gv, s2, l2, r2, A2, B2, C2, ds, dl, dr) => fun (G2 : Ctx) (s : Nat -> Exp)
                (resp : (n : Nat) -> (U : Ty) -> Lookup Gv n U -> HasTy G2 (s n) U) =>
              HasTy.tcase G2 (applySub(s2)(s)) (applySub(l2)(liftSub(s))) (applySub(r2)(liftSub(s))) A2 B2 C2
                (ds.rec G2 s resp)
                (dl.rec (Ctx.cons A2 G2) (liftSub(s)) (liftSub_respects A2 Gv G2 s resp))
                (dr.rec (Ctx.cons B2 G2) (liftSub(s)) (liftSub_respects B2 Gv G2 s resp))
        }
    }

    -- The single-substitution assignment `atSubj 0 v` respects (cons A G) ⇝ G when v : A.
    def atSub0_respects (A : Ty) (G : Ctx) (v : Exp) (dv : HasTy G v A)
        (n : Nat) (U : Ty) : Lookup (Ctx.cons A G) n U -> HasTy G (atSubj(Nat.zero)(v)(n)) U :=
      match n {
        | Nat.zero => fun (lk : Lookup (Ctx.cons A G) Nat.zero U) =>
            Eq.subst.{1} Ty (fun (x : Ty) => HasTy G v x) A U
              (Eq.symm.{1} Ty U A (lookup_zero_inv (Ctx.cons A G) Nat.zero U lk A G (Eq.refl.{1} Ctx (Ctx.cons A G)) (Eq.refl.{1} Nat Nat.zero)))
              dv
        | Nat.succ(m) => fun (lk : Lookup (Ctx.cons A G) (Nat.succ m) U) =>
            HasTy.tvar G m U (lookup_succ_inv (Ctx.cons A G) (Nat.succ m) U lk A G m (Eq.refl.{1} Ctx (Ctx.cons A G)) (Eq.refl.{1} Nat (Nat.succ m)))
      }

    -- **Substitution preserves typing** (the β/let case of preservation): substituting a
    -- value `v : A` for the most-recent binding in a well-typed `body : T` yields a
    -- well-typed term. A direct instance of the substitution lemma.
    def subst_preserves (A : Ty) (G : Ctx) (body : Exp) (T : Ty) (v : Exp)
        (dbody : HasTy (Ctx.cons A G) body T) (dv : HasTy G v A)
        : HasTy G (subst(body)(Nat.zero)(v)) T :=
      subst_lemma (Ctx.cons A G) body T dbody G (atSubj(Nat.zero)(v)) (atSub0_respects A G v dv)

    -- ===== Inversion scaffolding for the preservation theorem =====
    -- A constructor tag for Exp + reflexivity of nat equality give a single generic
    -- no-confusion principle (distinct head constructors are unequal), avoiding a
    -- per-constructor discriminator.
    fn expTag(e: Exp) -> Nat {
        match e {
          | Exp.evar(n)  => Nat.zero
          | Exp.enat(n)  => Nat.succ(Nat.zero)
          | Exp.ebool(b) => Nat.succ(Nat.succ(Nat.zero))
          | Exp.eadd(a, b) => Nat.succ(Nat.succ(Nat.succ(Nat.zero)))
          | Exp.elet(a, b) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))
          | Exp.elam(A, b) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))
          | Exp.eapp(f, a) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))
          | Exp.eif(c, t, el) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))))
          | Exp.efix(A, b) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))
          | Exp.epair(a, b) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))))))
          | Exp.efst(p) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))))
          | Exp.esnd(p) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))))))))
          | Exp.einl(B, v) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))))))
          | Exp.einr(A, v) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))))))))))
          | Exp.ecase(s, l, r) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))))))))
        }
    }
    fn nat_eqb_refl(n: Nat) -> Eq.{1} Bool (nat_eqb(n)(n)) Bool.true {
        match n { | Nat.zero => Eq.refl.{1} Bool Bool.true | Nat.succ(k) => k.rec }
    }
    -- Distinct-tag terms are unequal: from `e1 = e2` we'd get equal tags, but the tags'
    -- `nat_eqb` is `false` (computed), contradicting reflexivity.
    def exp_noconf (e1 : Exp) (e2 : Exp)
        (htag : Eq.{1} Bool (nat_eqb(expTag(e1))(expTag(e2))) Bool.false)
        (heq : Eq.{1} Exp e1 e2) : False :=
      ff_ne_tt (Eq.trans.{1} Bool Bool.false (nat_eqb(expTag(e1))(expTag(e2))) Bool.true
                  (Eq.symm.{1} Bool (nat_eqb(expTag(e1))(expTag(e2))) Bool.false htag)
                  (Eq.subst.{1} Nat (fun (t : Nat) => Eq.{1} Bool (nat_eqb(expTag(e1))(t)) Bool.true)
                     (expTag(e1)) (expTag(e2))
                     (Eq.subst.{1} Exp (fun (x : Exp) => Eq.{1} Nat (expTag(e1)) (expTag(x))) e1 e2 heq (Eq.refl.{1} Nat (expTag(e1))))
                     (nat_eqb_refl (expTag(e1)))))

    -- OExp no-confusion + injection (for relating `step` outputs to reducts later).
    def isNoneP (o : OExp) : Prop := OExp.rec.{1} (fun (_ : OExp) => Prop) True (fun (_ : Exp) => False) o
    def osome_ne_onone (e : Exp) (h : Eq.{1} OExp (OExp.osome e) OExp.onone) : False :=
      Eq.subst.{1} OExp isNoneP OExp.onone (OExp.osome e) (Eq.symm.{1} OExp (OExp.osome e) OExp.onone h) True.intro
    fn osomeOf(o: OExp) -> Exp { match o { | OExp.osome(e) => e | _ => Exp.enat(Nat.zero) } }
    def osome_inj (x : Exp) (y : Exp) (h : Eq.{1} OExp (OExp.osome x) (OExp.osome y)) : Eq.{1} Exp x y :=
      Eq.subst.{1} OExp (fun (o : OExp) => Eq.{1} Exp x (osomeOf o)) (OExp.osome x) (OExp.osome y) h (Eq.refl.{1} Exp x)

    -- Argument projections (with wildcard catch-alls) + constructor injectivity.
    fn addLof(e: Exp) -> Exp { match e { | Exp.eadd(a, b) => a | _ => Exp.enat(Nat.zero) } }
    fn addRof(e: Exp) -> Exp { match e { | Exp.eadd(a, b) => b | _ => Exp.enat(Nat.zero) } }
    fn appFof(e: Exp) -> Exp { match e { | Exp.eapp(f, a) => f | _ => Exp.enat(Nat.zero) } }
    fn appAof(e: Exp) -> Exp { match e { | Exp.eapp(f, a) => a | _ => Exp.enat(Nat.zero) } }
    fn ifCof(e: Exp) -> Exp { match e { | Exp.eif(c, t, el) => c | _ => Exp.enat(Nat.zero) } }
    fn ifTof(e: Exp) -> Exp { match e { | Exp.eif(c, t, el) => t | _ => Exp.enat(Nat.zero) } }
    fn ifEof(e: Exp) -> Exp { match e { | Exp.eif(c, t, el) => el | _ => Exp.enat(Nat.zero) } }
    fn letAof(e: Exp) -> Exp { match e { | Exp.elet(a, b) => a | _ => Exp.enat(Nat.zero) } }
    fn letBof(e: Exp) -> Exp { match e { | Exp.elet(a, b) => b | _ => Exp.enat(Nat.zero) } }
    fn fixTyOf(e: Exp) -> Ty { match e { | Exp.efix(A, b) => A | _ => Ty.tnat } }
    fn fixBodyOf(e: Exp) -> Exp { match e { | Exp.efix(A, b) => b | _ => Exp.enat(Nat.zero) } }
    fn pairLof(e: Exp) -> Exp { match e { | Exp.epair(a, b) => a | _ => Exp.enat(Nat.zero) } }
    fn pairRof(e: Exp) -> Exp { match e { | Exp.epair(a, b) => b | _ => Exp.enat(Nat.zero) } }
    fn fstArgOf(e: Exp) -> Exp { match e { | Exp.efst(p) => p | _ => Exp.enat(Nat.zero) } }
    fn sndArgOf(e: Exp) -> Exp { match e { | Exp.esnd(p) => p | _ => Exp.enat(Nat.zero) } }
    fn caseScrutOf(e: Exp) -> Exp { match e { | Exp.ecase(s, l, r) => s | _ => Exp.enat(Nat.zero) } }
    fn caseLof(e: Exp) -> Exp { match e { | Exp.ecase(s, l, r) => l | _ => Exp.enat(Nat.zero) } }
    fn caseRof(e: Exp) -> Exp { match e { | Exp.ecase(s, l, r) => r | _ => Exp.enat(Nat.zero) } }
    def proj_inj (proj : Exp -> Exp) (x : Exp) (y : Exp) (h : Eq.{1} Exp x y) : Eq.{1} Exp (proj x) (proj y) :=
      Eq.subst.{1} Exp (fun (z : Exp) => Eq.{1} Exp (proj x) (proj z)) x y h (Eq.refl.{1} Exp (proj x))
    def ty_proj_inj (proj : Ty -> Ty) (x : Ty) (y : Ty) (h : Eq.{1} Ty x y) : Eq.{1} Ty (proj x) (proj y) :=
      Eq.subst.{1} Ty (fun (z : Ty) => Eq.{1} Ty (proj x) (proj z)) x y h (Eq.refl.{1} Ty (proj x))

    -- Existential + conjunction, for the inversions that must expose a bound/argument type.
    inductive And2 (a : Prop) (b : Prop) : Prop | mk : a -> b -> And2 a b
    inductive ExTy (P : Ty -> Prop) : Prop | mk : (A : Ty) -> P A -> ExTy P

    -- ===== HasTy inversions (via the equation-hypothesis trick) =====
    fn hasty_add_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((a : Exp) -> (b : Exp) -> Eq.{1} Exp e (Exp.eadd a b)
            -> And2 (HasTy G a Ty.tnat) (And2 (HasTy G b Ty.tnat) (Eq.{1} Ty T Ty.tnat))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty T2 Ty.tnat)))
                (exp_noconf (Exp.evar n2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty Ty.tnat Ty.tnat)))
                (exp_noconf (Exp.enat n2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty Ty.tbool Ty.tnat)))
                (exp_noconf (Exp.ebool b2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.eadd a b)) =>
              And2.mk (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty Ty.tnat Ty.tnat))
                (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x Ty.tnat) a2 a (proj_inj addLof (Exp.eadd a2 b2) (Exp.eadd a b) heq) da)
                (And2.mk (HasTy Gv b Ty.tnat) (Eq.{1} Ty Ty.tnat Ty.tnat)
                  (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x Ty.tnat) b2 b (proj_inj addRof (Exp.eadd a2 b2) (Exp.eadd a b) heq) db)
                  (Eq.refl.{1} Ty Ty.tnat))
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty B2 Ty.tnat)))
                (exp_noconf (Exp.elet a2 body2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty (Ty.tarrow A2 B2) Ty.tnat)))
                (exp_noconf (Exp.elam A2 body2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty B2 Ty.tnat)))
                (exp_noconf (Exp.eapp f2 a2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty Tif Ty.tnat)))
                (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty Afix2 Ty.tnat)))
                (exp_noconf (Exp.efix Afix2 body2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty (Ty.tprod Ap Bp) Ty.tnat)))
                (exp_noconf (Exp.epair a2 b2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty Ap Ty.tnat)))
                (exp_noconf (Exp.efst p2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty Bp Ty.tnat)))
                (exp_noconf (Exp.esnd p2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty (Ty.tsum Ai Bi) Ty.tnat)))
                (exp_noconf (Exp.einl Bi v2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty (Ty.tsum Ai Bi) Ty.tnat)))
                (exp_noconf (Exp.einr Ai v2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.eadd a b)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv a Ty.tnat) (And2 (HasTy Gv b Ty.tnat) (Eq.{1} Ty Cc Ty.tnat)))
                (exp_noconf (Exp.ecase s2 l2 r2) (Exp.eadd a b) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }
    fn hasty_if_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((c : Exp) -> (t : Exp) -> (el : Exp) -> Eq.{1} Exp e (Exp.eif c t el)
            -> And2 (HasTy G c Ty.tbool) (And2 (HasTy G t T) (HasTy G el T))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t T2) (HasTy Gv el T2)))
                (exp_noconf (Exp.evar n2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t Ty.tnat) (HasTy Gv el Ty.tnat)))
                (exp_noconf (Exp.enat n2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t Ty.tbool) (HasTy Gv el Ty.tbool)))
                (exp_noconf (Exp.ebool b2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t Ty.tnat) (HasTy Gv el Ty.tnat)))
                (exp_noconf (Exp.eadd a2 b2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t B2) (HasTy Gv el B2)))
                (exp_noconf (Exp.elet a2 body2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t (Ty.tarrow A2 B2)) (HasTy Gv el (Ty.tarrow A2 B2))))
                (exp_noconf (Exp.elam A2 body2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t B2) (HasTy Gv el B2)))
                (exp_noconf (Exp.eapp f2 a2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.eif c t el)) =>
              And2.mk (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t Tif) (HasTy Gv el Tif))
                (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x Ty.tbool) cnd2 c (proj_inj ifCof (Exp.eif cnd2 thn2 els2) (Exp.eif c t el) heq) dc)
                (And2.mk (HasTy Gv t Tif) (HasTy Gv el Tif)
                  (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x Tif) thn2 t (proj_inj ifTof (Exp.eif cnd2 thn2 els2) (Exp.eif c t el) heq) dt)
                  (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x Tif) els2 el (proj_inj ifEof (Exp.eif cnd2 thn2 els2) (Exp.eif c t el) heq) de))
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t Afix2) (HasTy Gv el Afix2)))
                (exp_noconf (Exp.efix Afix2 body2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t (Ty.tprod Ap Bp)) (HasTy Gv el (Ty.tprod Ap Bp))))
                (exp_noconf (Exp.epair a2 b2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t Ap) (HasTy Gv el Ap)))
                (exp_noconf (Exp.efst p2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t Bp) (HasTy Gv el Bp)))
                (exp_noconf (Exp.esnd p2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t (Ty.tsum Ai Bi)) (HasTy Gv el (Ty.tsum Ai Bi))))
                (exp_noconf (Exp.einl Bi v2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t (Ty.tsum Ai Bi)) (HasTy Gv el (Ty.tsum Ai Bi))))
                (exp_noconf (Exp.einr Ai v2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (c : Exp) (t : Exp) (el : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.eif c t el)) =>
              False.rec.{0} (fun (_ : False) => And2 (HasTy Gv c Ty.tbool) (And2 (HasTy Gv t Cc) (HasTy Gv el Cc)))
                (exp_noconf (Exp.ecase s2 l2 r2) (Exp.eif c t el) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }
    def exp_ty_proj_inj (proj : Exp -> Ty) (x : Exp) (y : Exp) (h : Eq.{1} Exp x y) : Eq.{1} Ty (proj x) (proj y) :=
      Eq.subst.{1} Exp (fun (z : Exp) => Eq.{1} Ty (proj x) (proj z)) x y h (Eq.refl.{1} Ty (proj x))

    fn hasty_let_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((a : Exp) -> (body : Exp) -> Eq.{1} Exp e (Exp.elet a body)
            -> ExTy (fun (A : Ty) => And2 (HasTy G a A) (HasTy (Ctx.cons A G) body T))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body T2)))
                (exp_noconf (Exp.evar n2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body Ty.tnat)))
                (exp_noconf (Exp.enat n2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body Ty.tbool)))
                (exp_noconf (Exp.ebool b2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body Ty.tnat)))
                (exp_noconf (Exp.eadd a2 b2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.elet a body)) =>
              ExTy.mk (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body B2)) A2
                (And2.mk (HasTy Gv a A2) (HasTy (Ctx.cons A2 Gv) body B2)
                  (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x A2) a2 a (proj_inj letAof (Exp.elet a2 body2) (Exp.elet a body) heq) da)
                  (Eq.subst.{1} Exp (fun (x : Exp) => HasTy (Ctx.cons A2 Gv) x B2) body2 body (proj_inj letBof (Exp.elet a2 body2) (Exp.elet a body) heq) dbody))
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body (Ty.tarrow A2 B2))))
                (exp_noconf (Exp.elam A2 body2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body B2)))
                (exp_noconf (Exp.eapp f2 a2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body Tif)))
                (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body Afix2)))
                (exp_noconf (Exp.efix Afix2 body2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body (Ty.tprod Ap Bp))))
                (exp_noconf (Exp.epair a2 b2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body Ap)))
                (exp_noconf (Exp.efst p2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body Bp)))
                (exp_noconf (Exp.esnd p2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body (Ty.tsum Ai Bi))))
                (exp_noconf (Exp.einl Bi v2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body (Ty.tsum Ai Bi))))
                (exp_noconf (Exp.einr Ai v2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (a : Exp) (body : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.elet a body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv a A) (HasTy (Ctx.cons A Gv) body Cc)))
                (exp_noconf (Exp.ecase s2 l2 r2) (Exp.elet a body) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }
    fn hasty_app_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((f : Exp) -> (a : Exp) -> Eq.{1} Exp e (Exp.eapp f a)
            -> ExTy (fun (A : Ty) => And2 (HasTy G f (Ty.tarrow A T)) (HasTy G a A))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A T2)) (HasTy Gv a A)))
                (exp_noconf (Exp.evar n2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A Ty.tnat)) (HasTy Gv a A)))
                (exp_noconf (Exp.enat n2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A Ty.tbool)) (HasTy Gv a A)))
                (exp_noconf (Exp.ebool b2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A Ty.tnat)) (HasTy Gv a A)))
                (exp_noconf (Exp.eadd a2 b2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A B2)) (HasTy Gv a A)))
                (exp_noconf (Exp.elet a2 body2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A (Ty.tarrow A2 B2))) (HasTy Gv a A)))
                (exp_noconf (Exp.elam A2 body2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.eapp f a)) =>
              ExTy.mk (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A B2)) (HasTy Gv a A)) A2
                (And2.mk (HasTy Gv f (Ty.tarrow A2 B2)) (HasTy Gv a A2)
                  (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x (Ty.tarrow A2 B2)) f2 f (proj_inj appFof (Exp.eapp f2 a2) (Exp.eapp f a) heq) df)
                  (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x A2) a2 a (proj_inj appAof (Exp.eapp f2 a2) (Exp.eapp f a) heq) da))
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A Tif)) (HasTy Gv a A)))
                (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A Afix2)) (HasTy Gv a A)))
                (exp_noconf (Exp.efix Afix2 body2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A (Ty.tprod Ap Bp))) (HasTy Gv a A)))
                (exp_noconf (Exp.epair a2 b2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A Ap)) (HasTy Gv a A)))
                (exp_noconf (Exp.efst p2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A Bp)) (HasTy Gv a A)))
                (exp_noconf (Exp.esnd p2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A (Ty.tsum Ai Bi))) (HasTy Gv a A)))
                (exp_noconf (Exp.einl Bi v2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A (Ty.tsum Ai Bi))) (HasTy Gv a A)))
                (exp_noconf (Exp.einr Ai v2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (f : Exp) (a : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.eapp f a)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (HasTy Gv f (Ty.tarrow A Cc)) (HasTy Gv a A)))
                (exp_noconf (Exp.ecase s2 l2 r2) (Exp.eapp f a) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }
    fn hasty_lam_inv(G: Ctx, e: Exp, Tf: Ty, d: HasTy G e Tf)
      -> ((Alam : Ty) -> (body : Exp) -> Eq.{1} Exp e (Exp.elam Alam body)
            -> ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Tf (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam G) body B))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty T2 (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.evar n2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ty.tnat (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.enat n2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ty.tbool (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.ebool b2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ty.tnat (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.eadd a2 b2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty B2 (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.elet a2 body2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.elam Alam body)) =>
              ExTy.mk (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tarrow A2 B2) (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)) B2
                (And2.mk (Eq.{1} Ty (Ty.tarrow A2 B2) (Ty.tarrow Alam B2)) (HasTy (Ctx.cons Alam Gv) body B2)
                  (tarrow_cong A2 Alam B2 B2 (exp_ty_proj_inj lamTyOf (Exp.elam A2 body2) (Exp.elam Alam body) heq) (Eq.refl.{1} Ty B2))
                  (Eq.subst.{1} Ctx (fun (g : Ctx) => HasTy g body B2)
                     (Ctx.cons A2 Gv) (Ctx.cons Alam Gv)
                     (Eq.subst.{1} Ty (fun (x : Ty) => Eq.{1} Ctx (Ctx.cons A2 Gv) (Ctx.cons x Gv)) A2 Alam (exp_ty_proj_inj lamTyOf (Exp.elam A2 body2) (Exp.elam Alam body) heq) (Eq.refl.{1} Ctx (Ctx.cons A2 Gv)))
                     (Eq.subst.{1} Exp (fun (x : Exp) => HasTy (Ctx.cons A2 Gv) x B2) body2 body (proj_inj lamBodyOf (Exp.elam A2 body2) (Exp.elam Alam body) heq) dbody)))
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty B2 (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.eapp f2 a2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Tif (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Afix2 (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.efix Afix2 body2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tprod Ap Bp) (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.epair a2 b2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ap (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.efst p2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Bp (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.esnd p2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tsum Ai Bi) (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.einl Bi v2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tsum Ai Bi) (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.einr Ai v2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (Alam : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.elam Alam body)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Cc (Ty.tarrow Alam B)) (HasTy (Ctx.cons Alam Gv) body B)))
                (exp_noconf (Exp.ecase s2 l2 r2) (Exp.elam Alam body) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }
    -- fix inversion: a typed `efix Afix body` has body : Afix in the self-extended context,
    -- and its type is exactly Afix. (The 8 non-fix derivations are impossible by no-confusion.)
    fn hasty_fix_inv(G: Ctx, e: Exp, Tf: Ty, d: HasTy G e Tf)
      -> ((Afix : Ty) -> (body : Exp) -> Eq.{1} Exp e (Exp.efix Afix body)
            -> And2 (Eq.{1} Ty Tf Afix) (HasTy (Ctx.cons Afix G) body Afix)) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty T2 Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.evar n2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty Ty.tnat Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.enat n2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty Ty.tbool Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.ebool b2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty Ty.tnat Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.eadd a2 b2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty B2 Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.elet a2 body2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty (Ty.tarrow A2 B2) Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.elam A2 body2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty B2 Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.eapp f2 a2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty Tif Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty (Ty.tprod Ap Bp) Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.epair a2 b2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty Ap Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.efst p2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty Bp Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.esnd p2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty (Ty.tsum Ai Bi) Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.einl Bi v2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty (Ty.tsum Ai Bi) Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.einr Ai v2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.efix Afix body)) =>
              False.rec.{0} (fun (_ : False) => And2 (Eq.{1} Ty Cc Afix) (HasTy (Ctx.cons Afix Gv) body Afix))
                (exp_noconf (Exp.ecase s2 l2 r2) (Exp.efix Afix body) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, A2, body2, dbody) => fun (Afix : Ty) (body : Exp) (heq : Eq.{1} Exp (Exp.efix A2 body2) (Exp.efix Afix body)) =>
              And2.mk (Eq.{1} Ty A2 Afix) (HasTy (Ctx.cons Afix Gv) body Afix)
                (exp_ty_proj_inj fixTyOf (Exp.efix A2 body2) (Exp.efix Afix body) heq)
                (Eq.subst.{1} Ctx (fun (g : Ctx) => HasTy g body Afix) (Ctx.cons A2 Gv) (Ctx.cons Afix Gv)
                   (Eq.subst.{1} Ty (fun (x : Ty) => Eq.{1} Ctx (Ctx.cons A2 Gv) (Ctx.cons x Gv)) A2 Afix (exp_ty_proj_inj fixTyOf (Exp.efix A2 body2) (Exp.efix Afix body) heq) (Eq.refl.{1} Ctx (Ctx.cons A2 Gv)))
                   (Eq.subst.{1} Exp (fun (x : Exp) => HasTy (Ctx.cons A2 Gv) x Afix) body2 body (proj_inj fixBodyOf (Exp.efix A2 body2) (Exp.efix Afix body) heq)
                      (Eq.subst.{1} Ty (fun (x : Ty) => HasTy (Ctx.cons A2 Gv) body2 x) A2 Afix (exp_ty_proj_inj fixTyOf (Exp.efix A2 body2) (Exp.efix Afix body) heq) dbody)))
        }
    }

    -- pair inversion: a typed `epair a b` has its type a product of the components' types.
    fn hasty_pair_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((a : Exp) -> (b : Exp) -> Eq.{1} Exp e (Exp.epair a b)
            -> ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty T (Ty.tprod A B)) (And2 (HasTy G a A) (HasTy G b B))))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty T2 (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.evar n2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ty.tnat (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.enat n2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ty.tbool (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.ebool b2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ty.tnat (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.eadd a2 b2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty B2 (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.elet a2 body2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tarrow A2 B2) (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.elam A2 body2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty B2 (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.eapp f2 a2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Tif (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Afix2 (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.efix Afix2 body2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.epair a b)) =>
              ExTy.mk (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tprod Ap Bp) (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))) Ap
                (ExTy.mk (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tprod Ap Bp) (Ty.tprod Ap B)) (And2 (HasTy Gv a Ap) (HasTy Gv b B))) Bp
                  (And2.mk (Eq.{1} Ty (Ty.tprod Ap Bp) (Ty.tprod Ap Bp)) (And2 (HasTy Gv a Ap) (HasTy Gv b Bp))
                    (Eq.refl.{1} Ty (Ty.tprod Ap Bp))
                    (And2.mk (HasTy Gv a Ap) (HasTy Gv b Bp)
                      (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x Ap) a2 a (proj_inj pairLof (Exp.epair a2 b2) (Exp.epair a b) heq) da)
                      (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x Bp) b2 b (proj_inj pairRof (Exp.epair a2 b2) (Exp.epair a b) heq) db))))
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ap (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.efst p2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Bp (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.esnd p2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tsum Ai Bi) (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.einl Bi v2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tsum Ai Bi) (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.einr Ai v2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (a : Exp) (b : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.epair a b)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Cc (Ty.tprod A B)) (And2 (HasTy Gv a A) (HasTy Gv b B)))))
                (exp_noconf (Exp.ecase s2 l2 r2) (Exp.epair a b) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }
    -- fst inversion: a typed `efst p` has `p` of some product type whose first component is T.
    fn hasty_fst_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((p : Exp) -> Eq.{1} Exp e (Exp.efst p) -> ExTy (fun (B : Ty) => HasTy G p (Ty.tprod T B))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod T2 B))) (exp_noconf (Exp.evar n2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod Ty.tnat B))) (exp_noconf (Exp.enat n2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod Ty.tbool B))) (exp_noconf (Exp.ebool b2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod Ty.tnat B))) (exp_noconf (Exp.eadd a2 b2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod B2 B))) (exp_noconf (Exp.elet a2 body2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod (Ty.tarrow A2 B2) B))) (exp_noconf (Exp.elam A2 body2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod B2 B))) (exp_noconf (Exp.eapp f2 a2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod Tif B))) (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod Afix2 B))) (exp_noconf (Exp.efix Afix2 body2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod (Ty.tprod Ap Bp) B))) (exp_noconf (Exp.epair a2 b2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, A2, B2, dp) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.efst p)) =>
              ExTy.mk (fun (B : Ty) => HasTy Gv p (Ty.tprod A2 B)) B2
                (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x (Ty.tprod A2 B2)) p2 p (proj_inj fstArgOf (Exp.efst p2) (Exp.efst p) heq) dp)
          | HasTy.tsnd(Gv, p2, A2, B2, dp) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod B2 B))) (exp_noconf (Exp.esnd p2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod (Ty.tsum Ai Bi) B))) (exp_noconf (Exp.einl Bi v2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod (Ty.tsum Ai Bi) B))) (exp_noconf (Exp.einr Ai v2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.efst p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => HasTy Gv p (Ty.tprod Cc B))) (exp_noconf (Exp.ecase s2 l2 r2) (Exp.efst p) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }
    -- snd inversion: a typed `esnd p` has `p` of some product type whose second component is T.
    fn hasty_snd_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((p : Exp) -> Eq.{1} Exp e (Exp.esnd p) -> ExTy (fun (A : Ty) => HasTy G p (Ty.tprod A T))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A T2))) (exp_noconf (Exp.evar n2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A Ty.tnat))) (exp_noconf (Exp.enat n2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A Ty.tbool))) (exp_noconf (Exp.ebool b2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A Ty.tnat))) (exp_noconf (Exp.eadd a2 b2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A B2))) (exp_noconf (Exp.elet a2 body2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A (Ty.tarrow A2 B2)))) (exp_noconf (Exp.elam A2 body2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A B2))) (exp_noconf (Exp.eapp f2 a2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A Tif))) (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A Afix2))) (exp_noconf (Exp.efix Afix2 body2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A (Ty.tprod Ap Bp)))) (exp_noconf (Exp.epair a2 b2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, A2, B2, dp) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A A2))) (exp_noconf (Exp.efst p2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A (Ty.tsum Ai Bi)))) (exp_noconf (Exp.einl Bi v2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A (Ty.tsum Ai Bi)))) (exp_noconf (Exp.einr Ai v2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.esnd p)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => HasTy Gv p (Ty.tprod A Cc))) (exp_noconf (Exp.ecase s2 l2 r2) (Exp.esnd p) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, A2, B2, dp) => fun (p : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.esnd p)) =>
              ExTy.mk (fun (A : Ty) => HasTy Gv p (Ty.tprod A B2)) A2
                (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x (Ty.tprod A2 B2)) p2 p (proj_inj sndArgOf (Exp.esnd p2) (Exp.esnd p) heq) dp)
        }
    }

    -- inl inversion: a typed `einl Bx vx` has `vx` of the left summand, and its type is a sum.
    fn hasty_inl_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((Bx : Ty) -> (vx : Exp) -> Eq.{1} Exp e (Exp.einl Bx vx)
            -> ExTy (fun (A : Ty) => And2 (Eq.{1} Ty T (Ty.tsum A Bx)) (HasTy G vx A))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty T2 (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.evar n2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty Ty.tnat (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.enat n2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty Ty.tbool (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.ebool b2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty Ty.tnat (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.eadd a2 b2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty B2 (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.elet a2 body2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty (Ty.tarrow A2 B2) (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.elam A2 body2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty B2 (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.eapp f2 a2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty Tif (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty Afix2 (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.efix Afix2 body2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty (Ty.tprod Ap Bp) (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.epair a2 b2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty Ap (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.efst p2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty Bp (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.esnd p2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, B2, v2, A2, dv) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.einl B2 v2) (Exp.einl Bx vx)) =>
              ExTy.mk (fun (A : Ty) => And2 (Eq.{1} Ty (Ty.tsum A2 B2) (Ty.tsum A Bx)) (HasTy Gv vx A)) A2
                (And2.mk (Eq.{1} Ty (Ty.tsum A2 B2) (Ty.tsum A2 Bx)) (HasTy Gv vx A2)
                  (tsum_cong A2 A2 B2 Bx (Eq.refl.{1} Ty A2) (exp_ty_proj_inj inlTyOf (Exp.einl B2 v2) (Exp.einl Bx vx) heq))
                  (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x A2) v2 vx (proj_inj inlValOf (Exp.einl B2 v2) (Exp.einl Bx vx) heq) dv))
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty (Ty.tsum Ai Bi) (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.einr Ai v2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (Bx : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.einl Bx vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => And2 (Eq.{1} Ty Cc (Ty.tsum A Bx)) (HasTy Gv vx A))) (exp_noconf (Exp.ecase s2 l2 r2) (Exp.einl Bx vx) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }
    -- inr inversion (symmetric to inl).
    fn hasty_inr_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((Ax : Ty) -> (vx : Exp) -> Eq.{1} Exp e (Exp.einr Ax vx)
            -> ExTy (fun (B : Ty) => And2 (Eq.{1} Ty T (Ty.tsum Ax B)) (HasTy G vx B))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty T2 (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.evar n2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ty.tnat (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.enat n2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ty.tbool (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.ebool b2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ty.tnat (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.eadd a2 b2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty B2 (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.elet a2 body2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tarrow A2 B2) (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.elam A2 body2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty B2 (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.eapp f2 a2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Tif (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Afix2 (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.efix Afix2 body2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tprod Ap Bp) (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.epair a2 b2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Ap (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.efst p2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Bp (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.esnd p2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tsum Ai Bi) (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.einl Bi v2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, A2, v2, B2, dv) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.einr A2 v2) (Exp.einr Ax vx)) =>
              ExTy.mk (fun (B : Ty) => And2 (Eq.{1} Ty (Ty.tsum A2 B2) (Ty.tsum Ax B)) (HasTy Gv vx B)) B2
                (And2.mk (Eq.{1} Ty (Ty.tsum A2 B2) (Ty.tsum Ax B2)) (HasTy Gv vx B2)
                  (tsum_cong A2 Ax B2 B2 (exp_ty_proj_inj inrTyOf (Exp.einr A2 v2) (Exp.einr Ax vx) heq) (Eq.refl.{1} Ty B2))
                  (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x B2) v2 vx (proj_inj inrValOf (Exp.einr A2 v2) (Exp.einr Ax vx) heq) dv))
          | HasTy.tcase(Gv, s2, l2, r2, Ac, Bc, Cc, ds, dl, dr) => fun (Ax : Ty) (vx : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.einr Ax vx)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : Ty) => And2 (Eq.{1} Ty Cc (Ty.tsum Ax B)) (HasTy Gv vx B))) (exp_noconf (Exp.ecase s2 l2 r2) (Exp.einr Ax vx) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }
    -- case inversion: a typed `ecase s l r : T` has `s : tsum A B`, `l : T` under A, `r : T` under B.
    fn hasty_case_inv(G: Ctx, e: Exp, T: Ty, d: HasTy G e T)
      -> ((s : Exp) -> (l : Exp) -> (r : Exp) -> Eq.{1} Exp e (Exp.ecase s l r)
            -> ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy G s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A G) l T) (HasTy (Ctx.cons B G) r T))))) {
        match d {
          | HasTy.tvar(Gv, n2, T2, lk2) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.evar n2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l T2) (HasTy (Ctx.cons B Gv) r T2))))) (exp_noconf (Exp.evar n2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tnat(Gv, n2) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.enat n2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l Ty.tnat) (HasTy (Ctx.cons B Gv) r Ty.tnat))))) (exp_noconf (Exp.enat n2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tbool(Gv, b2) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.ebool b2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l Ty.tbool) (HasTy (Ctx.cons B Gv) r Ty.tbool))))) (exp_noconf (Exp.ebool b2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tadd(Gv, a2, b2, da, db) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.eadd a2 b2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l Ty.tnat) (HasTy (Ctx.cons B Gv) r Ty.tnat))))) (exp_noconf (Exp.eadd a2 b2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlet(Gv, a2, body2, A2, B2, da, dbody) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.elet a2 body2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l B2) (HasTy (Ctx.cons B Gv) r B2))))) (exp_noconf (Exp.elet a2 body2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tlam(Gv, A2, body2, B2, dbody) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.elam A2 body2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l (Ty.tarrow A2 B2)) (HasTy (Ctx.cons B Gv) r (Ty.tarrow A2 B2)))))) (exp_noconf (Exp.elam A2 body2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tapp(Gv, f2, a2, A2, B2, df, da) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.eapp f2 a2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l B2) (HasTy (Ctx.cons B Gv) r B2))))) (exp_noconf (Exp.eapp f2 a2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tif(Gv, cnd2, thn2, els2, Tif, dc, dt, de) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.eif cnd2 thn2 els2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l Tif) (HasTy (Ctx.cons B Gv) r Tif))))) (exp_noconf (Exp.eif cnd2 thn2 els2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfix(Gv, Afix2, body2, dbody) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.efix Afix2 body2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l Afix2) (HasTy (Ctx.cons B Gv) r Afix2))))) (exp_noconf (Exp.efix Afix2 body2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tpair(Gv, a2, b2, Ap, Bp, da, db) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.epair a2 b2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l (Ty.tprod Ap Bp)) (HasTy (Ctx.cons B Gv) r (Ty.tprod Ap Bp)))))) (exp_noconf (Exp.epair a2 b2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tfst(Gv, p2, Ap, Bp, dp) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.efst p2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l Ap) (HasTy (Ctx.cons B Gv) r Ap))))) (exp_noconf (Exp.efst p2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tsnd(Gv, p2, Ap, Bp, dp) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.esnd p2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l Bp) (HasTy (Ctx.cons B Gv) r Bp))))) (exp_noconf (Exp.esnd p2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinl(Gv, Bi, v2, Ai, dv) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.einl Bi v2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l (Ty.tsum Ai Bi)) (HasTy (Ctx.cons B Gv) r (Ty.tsum Ai Bi)))))) (exp_noconf (Exp.einl Bi v2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tinr(Gv, Ai, v2, Bi, dv) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.einr Ai v2) (Exp.ecase s l r)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l (Ty.tsum Ai Bi)) (HasTy (Ctx.cons B Gv) r (Ty.tsum Ai Bi)))))) (exp_noconf (Exp.einr Ai v2) (Exp.ecase s l r) (Eq.refl.{1} Bool Bool.false) heq)
          | HasTy.tcase(Gv, s2, l2, r2, A2, B2, C2, ds, dl, dr) => fun (s : Exp) (l : Exp) (r : Exp) (heq : Eq.{1} Exp (Exp.ecase s2 l2 r2) (Exp.ecase s l r)) =>
              ExTy.mk (fun (A : Ty) => ExTy (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A B)) (And2 (HasTy (Ctx.cons A Gv) l C2) (HasTy (Ctx.cons B Gv) r C2)))) A2
                (ExTy.mk (fun (B : Ty) => And2 (HasTy Gv s (Ty.tsum A2 B)) (And2 (HasTy (Ctx.cons A2 Gv) l C2) (HasTy (Ctx.cons B Gv) r C2))) B2
                  (And2.mk (HasTy Gv s (Ty.tsum A2 B2)) (And2 (HasTy (Ctx.cons A2 Gv) l C2) (HasTy (Ctx.cons B2 Gv) r C2))
                    (Eq.subst.{1} Exp (fun (x : Exp) => HasTy Gv x (Ty.tsum A2 B2)) s2 s (proj_inj caseScrutOf (Exp.ecase s2 l2 r2) (Exp.ecase s l r) heq) ds)
                    (And2.mk (HasTy (Ctx.cons A2 Gv) l C2) (HasTy (Ctx.cons B2 Gv) r C2)
                      (Eq.subst.{1} Exp (fun (x : Exp) => HasTy (Ctx.cons A2 Gv) x C2) l2 l (proj_inj caseLof (Exp.ecase s2 l2 r2) (Exp.ecase s l r) heq) dl)
                      (Eq.subst.{1} Exp (fun (x : Exp) => HasTy (Ctx.cons B2 Gv) x C2) r2 r (proj_inj caseRof (Exp.ecase s2 l2 r2) (Exp.ecase s l r) heq) dr))))
        }
    }

    -- ===== Small-step reduction relation and PRESERVATION =====
    inductive Step : Exp -> Exp -> Prop
      | s_add_l : (a : Exp) -> (a2 : Exp) -> (b : Exp) -> Step a a2 -> Step (Exp.eadd a b) (Exp.eadd a2 b)
      | s_add_r : (a : Exp) -> (b : Exp) -> (b2 : Exp) -> Step b b2 -> Step (Exp.eadd a b) (Exp.eadd a b2)
      | s_add   : (m : Nat) -> (n : Nat) -> Step (Exp.eadd (Exp.enat m) (Exp.enat n)) (Exp.enat (addN m n))
      | s_let_a : (a : Exp) -> (a2 : Exp) -> (body : Exp) -> Step a a2 -> Step (Exp.elet a body) (Exp.elet a2 body)
      | s_let   : (v : Exp) -> (body : Exp) -> Step (Exp.elet v body) (subst body Nat.zero v)
      | s_app_l : (f : Exp) -> (f2 : Exp) -> (a : Exp) -> Step f f2 -> Step (Exp.eapp f a) (Exp.eapp f2 a)
      | s_app_r : (f : Exp) -> (a : Exp) -> (a2 : Exp) -> Step a a2 -> Step (Exp.eapp f a) (Exp.eapp f a2)
      | s_beta  : (A : Ty) -> (body : Exp) -> (v : Exp) -> Step (Exp.eapp (Exp.elam A body) v) (subst body Nat.zero v)
      | s_if_c  : (c : Exp) -> (c2 : Exp) -> (t : Exp) -> (el : Exp) -> Step c c2 -> Step (Exp.eif c t el) (Exp.eif c2 t el)
      | s_if_t  : (t : Exp) -> (el : Exp) -> Step (Exp.eif (Exp.ebool Bool.true) t el) t
      | s_if_f  : (t : Exp) -> (el : Exp) -> Step (Exp.eif (Exp.ebool Bool.false) t el) el
      | s_fix   : (A : Ty) -> (body : Exp) -> Step (Exp.efix A body) (subst body Nat.zero (Exp.efix A body))
      | s_fst_l : (p : Exp) -> (p2 : Exp) -> Step p p2 -> Step (Exp.efst p) (Exp.efst p2)
      | s_fst   : (a : Exp) -> (b : Exp) -> Step (Exp.efst (Exp.epair a b)) a
      | s_snd_l : (p : Exp) -> (p2 : Exp) -> Step p p2 -> Step (Exp.esnd p) (Exp.esnd p2)
      | s_snd   : (a : Exp) -> (b : Exp) -> Step (Exp.esnd (Exp.epair a b)) b
      | s_case_l : (s : Exp) -> (s2 : Exp) -> (l : Exp) -> (r : Exp) -> Step s s2 -> Step (Exp.ecase s l r) (Exp.ecase s2 l r)
      | s_case_inl : (B : Ty) -> (v : Exp) -> (l : Exp) -> (r : Exp) -> Step (Exp.ecase (Exp.einl B v) l r) (subst l Nat.zero v)
      | s_case_inr : (A : Ty) -> (v : Exp) -> (l : Exp) -> (r : Exp) -> Step (Exp.ecase (Exp.einr A v) l r) (subst r Nat.zero v)
"#;

/// The preservation theorem proper, plus per-redex standalone lemmas (split from
/// [`PRESERVATION`] so it can be iterated/diagnosed separately).
pub const PRESERVATION_THM: &str = r#"
    -- Standalone sum-redex preservation lemmas (each is one redex arm of `preservation`).
    fn pres_case_inl(B: Ty, v: Exp, l: Exp, r: Exp)
      -> ((G : Ctx) -> (T : Ty) -> HasTy G (Exp.ecase (Exp.einl B v) l r) T -> HasTy G (subst l Nat.zero v) T) {
        fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.ecase (Exp.einl B v) l r) T) =>
            match hasty_case_inv G (Exp.ecase (Exp.einl B v) l r) T d (Exp.einl B v) l r (Eq.refl.{1} Exp (Exp.ecase (Exp.einl B v) l r)) {
              | ExTy.mk(A, ExTy.mk(Br, And2.mk(ds, And2.mk(dl, dr)))) =>
                  match hasty_inl_inv G (Exp.einl B v) (Ty.tsum A Br) ds B v (Eq.refl.{1} Exp (Exp.einl B v)) {
                    | ExTy.mk(A2, And2.mk(eqT, dv)) =>
                        subst_preserves A G l T v dl
                          (Eq.subst.{1} Ty (fun (x : Ty) => HasTy G v x) A2 A
                             (Eq.symm.{1} Ty A A2 (ty_proj_inj fstSum (Ty.tsum A Br) (Ty.tsum A2 B) eqT)) dv)
                  }
            }
    }
    fn pres_case_inr(A: Ty, v: Exp, l: Exp, r: Exp)
      -> ((G : Ctx) -> (T : Ty) -> HasTy G (Exp.ecase (Exp.einr A v) l r) T -> HasTy G (subst r Nat.zero v) T) {
        fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.ecase (Exp.einr A v) l r) T) =>
            match hasty_case_inv G (Exp.ecase (Exp.einr A v) l r) T d (Exp.einr A v) l r (Eq.refl.{1} Exp (Exp.ecase (Exp.einr A v) l r)) {
              | ExTy.mk(Al, ExTy.mk(B, And2.mk(ds, And2.mk(dl, dr)))) =>
                  match hasty_inr_inv G (Exp.einr A v) (Ty.tsum Al B) ds A v (Eq.refl.{1} Exp (Exp.einr A v)) {
                    | ExTy.mk(B2, And2.mk(eqT, dv)) =>
                        subst_preserves B G r T v dr
                          (Eq.subst.{1} Ty (fun (x : Ty) => HasTy G v x) B2 B
                             (Eq.symm.{1} Ty B B2 (ty_proj_inj sndSum (Ty.tsum Al B) (Ty.tsum A B2) eqT)) dv)
                  }
            }
    }

    -- **PRESERVATION**: reduction preserves typing. By induction on the reduction; redexes
    -- are discharged by `subst_preserves` (β/let) or directly, congruences by the induction
    -- hypothesis after inverting the typing of the compound term.
    fn preservation(e: Exp, e2: Exp, st: Step e e2)
      -> ((G : Ctx) -> (T : Ty) -> HasTy G e T -> HasTy G e2 T) {
        match st {
          | Step.s_add_l(a, a2, b, sta) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.eadd a b) T) =>
              match hasty_add_inv G (Exp.eadd a b) T d a b (Eq.refl.{1} Exp (Exp.eadd a b)) {
                | And2.mk(ha, And2.mk(hb, hT)) =>
                    Eq.subst.{1} Ty (fun (x : Ty) => HasTy G (Exp.eadd a2 b) x) Ty.tnat T (Eq.symm.{1} Ty T Ty.tnat hT)
                      (HasTy.tadd G a2 b (sta.rec G Ty.tnat ha) hb)
              }
          | Step.s_add_r(a, b, b2, stb) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.eadd a b) T) =>
              match hasty_add_inv G (Exp.eadd a b) T d a b (Eq.refl.{1} Exp (Exp.eadd a b)) {
                | And2.mk(ha, And2.mk(hb, hT)) =>
                    Eq.subst.{1} Ty (fun (x : Ty) => HasTy G (Exp.eadd a b2) x) Ty.tnat T (Eq.symm.{1} Ty T Ty.tnat hT)
                      (HasTy.tadd G a b2 ha (stb.rec G Ty.tnat hb))
              }
          | Step.s_add(m, n) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.eadd (Exp.enat m) (Exp.enat n)) T) =>
              match hasty_add_inv G (Exp.eadd (Exp.enat m) (Exp.enat n)) T d (Exp.enat m) (Exp.enat n) (Eq.refl.{1} Exp (Exp.eadd (Exp.enat m) (Exp.enat n))) {
                | And2.mk(ha, And2.mk(hb, hT)) =>
                    Eq.subst.{1} Ty (fun (x : Ty) => HasTy G (Exp.enat (addN m n)) x) Ty.tnat T (Eq.symm.{1} Ty T Ty.tnat hT)
                      (HasTy.tnat G (addN m n))
              }
          | Step.s_let_a(a, a2, body, sta) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.elet a body) T) =>
              match hasty_let_inv G (Exp.elet a body) T d a body (Eq.refl.{1} Exp (Exp.elet a body)) {
                | ExTy.mk(A, And2.mk(da, dbody)) => HasTy.tlet G a2 body A T (sta.rec G A da) dbody
              }
          | Step.s_let(v, body) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.elet v body) T) =>
              match hasty_let_inv G (Exp.elet v body) T d v body (Eq.refl.{1} Exp (Exp.elet v body)) {
                | ExTy.mk(A, And2.mk(dv, dbody)) => subst_preserves A G body T v dbody dv
              }
          | Step.s_app_l(f, f2, a, stf) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.eapp f a) T) =>
              match hasty_app_inv G (Exp.eapp f a) T d f a (Eq.refl.{1} Exp (Exp.eapp f a)) {
                | ExTy.mk(A, And2.mk(df, da)) => HasTy.tapp G f2 a A T (stf.rec G (Ty.tarrow A T) df) da
              }
          | Step.s_app_r(f, a, a2, sta) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.eapp f a) T) =>
              match hasty_app_inv G (Exp.eapp f a) T d f a (Eq.refl.{1} Exp (Exp.eapp f a)) {
                | ExTy.mk(A, And2.mk(df, da)) => HasTy.tapp G f a2 A T df (sta.rec G A da)
              }
          | Step.s_beta(A, body, v) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.eapp (Exp.elam A body) v) T) =>
              match hasty_app_inv G (Exp.eapp (Exp.elam A body) v) T d (Exp.elam A body) v (Eq.refl.{1} Exp (Exp.eapp (Exp.elam A body) v)) {
                | ExTy.mk(A2, And2.mk(df, dv)) =>
                    match hasty_lam_inv G (Exp.elam A body) (Ty.tarrow A2 T) df A body (Eq.refl.{1} Exp (Exp.elam A body)) {
                      | ExTy.mk(B, And2.mk(eqArrow, dbody)) =>
                          subst_preserves A G body T v
                            (Eq.subst.{1} Ty (fun (x : Ty) => HasTy (Ctx.cons A G) body x) B T
                               (Eq.symm.{1} Ty T B (ty_proj_inj codOf (Ty.tarrow A2 T) (Ty.tarrow A B) eqArrow)) dbody)
                            (Eq.subst.{1} Ty (fun (x : Ty) => HasTy G v x) A2 A
                               (ty_proj_inj domOf (Ty.tarrow A2 T) (Ty.tarrow A B) eqArrow) dv)
                    }
              }
          | Step.s_if_c(c, c2, t, el, stc) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.eif c t el) T) =>
              match hasty_if_inv G (Exp.eif c t el) T d c t el (Eq.refl.{1} Exp (Exp.eif c t el)) {
                | And2.mk(dc, And2.mk(dt, de)) => HasTy.tif G c2 t el T (stc.rec G Ty.tbool dc) dt de
              }
          | Step.s_if_t(t, el) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.eif (Exp.ebool Bool.true) t el) T) =>
              match hasty_if_inv G (Exp.eif (Exp.ebool Bool.true) t el) T d (Exp.ebool Bool.true) t el (Eq.refl.{1} Exp (Exp.eif (Exp.ebool Bool.true) t el)) {
                | And2.mk(dc, And2.mk(dt, de)) => dt
              }
          | Step.s_if_f(t, el) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.eif (Exp.ebool Bool.false) t el) T) =>
              match hasty_if_inv G (Exp.eif (Exp.ebool Bool.false) t el) T d (Exp.ebool Bool.false) t el (Eq.refl.{1} Exp (Exp.eif (Exp.ebool Bool.false) t el)) {
                | And2.mk(dc, And2.mk(dt, de)) => de
              }
          | Step.s_fix(A, body) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.efix A body) T) =>
              match hasty_fix_inv G (Exp.efix A body) T d A body (Eq.refl.{1} Exp (Exp.efix A body)) {
                | And2.mk(eqT, dbody) =>
                    Eq.subst.{1} Ty (fun (x : Ty) => HasTy G (subst(body)(Nat.zero)(Exp.efix(A, body))) x) A T
                      (Eq.symm.{1} Ty T A eqT)
                      (subst_preserves A G body A (Exp.efix(A, body)) dbody
                         (Eq.subst.{1} Ty (fun (x : Ty) => HasTy G (Exp.efix(A, body)) x) T A eqT d))
              }
          | Step.s_fst_l(p, p2, stp) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.efst p) T) =>
              match hasty_fst_inv G (Exp.efst p) T d p (Eq.refl.{1} Exp (Exp.efst p)) {
                | ExTy.mk(B, dp) => HasTy.tfst G p2 T B (stp.rec G (Ty.tprod T B) dp)
              }
          | Step.s_fst(a, b) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.efst (Exp.epair a b)) T) =>
              match hasty_fst_inv G (Exp.efst (Exp.epair a b)) T d (Exp.epair a b) (Eq.refl.{1} Exp (Exp.efst (Exp.epair a b))) {
                | ExTy.mk(B, dpair) =>
                    match hasty_pair_inv G (Exp.epair a b) (Ty.tprod T B) dpair a b (Eq.refl.{1} Exp (Exp.epair a b)) {
                      | ExTy.mk(A2, ExTy.mk(B2, And2.mk(eqProd, And2.mk(da, db)))) =>
                          Eq.subst.{1} Ty (fun (x : Ty) => HasTy G a x) A2 T
                            (Eq.symm.{1} Ty T A2 (ty_proj_inj fstTy (Ty.tprod T B) (Ty.tprod A2 B2) eqProd))
                            da
                    }
              }
          | Step.s_snd_l(p, p2, stp) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.esnd p) T) =>
              match hasty_snd_inv G (Exp.esnd p) T d p (Eq.refl.{1} Exp (Exp.esnd p)) {
                | ExTy.mk(A, dp) => HasTy.tsnd G p2 A T (stp.rec G (Ty.tprod A T) dp)
              }
          | Step.s_snd(a, b) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.esnd (Exp.epair a b)) T) =>
              match hasty_snd_inv G (Exp.esnd (Exp.epair a b)) T d (Exp.epair a b) (Eq.refl.{1} Exp (Exp.esnd (Exp.epair a b))) {
                | ExTy.mk(A, dpair) =>
                    match hasty_pair_inv G (Exp.epair a b) (Ty.tprod A T) dpair a b (Eq.refl.{1} Exp (Exp.epair a b)) {
                      | ExTy.mk(A2, ExTy.mk(B2, And2.mk(eqProd, And2.mk(da, db)))) =>
                          Eq.subst.{1} Ty (fun (x : Ty) => HasTy G b x) B2 T
                            (Eq.symm.{1} Ty T B2 (ty_proj_inj sndTy (Ty.tprod A T) (Ty.tprod A2 B2) eqProd))
                            db
                    }
              }
          | Step.s_case_l(s, s2, l, r, sts) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.ecase s l r) T) =>
              match hasty_case_inv G (Exp.ecase s l r) T d s l r (Eq.refl.{1} Exp (Exp.ecase s l r)) {
                | ExTy.mk(A, ExTy.mk(B, And2.mk(ds, And2.mk(dl, dr)))) =>
                    HasTy.tcase G s2 l r A B T (sts.rec G (Ty.tsum A B) ds) dl dr
              }
          | Step.s_case_inl(B, v, l, r) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.ecase (Exp.einl B v) l r) T) =>
              match hasty_case_inv G (Exp.ecase (Exp.einl B v) l r) T d (Exp.einl B v) l r (Eq.refl.{1} Exp (Exp.ecase (Exp.einl B v) l r)) {
                | ExTy.mk(A, ExTy.mk(Br, And2.mk(ds, And2.mk(dl, dr)))) =>
                    match hasty_inl_inv G (Exp.einl B v) (Ty.tsum A Br) ds B v (Eq.refl.{1} Exp (Exp.einl B v)) {
                      | ExTy.mk(A2, And2.mk(eqT, dv)) =>
                          subst_preserves A G l T v dl
                            (Eq.subst.{1} Ty (fun (x : Ty) => HasTy G v x) A2 A
                               (Eq.symm.{1} Ty A A2 (ty_proj_inj fstSum (Ty.tsum A Br) (Ty.tsum A2 B) eqT)) dv)
                    }
              }
          | Step.s_case_inr(A, v, l, r) => fun (G : Ctx) (T : Ty) (d : HasTy G (Exp.ecase (Exp.einr A v) l r) T) =>
              match hasty_case_inv G (Exp.ecase (Exp.einr A v) l r) T d (Exp.einr A v) l r (Eq.refl.{1} Exp (Exp.ecase (Exp.einr A v) l r)) {
                | ExTy.mk(Al, ExTy.mk(B, And2.mk(ds, And2.mk(dl, dr)))) =>
                    match hasty_inr_inv G (Exp.einr A v) (Ty.tsum Al B) ds A v (Eq.refl.{1} Exp (Exp.einr A v)) {
                      | ExTy.mk(B2, And2.mk(eqT, dv)) =>
                          subst_preserves B G r T v dr
                            (Eq.subst.{1} Ty (fun (x : Ty) => HasTy G v x) B2 B
                               (Eq.symm.{1} Ty B B2 (ty_proj_inj sndSum (Ty.tsum Al B) (Ty.tsum A B2) eqT)) dv)
                    }
              }
        }
    }
"#;

/// A session that additionally loads the [`PRESERVATION`] development (weakening so far).
pub fn preservation_session() -> Result<Session, String> {
    let mut s = safety_session()?;
    s.run(PRESERVATION)?;
    s.run(PRESERVATION_THM)?;
    Ok(s)
}

/// A *lighter* session for iterating on the preservation development: it skips the slow
/// `STEP_LEMMAS` + `PROGRESS` consts (which preservation does not depend on), loading only
/// the evaluator, the safety scaffolding's extractors, and the preservation development.
pub fn preservation_only_session() -> Result<Session, String> {
    let mut s = runnable_session()?;
    s.run(SAFETY_SCAFFOLD)?;
    s.run(PRESERVATION)?;
    s.run(PRESERVATION_THM)?;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A `Nat` literal as a `succ`/`zero` chain (for building object-language terms in tests).
    fn nat(n: u64) -> String {
        let mut s = String::from("Nat.zero");
        for _ in 0..n {
            s = format!("Nat.succ({s})");
        }
        s
    }

    /// The whole development — recursive types, the checker, and the soundness theorem
    /// (including the `eapp` case) — elaborates and is kernel-checked.
    #[test]
    fn lang_and_soundness_check() {
        let s = session().expect("prelude + simply-typed language + soundness should check");
        for n in [
            "Exp", "Ty", "Lookup", "HasTy", "tyeq", "tyeq_sound", "arrow_inv", "synth", "ok",
            "ok_sound", "synth_complete", "ok_complete", "ok_false_not_welltyped",
        ] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// The **type-safety scaffolding** (canonical forms + inversions + helpers) and the
    /// **progress** theorem elaborate and are kernel-checked.
    #[test]
    fn safety_scaffold_check() {
        let s = safety_session().expect("safety scaffolding + progress should check");
        for n in [
            "canon_arrow", "canon_nat", "canon_bool", "natlit_inv", "boollit_inv", "lam_inv",
            "nilLookupFalse", "bool_cases", "orB_false_left", "isSome_omap", "progress",
        ] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// The **weakening foundation** (`insertCtx`, `lookup_weaken`) — and the refactored
    /// `shiftIdx` — elaborate and are kernel-checked.
    #[test]
    fn weakening_foundation_check() {
        let s = preservation_session().expect("weakening + substitution + preservation should check");
        for n in [
            "shiftIdx", "insertCtx", "lookup_weaken", "HasTy_weaken", "applySub", "liftSub_respects",
            "subst_lemma", "subst_preserves", "Step", "preservation",
        ] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// **Preservation in action.** `(λx:tnat. x) 0` β-reduces (via `Step.s_beta`); applying
    /// `preservation` transports its typing across the step, yielding a kernel-checked proof
    /// that the reduct is still well-typed at the same type.
    #[test]
    fn preservation_applies_to_a_step() {
        let mut s = preservation_session().unwrap();
        s.run("def prog : Exp := Exp.eapp(Exp.elam(Ty.tnat, Exp.evar(Nat.zero)), Exp.enat(Nat.zero))").unwrap();
        s.run(
            "def the_step : Step prog (subst(Exp.evar(Nat.zero))(Nat.zero)(Exp.enat(Nat.zero))) := \
               Step.s_beta Ty.tnat (Exp.evar(Nat.zero)) (Exp.enat(Nat.zero))",
        )
        .unwrap();
        s.run(
            "def preserved : HasTy Ctx.nil (subst(Exp.evar(Nat.zero))(Nat.zero)(Exp.enat(Nat.zero))) (synth(prog)(Ctx.nil)) := \
               preservation prog (subst(Exp.evar(Nat.zero))(Nat.zero)(Exp.enat(Nat.zero))) the_step \
                 Ctx.nil (synth(prog)(Ctx.nil)) (ok_sound(prog)(Ctx.nil)(Eq.refl.{1} Bool Bool.true))",
        )
        .expect("preservation should transport the typing across the β-step");
        assert!(s.k.env().contains("preserved"));
    }

    /// **Progress in action.** Applying `progress` to a concrete closed well-typed term
    /// (`(λx:tnat. x+1) 2`) yields a kernel-checked proof that it is a value or can step —
    /// i.e. it is not stuck. The certificate is just the typing derivation (`ok_sound … refl`).
    #[test]
    fn progress_applies_to_closed_program() {
        let mut s = safety_session().unwrap();
        s.run(
            "def p : Exp := \
               Exp.eapp(Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero)))), \
                        Exp.enat(Nat.succ(Nat.succ(Nat.zero))))",
        )
        .unwrap();
        s.run(
            "def p_not_stuck : Eq.{1} Bool (orB(isValue(p))(canStep(p))) Bool.true := \
               progress Ctx.nil p (synth(p)(Ctx.nil)) \
                 (ok_sound(p)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)) \
                 (Eq.refl.{1} Bool Bool.true)",
        )
        .expect("progress should certify the closed program is not stuck");
        assert!(s.k.env().contains("p_not_stuck"));
    }

    /// The **evaluator** elaborates and is kernel-checked.
    #[test]
    fn dynamics_check() {
        let s = runnable_session().expect("the evaluator should check");
        for n in ["isValue", "shift", "subst", "step", "run", "OExp"] {
            assert!(s.k.env().contains(n), "missing '{n}'");
        }
    }

    /// **Running code.** Typed programs reduce to values, computed by the kernel:
    ///   * `(λx:tnat. x + 1) 2  ⇒  3`           (β + the `eadd` primitive)
    ///   * `if true then 7 else 0  ⇒  7`        (branch selection)
    ///   * `let x = 4 in x + x  ⇒  8`           (a binder, a variable used twice)
    #[test]
    fn programs_run_to_values() {
        let mut s = runnable_session().unwrap();
        // (λx:tnat. x + 1) 2
        s.run(
            "def p1 : Exp := \
               Exp.eapp(Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero)))), \
                        Exp.enat(Nat.succ(Nat.succ(Nat.zero))))",
        )
        .unwrap();
        s.run("def r1 : Exp := run(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))(p1)").unwrap();
        // if true then 7 else 0
        s.run(
            "def p2 : Exp := Exp.eif(Exp.ebool(Bool.true), \
               Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))))), \
               Exp.enat(Nat.zero))",
        )
        .unwrap();
        s.run("def r2 : Exp := run(Nat.succ(Nat.succ(Nat.zero)))(p2)").unwrap();
        // let x = 4 in x + x
        s.run(
            "def p3 : Exp := Exp.elet(Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))), \
               Exp.eadd(Exp.evar(Nat.zero), Exp.evar(Nat.zero)))",
        )
        .unwrap();
        s.run("def r3 : Exp := run(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))(p3)").unwrap();
        assert_eq!(s.run_entry("r1").unwrap(), "Exp.enat 3", "(λx. x+1) 2 = 3");
        assert_eq!(s.run_entry("r2").unwrap(), "Exp.enat 7", "if true then 7 else 0 = 7");
        assert_eq!(s.run_entry("r3").unwrap(), "Exp.enat 8", "let x=4 in x+x = 8");
    }

    /// **Conditionals type-check.** `if true then 0 else 1` synthesizes `tnat`; a
    /// non-boolean condition (`if 0 then …`) and mismatched branches (`if true then 0 else
    /// true`) are both rejected.
    #[test]
    fn checker_handles_conditionals() {
        let mut s = session().unwrap();
        s.run(
            "def good : Exp := \
               Exp.eif(Exp.ebool(Bool.true), Exp.enat(Nat.zero), Exp.enat(Nat.succ(Nat.zero)))",
        )
        .unwrap();
        s.run("def good_ty : Ty := synth(good)(Ctx.nil)").unwrap();
        s.run("def good_ok : Bool := ok(good)(Ctx.nil)").unwrap();
        // condition isn't a bool
        s.run("def badcond : Bool := ok(Exp.eif(Exp.enat(Nat.zero), Exp.enat(Nat.zero), Exp.enat(Nat.zero)))(Ctx.nil)").unwrap();
        // branches disagree
        s.run("def badbranch : Bool := ok(Exp.eif(Exp.ebool(Bool.true), Exp.enat(Nat.zero), Exp.ebool(Bool.false)))(Ctx.nil)").unwrap();
        assert_eq!(s.run_entry("good_ty").unwrap(), "Ty.tnat");
        assert_eq!(s.run_entry("good_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("badcond").unwrap(), "Bool.false", "non-boolean condition");
        assert_eq!(s.run_entry("badbranch").unwrap(), "Bool.false", "branch types disagree");
    }

    /// **The checker DECIDES typability** (soundness + completeness). A rejected term is
    /// genuinely untypable: `ok_false_not_welltyped` turns `ok e = false` into a refutation
    /// `HasTy Γ e T → False`, for any context and type.
    #[test]
    fn rejected_term_is_genuinely_untypable() {
        let mut s = session().unwrap();
        // `0 true` — applying a non-function.
        s.run("def bad : Exp := Exp.eapp(Exp.enat(Nat.zero), Exp.ebool(Bool.true))").unwrap();
        s.run(
            "def bad_untypable (T : Ty) : HasTy Ctx.nil bad T -> False := \
               ok_false_not_welltyped Ctx.nil bad T (Eq.refl.{1} Bool Bool.false)",
        )
        .expect("a rejected term must be provably untypable");
        assert!(s.k.env().contains("bad_untypable"));
    }

    /// The checker handles `let` and variables: `let x = 0 in x + 1` synthesizes `tnat`.
    #[test]
    fn checker_accepts_let_with_variable() {
        let mut s = session().unwrap();
        s.run(
            "def prog : Exp := \
               Exp.elet(Exp.enat(Nat.zero), \
                        Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero))))",
        )
        .unwrap();
        s.run("def prog_ty : Ty := synth(prog)(Ctx.nil)").unwrap();
        s.run("def prog_ok : Bool := ok(prog)(Ctx.nil)").unwrap();
        assert_eq!(s.run_entry("prog_ty").unwrap(), "Ty.tnat");
        assert_eq!(s.run_entry("prog_ok").unwrap(), "Bool.true");
    }

    /// **λ-abstraction and application type-check.** `(λx:tnat. x + 1) 0` is well typed and
    /// synthesizes `tnat`; the lambda itself synthesizes the arrow `tnat → tnat`.
    #[test]
    fn checker_accepts_lambda_application() {
        let mut s = session().unwrap();
        // λ(x:tnat). x + 1
        s.run(
            "def idfun : Exp := \
               Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero))))",
        )
        .unwrap();
        s.run("def fun_ty : Ty := synth(idfun)(Ctx.nil)").unwrap();
        s.run("def applied : Exp := Exp.eapp(idfun, Exp.enat(Nat.zero))").unwrap();
        s.run("def applied_ty : Ty := synth(applied)(Ctx.nil)").unwrap();
        s.run("def applied_ok : Bool := ok(applied)(Ctx.nil)").unwrap();
        assert_eq!(s.run_entry("fun_ty").unwrap(), "Ty.tarrow Ty.tnat Ty.tnat");
        assert_eq!(s.run_entry("applied_ty").unwrap(), "Ty.tnat");
        assert_eq!(s.run_entry("applied_ok").unwrap(), "Bool.true");
    }

    /// **Application type errors are caught**: applying a non-function (`0 0`) and a
    /// domain mismatch (`(λx:tnat. x) true`) both make `ok` reduce to `false`.
    #[test]
    fn checker_rejects_application_errors() {
        let mut s = session().unwrap();
        // 0 applied to 0 — the "function" isn't an arrow.
        s.run("def notfun : Bool := ok(Exp.eapp(Exp.enat(Nat.zero), Exp.enat(Nat.zero)))(Ctx.nil)").unwrap();
        // (λx:tnat. x) true — argument type tbool ≠ domain tnat.
        s.run(
            "def mismatch : Bool := \
               ok(Exp.eapp(Exp.elam(Ty.tnat, Exp.evar(Nat.zero)), Exp.ebool(Bool.true)))(Ctx.nil)",
        )
        .unwrap();
        assert_eq!(s.run_entry("notfun").unwrap(), "Bool.false", "applying a non-function");
        assert_eq!(s.run_entry("mismatch").unwrap(), "Bool.false", "argument/domain type mismatch");
    }

    /// **Reflective typing of a higher-order term.** `(λx:tnat. x + 1) 0` is certified by
    /// running the checker: `ok_sound applied nil refl` produces the `HasTy` derivation
    /// (with its `tapp`/`tlam`/`tadd`/`tvar` steps) — a real proof, by computation.
    #[test]
    fn reflective_derivation_for_application() {
        let mut s = session().unwrap();
        s.run(
            "def applied : Exp := \
               Exp.eapp(Exp.elam(Ty.tnat, Exp.eadd(Exp.evar(Nat.zero), Exp.enat(Nat.succ(Nat.zero)))), \
                        Exp.enat(Nat.zero))",
        )
        .unwrap();
        s.run(
            "def derivation : HasTy Ctx.nil applied (synth(applied)(Ctx.nil)) := \
               ok_sound(applied)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)",
        )
        .expect("reflective derivation for an application should check");
        assert!(s.k.env().contains("derivation"));
    }

    /// **`fix`/recursion type-checks and runs (Tier 2).** A genuinely self-referential
    /// function — `fix self : nat→nat. λx:nat. if true then x+1 else self x` — type-checks
    /// (synthesizes `nat → nat`), and applied to `5` it *runs to 6*: the `fix` unrolls, the
    /// λ β-reduces, and the recursive call sits in the dead `else` branch (CBV picks `then`).
    #[test]
    fn fix_typechecks_and_runs() {
        let mut s = runnable_session().unwrap();
        // self is de Bruijn 1 inside the λ (efix binds 0, the λ pushes it to 1); x is 0.
        let rec = format!(
            "Exp.efix(Ty.tarrow(Ty.tnat, Ty.tnat), \
               Exp.elam(Ty.tnat, \
                 Exp.eif(Exp.ebool(Bool.true), \
                         Exp.eadd(Exp.evar({zero}), Exp.enat({one})), \
                         Exp.eapp(Exp.evar({one_idx}), Exp.evar({zero})))))",
            zero = nat(0),
            one = nat(1),
            one_idx = nat(1),
        );
        s.run(&format!("def rec : Exp := {rec}")).unwrap();
        s.run("def rec_ty : Ty := synth(rec)(Ctx.nil)").unwrap();
        s.run("def rec_ok : Bool := ok(rec)(Ctx.nil)").unwrap();
        s.run(&format!("def applied : Exp := Exp.eapp(rec, Exp.enat({}))", nat(5))).unwrap();
        s.run("def applied_ok : Bool := ok(applied)(Ctx.nil)").unwrap();
        s.run(&format!("def result : Exp := run({})(applied)", nat(10))).unwrap();
        assert_eq!(s.run_entry("rec_ty").unwrap(), "Ty.tarrow Ty.tnat Ty.tnat", "fix synthesizes nat→nat");
        assert_eq!(s.run_entry("rec_ok").unwrap(), "Bool.true", "the recursive function is well typed");
        assert_eq!(s.run_entry("applied_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("result").unwrap(), "Exp.enat 6", "(fix …) 5 = 6");
    }

    /// **Type safety extends to `fix`.** Progress: `fix nat. 7` is not stuck (it unrolls).
    /// Preservation: the `s_fix` unrolling step preserves the type — the unrolled body is
    /// still well typed at the same type. Both kernel-checked, with `efix` in the language.
    #[test]
    fn fix_is_type_safe() {
        let mut s = preservation_session().unwrap();
        // A trivial fixpoint whose body ignores the recursive binding: fix self:nat. 7.
        s.run(&format!("def f7 : Exp := Exp.efix(Ty.tnat, Exp.enat({}))", nat(7))).unwrap();
        // Progress: the closed fixpoint is a value or steps.
        s.run(
            "def f7_not_stuck : Eq.{1} Bool (orB(isValue(f7))(canStep(f7))) Bool.true := \
               progress Ctx.nil f7 (synth(f7)(Ctx.nil)) \
                 (ok_sound(f7)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)) (Eq.refl.{1} Bool Bool.true)",
        )
        .expect("progress should certify the fixpoint is not stuck");
        // Preservation: the unrolling step preserves typing.
        s.run(
            "def f7_step : Step f7 (subst(Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))) (Nat.zero) (f7)) := \
               Step.s_fix Ty.tnat (Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))))))",
        )
        .unwrap();
        s.run(
            "def f7_preserved : HasTy Ctx.nil (subst(Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))) (Nat.zero) (f7)) (synth(f7)(Ctx.nil)) := \
               preservation f7 (subst(Exp.enat(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))))))) (Nat.zero) (f7)) f7_step \
                 Ctx.nil (synth(f7)(Ctx.nil)) (ok_sound(f7)(Ctx.nil)(Eq.refl.{1} Bool Bool.true))",
        )
        .expect("preservation should transport typing across the fix-unroll step");
        assert!(s.k.env().contains("f7_not_stuck"));
        assert!(s.k.env().contains("f7_preserved"));
    }

    /// **Products (pairs) type-check and run (Tier 2).** `fst (1+2, true)` synthesizes `nat`
    /// and runs to `3`; `snd (1, false)` synthesizes `bool` and runs to `false`. The verified
    /// checker computes the component types; the evaluator projects (pairs are lazy values).
    #[test]
    fn products_typecheck_and_run() {
        let mut s = runnable_session().unwrap();
        // fst ((1+2), true)
        s.run(&format!(
            "def p1 : Exp := Exp.efst(Exp.epair(Exp.eadd(Exp.enat({}), Exp.enat({})), Exp.ebool(Bool.true)))",
            nat(1), nat(2)
        )).unwrap();
        s.run("def p1_ty : Ty := synth(p1)(Ctx.nil)").unwrap();
        s.run("def p1_ok : Bool := ok(p1)(Ctx.nil)").unwrap();
        s.run(&format!("def p1_val : Exp := run({})(p1)", nat(8))).unwrap();
        // snd (1, false)
        s.run(&format!(
            "def p2 : Exp := Exp.esnd(Exp.epair(Exp.enat({}), Exp.ebool(Bool.false)))",
            nat(1)
        )).unwrap();
        s.run("def p2_ty : Ty := synth(p2)(Ctx.nil)").unwrap();
        s.run(&format!("def p2_val : Exp := run({})(p2)", nat(4))).unwrap();
        assert_eq!(s.run_entry("p1_ty").unwrap(), "Ty.tnat", "fst of (nat, bool) is nat");
        assert_eq!(s.run_entry("p1_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("p1_val").unwrap(), "Exp.enat 3", "fst (1+2, true) = 3");
        assert_eq!(s.run_entry("p2_ty").unwrap(), "Ty.tbool", "snd of (nat, bool) is bool");
        assert_eq!(s.run_entry("p2_val").unwrap(), "Exp.ebool Bool.false", "snd (1, false) = false");
    }

    /// **Type safety extends to products.** Progress: `fst (5, 7)` is not stuck (it projects).
    /// Preservation: the `s_fst` projection step preserves the type (the projected component
    /// keeps the first-component type). Both kernel-checked with pairs in the language.
    #[test]
    fn products_type_safe() {
        let mut s = preservation_session().unwrap();
        s.run(&format!(
            "def fp : Exp := Exp.efst(Exp.epair(Exp.enat({}), Exp.enat({})))", nat(5), nat(7)
        )).unwrap();
        s.run(
            "def fp_not_stuck : Eq.{1} Bool (orB(isValue(fp))(canStep(fp))) Bool.true := \
               progress Ctx.nil fp (synth(fp)(Ctx.nil)) \
                 (ok_sound(fp)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)) (Eq.refl.{1} Bool Bool.true)",
        )
        .expect("progress should certify the projection is not stuck");
        s.run(&format!(
            "def fp_step : Step fp (Exp.enat({})) := Step.s_fst (Exp.enat({})) (Exp.enat({}))",
            nat(5), nat(5), nat(7)
        )).unwrap();
        s.run(&format!(
            "def fp_preserved : HasTy Ctx.nil (Exp.enat({})) (synth(fp)(Ctx.nil)) := \
               preservation fp (Exp.enat({})) fp_step Ctx.nil (synth(fp)(Ctx.nil)) \
                 (ok_sound(fp)(Ctx.nil)(Eq.refl.{{1}} Bool Bool.true))",
            nat(5), nat(5)
        ))
        .expect("preservation should transport typing across the fst-projection step");
        assert!(s.k.env().contains("fp_not_stuck"));
        assert!(s.k.env().contains("fp_preserved"));
    }

    /// **Sums (case analysis) type-check and run (Tier 2).** `case (inl 5) of x => x+1 | y => 0`
    /// synthesizes `nat` and runs to `6` (the `inl` branch fires, binding the payload); and
    /// `case (inr false) of x => 0 | y => if y then 1 else 2` runs to `2` (the `inr` branch
    /// fires). The verified checker derives each branch's payload type via `fstSum`/`sndSum`.
    #[test]
    fn sums_typecheck_and_run() {
        let mut s = runnable_session().unwrap();
        // case (inl[:tbool] 5) of x => x + 1 | y => 0
        s.run(&format!(
            "def c1 : Exp := Exp.ecase(Exp.einl(Ty.tbool, Exp.enat({})), \
               Exp.eadd(Exp.evar(Nat.zero), Exp.enat({})), Exp.enat(Nat.zero))",
            nat(5), nat(1)
        )).unwrap();
        s.run("def c1_ty : Ty := synth(c1)(Ctx.nil)").unwrap();
        s.run("def c1_ok : Bool := ok(c1)(Ctx.nil)").unwrap();
        s.run(&format!("def c1_val : Exp := run({})(c1)", nat(8))).unwrap();
        // case (inr[:tnat] false) of x => 0 | y => if y then 1 else 2
        s.run(&format!(
            "def c2 : Exp := Exp.ecase(Exp.einr(Ty.tnat, Exp.ebool(Bool.false)), \
               Exp.enat(Nat.zero), Exp.eif(Exp.evar(Nat.zero), Exp.enat({}), Exp.enat({})))",
            nat(1), nat(2)
        )).unwrap();
        s.run("def c2_ty : Ty := synth(c2)(Ctx.nil)").unwrap();
        s.run(&format!("def c2_val : Exp := run({})(c2)", nat(8))).unwrap();
        assert_eq!(s.run_entry("c1_ty").unwrap(), "Ty.tnat", "case on (nat+bool) sum is nat");
        assert_eq!(s.run_entry("c1_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("c1_val").unwrap(), "Exp.enat 6", "case (inl 5) x=>x+1 = 6");
        assert_eq!(s.run_entry("c2_ty").unwrap(), "Ty.tnat");
        assert_eq!(s.run_entry("c2_val").unwrap(), "Exp.enat 2", "case (inr false) y=>if y..=2");
    }

    /// **Type safety extends to sums.** Progress: `case (inl 5) of x => x | y => 0` is not stuck
    /// (the `inl` branch fires). Preservation: the `s_case_inl` β-step preserves the type — the
    /// reduct (the substituted left branch) keeps the case's result type. Both kernel-checked.
    #[test]
    fn sums_type_safe() {
        let mut s = preservation_session().unwrap();
        // case (inl[:tbool] 5) of x => x | y => 0   — left branch returns the payload.
        s.run(&format!(
            "def cs : Exp := Exp.ecase(Exp.einl(Ty.tbool, Exp.enat({})), \
               Exp.evar(Nat.zero), Exp.enat(Nat.zero))",
            nat(5)
        )).unwrap();
        s.run(
            "def cs_not_stuck : Eq.{1} Bool (orB(isValue(cs))(canStep(cs))) Bool.true := \
               progress Ctx.nil cs (synth(cs)(Ctx.nil)) \
                 (ok_sound(cs)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)) (Eq.refl.{1} Bool Bool.true)",
        )
        .expect("progress should certify the case is not stuck");
        s.run(&format!(
            "def cs_step : Step cs (Exp.enat({})) := \
               Step.s_case_inl Ty.tbool (Exp.enat({})) (Exp.evar Nat.zero) (Exp.enat Nat.zero)",
            nat(5), nat(5)
        )).unwrap();
        s.run(&format!(
            "def cs_preserved : HasTy Ctx.nil (Exp.enat({})) (synth(cs)(Ctx.nil)) := \
               preservation cs (Exp.enat({})) cs_step Ctx.nil (synth(cs)(Ctx.nil)) \
                 (ok_sound(cs)(Ctx.nil)(Eq.refl.{{1}} Bool Bool.true))",
            nat(5), nat(5)
        ))
        .expect("preservation should transport typing across the case-inl step");
        assert!(s.k.env().contains("cs_not_stuck"));
        assert!(s.k.env().contains("cs_preserved"));
    }

    /// **Soundness has teeth, with functions.** An application type error reduces `ok` to
    /// `false`, so no `refl` certificate exists and no derivation can be forged.
    #[test]
    fn ill_typed_application_cannot_be_certified() {
        let mut s = session().unwrap();
        s.run(
            "def bad : Exp := \
               Exp.eapp(Exp.elam(Ty.tnat, Exp.evar(Nat.zero)), Exp.ebool(Bool.true))",
        )
        .unwrap();
        let r = s.run(
            "def forged : HasTy Ctx.nil bad (synth(bad)(Ctx.nil)) := \
               ok_sound(bad)(Ctx.nil)(Eq.refl.{1} Bool Bool.true)",
        );
        assert!(r.is_err(), "an ill-typed application must not be certifiable");
    }
}
