//! **A verified type checker and evaluator for System F** (the polymorphic λ-calculus) —
//! the parametric-polymorphism tier, built as a *self-contained* development beside the
//! simply-typed [`crate::stlc`] so the two never disturb each other's proofs.
//!
//! The calculus is Church-style System F with explicit types and de Bruijn indices for
//! **both** namespaces (term variables and type variables):
//!
//!  * **Types** `FTy` — type variables, a base type `tnat`, the arrow, and `∀` (`tall`,
//!    whose body may mention `tvar 0`). Type substitution `tsubst`/`tshift` is the
//!    standard capture-avoiding de Bruijn machinery.
//!  * **Terms** `FExp` — variables, `nat` literals, λ (annotated), application, **type
//!    abstraction** `Λ` (`etlam`) and **type application** `e [T]` (`etapp`). Type
//!    application instantiates: `(Λ. e) [T] → e{T/0}`, substituting `T` into the type
//!    annotations inside `e` (`esubstTy`).
//!  * **Checker** — `fsynth : FExp → FCtx → FTy` and `fok : FExp → FCtx → Bool`, with a
//!    decidable `ftyeq`. Entering a `Λ` shifts the term context's types (`shiftCtx`),
//!    because a fresh type variable is introduced beneath them.
//!  * **Dynamics** — a call-by-value evaluator (`run`) over `step`, with λ and Λ as values.
//!
//! Checkpoint A (this layer) is purely computational — it type-checks and *runs*
//! polymorphic programs. The typing relation `FHasTy` and the soundness / type-safety
//! metatheory are layered on top in later sessions.

use crate::verify::Session;

/// Logic + booleans + naturals — the reusable proof core (shared shape with
/// [`crate::stlc::PRELUDE`], minus the STLC-specific object types).
pub const SF_PRELUDE: &str = r#"
    inductive True  : Prop | intro : True
    inductive False : Prop
    inductive Eq.{u} (A : Sort u) (a : A) : A -> Prop | refl : Eq A a a
    def Eq.subst.{u} (A : Sort u) (P : A -> Prop) (a : A) (b : A) (h : Eq A a b) (pa : P a)
      : P b := Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => P x) pa b h
    def Eq.symm.{u} (A : Sort u) (a : A) (b : A) (h : Eq A a b) : Eq A b a :=
      Eq.rec.{u, 0} A a (fun (x : A) (p : Eq A a x) => Eq A x a) (Eq.refl.{u} A a) b h
    def Eq.trans.{u} (A : Sort u) (a : A) (b : A) (c : A) (h1 : Eq A a b) (h2 : Eq A b c)
      : Eq A a c := Eq.subst.{u} A (fun (x : A) => Eq A a x) b c h2 h1

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

    inductive Nat : Type | zero : Nat | succ : Nat -> Nat
    fn pred(n: Nat) -> Nat { match n { | Nat.zero => Nat.zero | Nat.succ(m) => m } }
    fn eqNat(x: Nat) -> (Nat -> Bool) {
        match x {
          | Nat.zero    => fun (y : Nat) => match y { | Nat.zero => Bool.true  | Nat.succ(m) => Bool.false }
          | Nat.succ(x2) => fun (y : Nat) => match y { | Nat.zero => Bool.false | Nat.succ(y2) => eqNat(x2)(y2) }
        }
    }
    fn ltNat(x: Nat) -> (Nat -> Bool) {
        match x {
          | Nat.zero    => fun (y : Nat) => match y { | Nat.zero => Bool.false | Nat.succ(m) => Bool.true }
          | Nat.succ(x2) => fun (y : Nat) => match y { | Nat.zero => Bool.false | Nat.succ(y2) => ltNat(x2)(y2) }
        }
    }
"#;

/// System F types, the type-substitution machinery, terms, the checker, and the
/// decidable type equality.
pub const SF_LANG: &str = r#"
    -- ===== Types =====
    inductive FTy : Type
      | tvar   : Nat -> FTy            -- type variable (de Bruijn)
      | tnat   : FTy                   -- a base type, so we can run observable programs
      | tarrow : FTy -> FTy -> FTy
      | tall   : FTy -> FTy            -- forall. body  (body may use tvar 0)

    -- Type-variable shifting: lift every free `tvar >= c` by one (used when going under a
    -- new `tall` binder). Recurses on the type (first arg), cutoff curried second.
    fn tshift(t: FTy) -> (Nat -> FTy) {
        match t {
          | FTy.tvar(n)      => fun (c : Nat) => match ltNat(n)(c) { | Bool.true => FTy.tvar(n) | Bool.false => FTy.tvar(Nat.succ(n)) }
          | FTy.tnat         => fun (c : Nat) => FTy.tnat
          | FTy.tarrow(a, b) => fun (c : Nat) => FTy.tarrow(tshift(a)(c), tshift(b)(c))
          | FTy.tall(a)      => fun (c : Nat) => FTy.tall(tshift(a)(Nat.succ(c)))
        }
    }
    -- Type substitution `t{s/j}`: replace `tvar j` by `s`, dropping the binder (vars > j
    -- decrement), shifting `s` under each `tall` it descends into. Recurses on `t` first.
    fn tsubstVar(j: Nat, s: FTy, n: Nat) -> FTy {
        match eqNat(n)(j) {
          | Bool.true  => s
          | Bool.false => match ltNat(j)(n) { | Bool.true => FTy.tvar(pred(n)) | Bool.false => FTy.tvar(n) }
        }
    }
    fn tsubst(t: FTy) -> (Nat -> (FTy -> FTy)) {
        match t {
          | FTy.tvar(n)      => fun (j : Nat) => fun (s : FTy) => tsubstVar(j, s, n)
          | FTy.tnat         => fun (j : Nat) => fun (s : FTy) => FTy.tnat
          | FTy.tarrow(a, b) => fun (j : Nat) => fun (s : FTy) => FTy.tarrow(tsubst(a)(j)(s), tsubst(b)(j)(s))
          | FTy.tall(a)      => fun (j : Nat) => fun (s : FTy) => FTy.tall(tsubst(a)(Nat.succ(j))(tshift(s)(Nat.zero)))
        }
    }

    -- Type destructors (junk = tnat off the constructor) and the shape tests.
    fn isArrow(t: FTy) -> Bool {
        match t { | FTy.tvar(n) => Bool.false | FTy.tnat => Bool.false | FTy.tarrow(a, b) => Bool.true | FTy.tall(a) => Bool.false }
    }
    fn domOf(t: FTy) -> FTy {
        match t { | FTy.tvar(n) => FTy.tnat | FTy.tnat => FTy.tnat | FTy.tarrow(a, b) => a | FTy.tall(a) => FTy.tnat }
    }
    fn codOf(t: FTy) -> FTy {
        match t { | FTy.tvar(n) => FTy.tnat | FTy.tnat => FTy.tnat | FTy.tarrow(a, b) => b | FTy.tall(a) => FTy.tnat }
    }
    fn isAll(t: FTy) -> Bool {
        match t { | FTy.tvar(n) => Bool.false | FTy.tnat => Bool.false | FTy.tarrow(a, b) => Bool.false | FTy.tall(a) => Bool.true }
    }
    fn allBodyOf(t: FTy) -> FTy {
        match t { | FTy.tvar(n) => FTy.tnat | FTy.tnat => FTy.tnat | FTy.tarrow(a, b) => FTy.tnat | FTy.tall(a) => a }
    }

    -- Decidable type equality, structural (type variables compared by index).
    fn ftyeq(x: FTy) -> (FTy -> Bool) {
        match x {
          | FTy.tvar(xn) => fun (y : FTy) =>
              match y { | FTy.tvar(yn) => eqNat(xn)(yn) | FTy.tnat => Bool.false | FTy.tarrow(a, b) => Bool.false | FTy.tall(a) => Bool.false }
          | FTy.tnat => fun (y : FTy) =>
              match y { | FTy.tvar(yn) => Bool.false | FTy.tnat => Bool.true | FTy.tarrow(a, b) => Bool.false | FTy.tall(a) => Bool.false }
          | FTy.tarrow(xa, xb) => fun (y : FTy) =>
              match y { | FTy.tvar(yn) => Bool.false | FTy.tnat => Bool.false | FTy.tarrow(ya, yb) => and(ftyeq(xa)(ya), ftyeq(xb)(yb)) | FTy.tall(a) => Bool.false }
          | FTy.tall(xa) => fun (y : FTy) =>
              match y { | FTy.tvar(yn) => Bool.false | FTy.tnat => Bool.false | FTy.tarrow(a, b) => Bool.false | FTy.tall(ya) => ftyeq(xa)(ya) }
        }
    }

    -- ===== Terms =====
    inductive FExp : Type
      | evar  : Nat -> FExp
      | enat  : Nat -> FExp
      | elam  : FTy -> FExp -> FExp     -- λ (_ : A). body
      | eapp  : FExp -> FExp -> FExp
      | etlam : FExp -> FExp            -- Λ. body
      | etapp : FExp -> FTy -> FExp     -- e [T]

    -- ===== Typing context (term-variable types) + lookup/scope =====
    inductive FCtx : Type | nil : FCtx | cons : FTy -> FCtx -> FCtx
    fn flookup(G: FCtx) -> (Nat -> FTy) {
        match G {
          | FCtx.nil => fun (n : Nat) => FTy.tnat
          | FCtx.cons(t, rest) => fun (n : Nat) => match n { | Nat.zero => t | Nat.succ(m) => flookup(rest)(m) }
        }
    }
    fn finScope(G: FCtx) -> (Nat -> Bool) {
        match G {
          | FCtx.nil => fun (n : Nat) => Bool.false
          | FCtx.cons(t, rest) => fun (n : Nat) => match n { | Nat.zero => Bool.true | Nat.succ(m) => finScope(rest)(m) }
        }
    }
    -- Entering a `Λ` introduces a fresh type variable at index 0, so every type already in
    -- the term context must be shifted up.
    fn shiftCtx(G: FCtx) -> FCtx {
        match G { | FCtx.nil => FCtx.nil | FCtx.cons(t, rest) => FCtx.cons(tshift(t)(Nat.zero), shiftCtx(rest)) }
    }

    -- ===== Checker =====
    fn fsynth(e: FExp) -> (FCtx -> FTy) {
        match e {
          | FExp.evar(n)     => fun (G : FCtx) => flookup(G)(n)
          | FExp.enat(n)     => fun (G : FCtx) => FTy.tnat
          | FExp.elam(A, b)  => fun (G : FCtx) => FTy.tarrow(A, fsynth(b)(FCtx.cons(A, G)))
          | FExp.eapp(f, a)  => fun (G : FCtx) => codOf(fsynth(f)(G))
          | FExp.etlam(b)    => fun (G : FCtx) => FTy.tall(fsynth(b)(shiftCtx(G)))
          | FExp.etapp(f, T) => fun (G : FCtx) => tsubst(allBodyOf(fsynth(f)(G)))(Nat.zero)(T)
        }
    }
    fn fok(e: FExp) -> (FCtx -> Bool) {
        match e {
          | FExp.evar(n)     => fun (G : FCtx) => finScope(G)(n)
          | FExp.enat(n)     => fun (G : FCtx) => Bool.true
          | FExp.elam(A, b)  => fun (G : FCtx) => fok(b)(FCtx.cons(A, G))
          | FExp.eapp(f, a)  => fun (G : FCtx) =>
              and(and(fok(f)(G), fok(a)(G)),
                  and(isArrow(fsynth(f)(G)), ftyeq(domOf(fsynth(f)(G)))(fsynth(a)(G))))
          | FExp.etlam(b)    => fun (G : FCtx) => fok(b)(shiftCtx(G))
          | FExp.etapp(f, T) => fun (G : FCtx) => and(fok(f)(G), isAll(fsynth(f)(G)))
        }
    }
"#;

/// The call-by-value dynamics: capture-avoiding term/type substitution and a fuelled
/// evaluator. λ and Λ are values; `eapp` β-reduces, `etapp` does the type-β step.
pub const SF_DYNAMICS: &str = r#"
    fn isValue(e: FExp) -> Bool {
        match e {
          | FExp.evar(n)     => Bool.false
          | FExp.enat(n)     => Bool.true
          | FExp.elam(A, b)  => Bool.true
          | FExp.eapp(f, a)  => Bool.false
          | FExp.etlam(b)    => Bool.true
          | FExp.etapp(f, T) => Bool.false
        }
    }

    -- Shift term variables (>= c) up by one. Recurses on the term first.
    fn eshiftTm(e: FExp) -> (Nat -> FExp) {
        match e {
          | FExp.evar(n)     => fun (c : Nat) => match ltNat(n)(c) { | Bool.true => FExp.evar(n) | Bool.false => FExp.evar(Nat.succ(n)) }
          | FExp.enat(n)     => fun (c : Nat) => FExp.enat(n)
          | FExp.elam(A, b)  => fun (c : Nat) => FExp.elam(A, eshiftTm(b)(Nat.succ(c)))
          | FExp.eapp(f, a)  => fun (c : Nat) => FExp.eapp(eshiftTm(f)(c), eshiftTm(a)(c))
          | FExp.etlam(b)    => fun (c : Nat) => FExp.etlam(eshiftTm(b)(c))
          | FExp.etapp(f, T) => fun (c : Nat) => FExp.etapp(eshiftTm(f)(c), T)
        }
    }
    -- Shift type variables (>= c) inside a term's type annotations.
    fn eshiftTy(e: FExp) -> (Nat -> FExp) {
        match e {
          | FExp.evar(n)     => fun (c : Nat) => FExp.evar(n)
          | FExp.enat(n)     => fun (c : Nat) => FExp.enat(n)
          | FExp.elam(A, b)  => fun (c : Nat) => FExp.elam(tshift(A)(c), eshiftTy(b)(c))
          | FExp.eapp(f, a)  => fun (c : Nat) => FExp.eapp(eshiftTy(f)(c), eshiftTy(a)(c))
          | FExp.etlam(b)    => fun (c : Nat) => FExp.etlam(eshiftTy(b)(Nat.succ(c)))
          | FExp.etapp(f, T) => fun (c : Nat) => FExp.etapp(eshiftTy(f)(c), tshift(T)(c))
        }
    }
    -- Term substitution `e{v/j}`. Recurses on the term first; value + index curried.
    fn esubstVar(j: Nat, v: FExp, n: Nat) -> FExp {
        match eqNat(n)(j) {
          | Bool.true  => v
          | Bool.false => match ltNat(j)(n) { | Bool.true => FExp.evar(pred(n)) | Bool.false => FExp.evar(n) }
        }
    }
    fn esubstTm(e: FExp) -> (Nat -> (FExp -> FExp)) {
        match e {
          | FExp.evar(n)     => fun (j : Nat) => fun (v : FExp) => esubstVar(j, v, n)
          | FExp.enat(n)     => fun (j : Nat) => fun (v : FExp) => FExp.enat(n)
          | FExp.elam(A, b)  => fun (j : Nat) => fun (v : FExp) => FExp.elam(A, esubstTm(b)(Nat.succ(j))(eshiftTm(v)(Nat.zero)))
          | FExp.eapp(f, a)  => fun (j : Nat) => fun (v : FExp) => FExp.eapp(esubstTm(f)(j)(v), esubstTm(a)(j)(v))
          | FExp.etlam(b)    => fun (j : Nat) => fun (v : FExp) => FExp.etlam(esubstTm(b)(j)(eshiftTy(v)(Nat.zero)))
          | FExp.etapp(f, T) => fun (j : Nat) => fun (v : FExp) => FExp.etapp(esubstTm(f)(j)(v), T)
        }
    }
    -- Type substitution into a term's annotations `e{T/j}`.
    fn esubstTy(e: FExp) -> (Nat -> (FTy -> FExp)) {
        match e {
          | FExp.evar(n)     => fun (j : Nat) => fun (s : FTy) => FExp.evar(n)
          | FExp.enat(n)     => fun (j : Nat) => fun (s : FTy) => FExp.enat(n)
          | FExp.elam(A, b)  => fun (j : Nat) => fun (s : FTy) => FExp.elam(tsubst(A)(j)(s), esubstTy(b)(j)(s))
          | FExp.eapp(f, a)  => fun (j : Nat) => fun (s : FTy) => FExp.eapp(esubstTy(f)(j)(s), esubstTy(a)(j)(s))
          | FExp.etlam(b)    => fun (j : Nat) => fun (s : FTy) => FExp.etlam(esubstTy(b)(Nat.succ(j))(tshift(s)(Nat.zero)))
          | FExp.etapp(f, T) => fun (j : Nat) => fun (s : FTy) => FExp.etapp(esubstTy(f)(j)(s), tsubst(T)(j)(s))
        }
    }

    -- One CBV small step (a stuck term steps to itself).
    fn step(e: FExp) -> FExp {
        match e {
          | FExp.evar(n)     => FExp.evar(n)
          | FExp.enat(n)     => FExp.enat(n)
          | FExp.elam(A, b)  => FExp.elam(A, b)
          | FExp.etlam(b)    => FExp.etlam(b)
          | FExp.eapp(f, a)  => match isValue(f) {
              | Bool.false => FExp.eapp(step(f), a)
              | Bool.true  => match isValue(a) {
                  | Bool.false => FExp.eapp(f, step(a))
                  | Bool.true  => match f {
                      | FExp.elam(A, b)  => esubstTm(b)(Nat.zero)(a)
                      | FExp.evar(n)     => FExp.eapp(f, a)
                      | FExp.enat(n)     => FExp.eapp(f, a)
                      | FExp.eapp(g, h)  => FExp.eapp(f, a)
                      | FExp.etlam(b)    => FExp.eapp(f, a)
                      | FExp.etapp(g, T) => FExp.eapp(f, a)
                    }
                }
            }
          | FExp.etapp(f, T) => match isValue(f) {
              | Bool.false => FExp.etapp(step(f), T)
              | Bool.true  => match f {
                  | FExp.etlam(b)    => esubstTy(b)(Nat.zero)(T)
                  | FExp.evar(n)     => FExp.etapp(f, T)
                  | FExp.enat(n)     => FExp.etapp(f, T)
                  | FExp.elam(A, b)  => FExp.etapp(f, T)
                  | FExp.eapp(g, h)  => FExp.etapp(f, T)
                  | FExp.etapp(g, S) => FExp.etapp(f, T)
                }
            }
        }
    }
    -- Fuelled evaluation to a value.
    fn run(fuel: Nat) -> (FExp -> FExp) {
        match fuel {
          | Nat.zero     => fun (e : FExp) => e
          | Nat.succ(f2) => fun (e : FExp) =>
              match isValue(e) { | Bool.true => e | Bool.false => run(f2)(step(e)) }
        }
    }
"#;

/// **The typing relation `FHasTy` (the spec) and the soundness theorem.** `fok_sound`
/// proves the decidable checker implies a real typing derivation:
/// `fok e Γ = true → FHasTy Γ e (fsynth e Γ)`, by structural recursion on `e`. The `etlam`
/// case uses the shifted context; `etapp` inverts the synthesized type to a `∀` (`all_inv`)
/// and lands on `tsubst`; `eapp` inverts to an arrow and rewrites the domain (as in the STLC).
pub const SF_SAFETY: &str = r#"
    -- Generic congruences (subsume the per-constructor cong lemmas below).
    def congrArg.{u, v} (A : Sort u) (B : Sort v) (f : A -> B) (a : A) (b : A) (h : Eq.{u} A a b)
      : Eq.{v} B (f a) (f b) :=
      Eq.subst.{u} A (fun (x : A) => Eq.{v} B (f a) (f x)) a b h (Eq.refl.{v} B (f a))
    def congrArg2.{u, v, w} (A : Sort u) (B : Sort v) (C : Sort w) (f : A -> (B -> C))
        (a : A) (a2 : A) (b : B) (b2 : B) (ha : Eq.{u} A a a2) (hb : Eq.{v} B b b2)
      : Eq.{w} C (f a b) (f a2 b2) :=
      Eq.subst.{v} B (fun (y : B) => Eq.{w} C (f a b) (f a2 y)) b b2 hb
        (Eq.subst.{u} A (fun (x : A) => Eq.{w} C (f a b) (f x b)) a a2 ha (Eq.refl.{w} C (f a b)))

    -- Congruences, now derived from the generic ones (same signatures, all call sites unchanged).
    def succ_cong (m : Nat) (n : Nat) (h : Eq.{1} Nat m n) : Eq.{1} Nat (Nat.succ m) (Nat.succ n) :=
      congrArg.{1, 1} Nat Nat (fun (x : Nat) => Nat.succ x) m n h
    def tvar_cong (m : Nat) (n : Nat) (h : Eq.{1} Nat m n) : Eq.{1} FTy (FTy.tvar m) (FTy.tvar n) :=
      congrArg.{1, 1} Nat FTy (fun (x : Nat) => FTy.tvar x) m n h
    def tarrow_cong (xa : FTy) (ya : FTy) (xb : FTy) (yb : FTy)
        (ea : Eq.{1} FTy xa ya) (eb : Eq.{1} FTy xb yb)
        : Eq.{1} FTy (FTy.tarrow xa xb) (FTy.tarrow ya yb) :=
      congrArg2.{1, 1, 1} FTy FTy FTy (fun (m : FTy) => fun (n : FTy) => FTy.tarrow m n) xa ya xb yb ea eb
    def tall_cong (xa : FTy) (ya : FTy) (e : Eq.{1} FTy xa ya)
        : Eq.{1} FTy (FTy.tall xa) (FTy.tall ya) :=
      congrArg.{1, 1} FTy FTy (fun (x : FTy) => FTy.tall x) xa ya e

    -- Nat equality reflection.
    fn eqNat_sound(x: Nat) -> ((y : Nat) -> Eq.{1} Bool (eqNat(x)(y)) Bool.true -> Eq.{1} Nat x y) {
        match x {
          | Nat.zero => fun (y : Nat) =>
              match y {
                | Nat.zero    => fun (h : Eq.{1} Bool (eqNat(Nat.zero)(Nat.zero)) Bool.true) => Eq.refl.{1} Nat Nat.zero
                | Nat.succ(m) => fun (h : Eq.{1} Bool (eqNat(Nat.zero)(Nat.succ(m))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Nat Nat.zero (Nat.succ m)) (ff_ne_tt h)
              }
          | Nat.succ(x2) => fun (y : Nat) =>
              match y {
                | Nat.zero    => fun (h : Eq.{1} Bool (eqNat(Nat.succ(x2))(Nat.zero)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Nat (Nat.succ x2) Nat.zero) (ff_ne_tt h)
                | Nat.succ(y2) => fun (h : Eq.{1} Bool (eqNat(Nat.succ(x2))(Nat.succ(y2))) Bool.true) =>
                    succ_cong x2 y2 (eqNat_sound(x2)(y2)(h))
              }
        }
    }

    -- Decidable type equality is sound: ftyeq x y = true → x = y.
    fn ftyeq_sound(x: FTy) -> ((y : FTy) -> Eq.{1} Bool (ftyeq(x)(y)) Bool.true -> Eq.{1} FTy x y) {
        match x {
          | FTy.tvar(xn) => fun (y : FTy) =>
              match y {
                | FTy.tvar(yn)     => fun (h : Eq.{1} Bool (ftyeq(FTy.tvar(xn))(FTy.tvar(yn))) Bool.true) =>
                    tvar_cong xn yn (eqNat_sound(xn)(yn)(h))
                | FTy.tnat         => fun (h : Eq.{1} Bool (ftyeq(FTy.tvar(xn))(FTy.tnat)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tvar xn) FTy.tnat) (ff_ne_tt h)
                | FTy.tarrow(a, b) => fun (h : Eq.{1} Bool (ftyeq(FTy.tvar(xn))(FTy.tarrow(a, b))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tvar xn) (FTy.tarrow a b)) (ff_ne_tt h)
                | FTy.tall(a)      => fun (h : Eq.{1} Bool (ftyeq(FTy.tvar(xn))(FTy.tall(a))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tvar xn) (FTy.tall a)) (ff_ne_tt h)
              }
          | FTy.tnat => fun (y : FTy) =>
              match y {
                | FTy.tvar(yn)     => fun (h : Eq.{1} Bool (ftyeq(FTy.tnat)(FTy.tvar(yn))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy FTy.tnat (FTy.tvar yn)) (ff_ne_tt h)
                | FTy.tnat         => fun (h : Eq.{1} Bool (ftyeq(FTy.tnat)(FTy.tnat)) Bool.true) => Eq.refl.{1} FTy FTy.tnat
                | FTy.tarrow(a, b) => fun (h : Eq.{1} Bool (ftyeq(FTy.tnat)(FTy.tarrow(a, b))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy FTy.tnat (FTy.tarrow a b)) (ff_ne_tt h)
                | FTy.tall(a)      => fun (h : Eq.{1} Bool (ftyeq(FTy.tnat)(FTy.tall(a))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy FTy.tnat (FTy.tall a)) (ff_ne_tt h)
              }
          | FTy.tarrow(xa, xb) => fun (y : FTy) =>
              match y {
                | FTy.tvar(yn)     => fun (h : Eq.{1} Bool (ftyeq(FTy.tarrow(xa, xb))(FTy.tvar(yn))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tarrow xa xb) (FTy.tvar yn)) (ff_ne_tt h)
                | FTy.tnat         => fun (h : Eq.{1} Bool (ftyeq(FTy.tarrow(xa, xb))(FTy.tnat)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tarrow xa xb) FTy.tnat) (ff_ne_tt h)
                | FTy.tarrow(ya, yb) => fun (h : Eq.{1} Bool (ftyeq(FTy.tarrow(xa, xb))(FTy.tarrow(ya, yb))) Bool.true) =>
                    tarrow_cong xa ya xb yb
                      (ftyeq_sound(xa)(ya) (and_left (ftyeq(xa)(ya)) (ftyeq(xb)(yb)) h))
                      (ftyeq_sound(xb)(yb) (and_right (ftyeq(xa)(ya)) (ftyeq(xb)(yb)) h))
                | FTy.tall(a)      => fun (h : Eq.{1} Bool (ftyeq(FTy.tarrow(xa, xb))(FTy.tall(a))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tarrow xa xb) (FTy.tall a)) (ff_ne_tt h)
              }
          | FTy.tall(xa) => fun (y : FTy) =>
              match y {
                | FTy.tvar(yn)     => fun (h : Eq.{1} Bool (ftyeq(FTy.tall(xa))(FTy.tvar(yn))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tall xa) (FTy.tvar yn)) (ff_ne_tt h)
                | FTy.tnat         => fun (h : Eq.{1} Bool (ftyeq(FTy.tall(xa))(FTy.tnat)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tall xa) FTy.tnat) (ff_ne_tt h)
                | FTy.tarrow(a, b) => fun (h : Eq.{1} Bool (ftyeq(FTy.tall(xa))(FTy.tarrow(a, b))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tall xa) (FTy.tarrow a b)) (ff_ne_tt h)
                | FTy.tall(ya)     => fun (h : Eq.{1} Bool (ftyeq(FTy.tall(xa))(FTy.tall(ya))) Bool.true) =>
                    tall_cong xa ya (ftyeq_sound(xa)(ya)(h))
              }
        }
    }

    -- Shape inversions (junk-armed no-confusion).
    fn arrow_inv(t: FTy) -> (Eq.{1} Bool (isArrow(t)) Bool.true -> Eq.{1} FTy t (FTy.tarrow (domOf(t)) (codOf(t)))) {
        match t {
          | FTy.tvar(n)      => fun (h : Eq.{1} Bool (isArrow(FTy.tvar(n))) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tvar n) (FTy.tarrow (domOf(FTy.tvar(n))) (codOf(FTy.tvar(n))))) (ff_ne_tt h)
          | FTy.tnat         => fun (h : Eq.{1} Bool (isArrow(FTy.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} FTy FTy.tnat (FTy.tarrow (domOf(FTy.tnat)) (codOf(FTy.tnat)))) (ff_ne_tt h)
          | FTy.tarrow(a, b) => fun (h : Eq.{1} Bool (isArrow(FTy.tarrow(a, b))) Bool.true) =>
              Eq.refl.{1} FTy (FTy.tarrow a b)
          | FTy.tall(a)      => fun (h : Eq.{1} Bool (isArrow(FTy.tall(a))) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tall a) (FTy.tarrow (domOf(FTy.tall(a))) (codOf(FTy.tall(a))))) (ff_ne_tt h)
        }
    }
    fn all_inv(t: FTy) -> (Eq.{1} Bool (isAll(t)) Bool.true -> Eq.{1} FTy t (FTy.tall (allBodyOf(t)))) {
        match t {
          | FTy.tvar(n)      => fun (h : Eq.{1} Bool (isAll(FTy.tvar(n))) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tvar n) (FTy.tall (allBodyOf(FTy.tvar(n))))) (ff_ne_tt h)
          | FTy.tnat         => fun (h : Eq.{1} Bool (isAll(FTy.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} FTy FTy.tnat (FTy.tall (allBodyOf(FTy.tnat)))) (ff_ne_tt h)
          | FTy.tarrow(a, b) => fun (h : Eq.{1} Bool (isAll(FTy.tarrow(a, b))) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} FTy (FTy.tarrow a b) (FTy.tall (allBodyOf(FTy.tarrow(a, b))))) (ff_ne_tt h)
          | FTy.tall(a)      => fun (h : Eq.{1} Bool (isAll(FTy.tall(a))) Bool.true) =>
              Eq.refl.{1} FTy (FTy.tall a)
        }
    }

    -- The de Bruijn lookup relation + its reflection from the boolean scope test.
    inductive FLookup : FCtx -> Nat -> FTy -> Prop
      | here  : (G : FCtx) -> (T : FTy) -> FLookup (FCtx.cons T G) Nat.zero T
      | there : (G : FCtx) -> (n : Nat) -> (T : FTy) -> (U : FTy)
                  -> FLookup G n T -> FLookup (FCtx.cons U G) (Nat.succ n) T
    fn flookup_sound(G: FCtx) -> ((n : Nat) -> Eq.{1} Bool (finScope(G)(n)) Bool.true -> FLookup G n (flookup(G)(n))) {
        match G {
          | FCtx.nil => fun (n : Nat) (h : Eq.{1} Bool (finScope(FCtx.nil)(n)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => FLookup FCtx.nil n (flookup(FCtx.nil)(n))) (ff_ne_tt h)
          | FCtx.cons(t, rest) => fun (n : Nat) =>
              match n {
                | Nat.zero    => fun (h : Eq.{1} Bool (finScope(FCtx.cons(t, rest))(Nat.zero)) Bool.true) =>
                    FLookup.here rest t
                | Nat.succ(m) => fun (h : Eq.{1} Bool (finScope(FCtx.cons(t, rest))(Nat.succ(m))) Bool.true) =>
                    FLookup.there rest m (flookup(rest)(m)) t (flookup_sound(rest)(m)(h))
              }
        }
    }

    -- The typing relation (the spec).
    inductive FHasTy : FCtx -> FExp -> FTy -> Prop
      | ftvar  : (G : FCtx) -> (n : Nat) -> (T : FTy) -> FLookup G n T -> FHasTy G (FExp.evar n) T
      | ftnat  : (G : FCtx) -> (n : Nat) -> FHasTy G (FExp.enat n) FTy.tnat
      | ftlam  : (G : FCtx) -> (A : FTy) -> (b : FExp) -> (B : FTy)
                   -> FHasTy (FCtx.cons A G) b B -> FHasTy G (FExp.elam A b) (FTy.tarrow A B)
      | ftapp  : (G : FCtx) -> (f : FExp) -> (a : FExp) -> (A : FTy) -> (B : FTy)
                   -> FHasTy G f (FTy.tarrow A B) -> FHasTy G a A -> FHasTy G (FExp.eapp f a) B
      | fttlam : (G : FCtx) -> (b : FExp) -> (B : FTy)
                   -> FHasTy (shiftCtx G) b B -> FHasTy G (FExp.etlam b) (FTy.tall B)
      | fttapp : (G : FCtx) -> (f : FExp) -> (B : FTy) -> (T : FTy)
                   -> FHasTy G f (FTy.tall B) -> FHasTy G (FExp.etapp f T) (tsubst B Nat.zero T)

    -- SOUNDNESS: ok e Γ = true → HasTy Γ e (synth e Γ).
    fn fok_sound(e: FExp)
      -> ((G : FCtx) -> Eq.{1} Bool (fok(e)(G)) Bool.true -> FHasTy G e (fsynth(e)(G))) {
        match e {
          | FExp.evar(n) => fun (G : FCtx) (h : Eq.{1} Bool (fok(FExp.evar(n))(G)) Bool.true) =>
              FHasTy.ftvar G n (flookup(G)(n)) (flookup_sound(G)(n)(h))
          | FExp.enat(n) => fun (G : FCtx) (h : Eq.{1} Bool (fok(FExp.enat(n))(G)) Bool.true) =>
              FHasTy.ftnat G n
          | FExp.elam(A, b) => fun (G : FCtx) (h : Eq.{1} Bool (fok(FExp.elam(A, b))(G)) Bool.true) =>
              FHasTy.ftlam G A b (fsynth(b)(FCtx.cons(A, G))) (fok_sound(b)(FCtx.cons(A, G)) h)
          | FExp.eapp(f, a) => fun (G : FCtx) (h : Eq.{1} Bool (fok(FExp.eapp(f, a))(G)) Bool.true) =>
              FHasTy.ftapp G f a (fsynth(a)(G)) (codOf(fsynth(f)(G)))
                (Eq.subst.{1} FTy
                   (fun (d : FTy) => FHasTy G f (FTy.tarrow d (codOf(fsynth(f)(G)))))
                   (domOf(fsynth(f)(G))) (fsynth(a)(G))
                   (ftyeq_sound(domOf(fsynth(f)(G)))(fsynth(a)(G))
                      (and_right (isArrow(fsynth(f)(G))) (ftyeq(domOf(fsynth(f)(G)))(fsynth(a)(G)))
                         (and_right (and(fok(f)(G), fok(a)(G)))
                                    (and(isArrow(fsynth(f)(G)), ftyeq(domOf(fsynth(f)(G)))(fsynth(a)(G)))) h)))
                   (Eq.subst.{1} FTy (fun (t : FTy) => FHasTy G f t)
                      (fsynth(f)(G)) (FTy.tarrow (domOf(fsynth(f)(G))) (codOf(fsynth(f)(G))))
                      (arrow_inv(fsynth(f)(G))
                         (and_left (isArrow(fsynth(f)(G))) (ftyeq(domOf(fsynth(f)(G)))(fsynth(a)(G)))
                            (and_right (and(fok(f)(G), fok(a)(G)))
                                       (and(isArrow(fsynth(f)(G)), ftyeq(domOf(fsynth(f)(G)))(fsynth(a)(G)))) h)))
                      (fok_sound(f)(G)
                         (and_left (fok(f)(G)) (fok(a)(G))
                            (and_left (and(fok(f)(G), fok(a)(G)))
                                      (and(isArrow(fsynth(f)(G)), ftyeq(domOf(fsynth(f)(G)))(fsynth(a)(G)))) h)))))
                (fok_sound(a)(G)
                   (and_right (fok(f)(G)) (fok(a)(G))
                      (and_left (and(fok(f)(G), fok(a)(G)))
                                (and(isArrow(fsynth(f)(G)), ftyeq(domOf(fsynth(f)(G)))(fsynth(a)(G)))) h)))
          | FExp.etlam(b) => fun (G : FCtx) (h : Eq.{1} Bool (fok(FExp.etlam(b))(G)) Bool.true) =>
              FHasTy.fttlam G b (fsynth(b)(shiftCtx(G))) (fok_sound(b)(shiftCtx(G)) h)
          | FExp.etapp(f, T) => fun (G : FCtx) (h : Eq.{1} Bool (fok(FExp.etapp(f, T))(G)) Bool.true) =>
              FHasTy.fttapp G f (allBodyOf(fsynth(f)(G))) T
                (Eq.subst.{1} FTy (fun (t : FTy) => FHasTy G f t)
                   (fsynth(f)(G)) (FTy.tall (allBodyOf(fsynth(f)(G))))
                   (all_inv(fsynth(f)(G))
                      (and_right (fok(f)(G)) (isAll(fsynth(f)(G))) h))
                   (fok_sound(f)(G)
                      (and_left (fok(f)(G)) (isAll(fsynth(f)(G))) h)))
        }
    }
"#;

/// **Progress.** A well-typed *closed* term is a value or can step: `FHasTy nil e T →
/// isValue e ∨ canStep e`. Built from canonical-forms lemmas (`canon_arrow`/`canon_all`,
/// a value's shape is dictated by its type) and a structural reducibility predicate
/// `canStep`. Proved by recursion on the typing derivation.
pub const SF_PROGRESS: &str = r#"
    inductive Or (a : Prop) (b : Prop) : Prop | inl : a -> Or a b | inr : b -> Or a b
    fn orB(x: Bool) -> (Bool -> Bool) {
        match x { | Bool.true => fun (y : Bool) => Bool.true | Bool.false => fun (y : Bool) => y }
    }
    def orB_false_left (x : Bool) (y : Bool)
        : Eq.{1} Bool (orB(x)(y)) Bool.true -> Eq.{1} Bool x Bool.false -> Eq.{1} Bool y Bool.true :=
      match x {
        | Bool.true  => fun (h : Eq.{1} Bool (orB(Bool.true)(y)) Bool.true) (hxf : Eq.{1} Bool Bool.true Bool.false) =>
            False.rec.{0} (fun (_ : False) => Eq.{1} Bool y Bool.true) (ff_ne_tt (Eq.symm.{1} Bool Bool.true Bool.false hxf))
        | Bool.false => fun (h : Eq.{1} Bool (orB(Bool.false)(y)) Bool.true) (hxf : Eq.{1} Bool Bool.false Bool.false) => h
      }
    def orB_true_left (x : Bool) (y : Bool) (hx : Eq.{1} Bool x Bool.true) : Eq.{1} Bool (orB(x)(y)) Bool.true :=
      Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} Bool (orB(b)(y)) Bool.true) Bool.true x
        (Eq.symm.{1} Bool x Bool.true hx) (Eq.refl.{1} Bool Bool.true)
    def orB_true_right (x : Bool) (y : Bool) (hy : Eq.{1} Bool y Bool.true) : Eq.{1} Bool (orB(x)(y)) Bool.true :=
      match x { | Bool.true => Eq.refl.{1} Bool Bool.true | Bool.false => hy }
    def bool_cases (b : Bool) : Or (Eq.{1} Bool b Bool.true) (Eq.{1} Bool b Bool.false) :=
      match b {
        | Bool.true  => Or.inl (Eq.{1} Bool Bool.true Bool.true) (Eq.{1} Bool Bool.true Bool.false) (Eq.refl.{1} Bool Bool.true)
        | Bool.false => Or.inr (Eq.{1} Bool Bool.false Bool.true) (Eq.{1} Bool Bool.false Bool.false) (Eq.refl.{1} Bool Bool.false)
      }

    fn isNil(G: FCtx) -> Bool { match G { | FCtx.nil => Bool.true | FCtx.cons(t, rest) => Bool.false } }
    fn isLam(e: FExp) -> Bool {
        match e { | FExp.evar(n) => Bool.false | FExp.enat(n) => Bool.false | FExp.elam(A, b) => Bool.true | FExp.eapp(f, a) => Bool.false | FExp.etlam(b) => Bool.false | FExp.etapp(f, T) => Bool.false }
    }
    fn isTlam(e: FExp) -> Bool {
        match e { | FExp.evar(n) => Bool.false | FExp.enat(n) => Bool.false | FExp.elam(A, b) => Bool.false | FExp.eapp(f, a) => Bool.false | FExp.etlam(b) => Bool.true | FExp.etapp(f, T) => Bool.false }
    }

    -- A flat structural reducibility predicate: `eapp f a` reduces when `f` does, or `f` is
    -- a value and `a` reduces, or both are values and `f` is a λ; `etapp f T` similarly.
    fn canStep(e: FExp) -> Bool {
        match e {
          | FExp.evar(n)     => Bool.false
          | FExp.enat(n)     => Bool.false
          | FExp.elam(A, b)  => Bool.false
          | FExp.etlam(b)    => Bool.false
          | FExp.eapp(f, a)  =>
              orB(canStep(f))(orB(and(isValue(f), canStep(a)))(and(isValue(f), and(isValue(a), isLam(f)))))
          | FExp.etapp(f, T) =>
              orB(canStep(f))(and(isValue(f), isTlam(f)))
        }
    }

    -- Canonical forms: a value whose type is an arrow is a λ; whose type is a ∀ is a Λ.
    fn canon_arrow(G: FCtx, e: FExp, ty: FTy, d: FHasTy G e ty)
      -> (Eq.{1} Bool (isValue(e)) Bool.true -> Eq.{1} Bool (isArrow(ty)) Bool.true -> Eq.{1} Bool (isLam(e)) Bool.true) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (h1 : Eq.{1} Bool (isValue(FExp.evar(n2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(FExp.evar(n2))) Bool.true) (ff_ne_tt h1)
          | FHasTy.ftnat(G2, n2) => fun (h1 : Eq.{1} Bool (isValue(FExp.enat(n2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(FTy.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(FExp.enat(n2))) Bool.true) (ff_ne_tt h2)
          | FHasTy.ftlam(G2, A2, body2, B2, dbody) => fun (h1 : Eq.{1} Bool (isValue(FExp.elam(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(FTy.tarrow A2 B2)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (h1 : Eq.{1} Bool (isValue(FExp.eapp(f2, a2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(FExp.eapp(f2, a2))) Bool.true) (ff_ne_tt h1)
          | FHasTy.fttlam(G2, body2, B2, dbody) => fun (h1 : Eq.{1} Bool (isValue(FExp.etlam(body2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(FTy.tall B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(FExp.etlam(body2))) Bool.true) (ff_ne_tt h2)
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (h1 : Eq.{1} Bool (isValue(FExp.etapp(f2, T2))) Bool.true) (h2 : Eq.{1} Bool (isArrow(tsubst B2 Nat.zero T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isLam(FExp.etapp(f2, T2))) Bool.true) (ff_ne_tt h1)
        }
    }
    fn canon_all(G: FCtx, e: FExp, ty: FTy, d: FHasTy G e ty)
      -> (Eq.{1} Bool (isValue(e)) Bool.true -> Eq.{1} Bool (isAll(ty)) Bool.true -> Eq.{1} Bool (isTlam(e)) Bool.true) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (h1 : Eq.{1} Bool (isValue(FExp.evar(n2))) Bool.true) (h2 : Eq.{1} Bool (isAll(T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isTlam(FExp.evar(n2))) Bool.true) (ff_ne_tt h1)
          | FHasTy.ftnat(G2, n2) => fun (h1 : Eq.{1} Bool (isValue(FExp.enat(n2))) Bool.true) (h2 : Eq.{1} Bool (isAll(FTy.tnat)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isTlam(FExp.enat(n2))) Bool.true) (ff_ne_tt h2)
          | FHasTy.ftlam(G2, A2, body2, B2, dbody) => fun (h1 : Eq.{1} Bool (isValue(FExp.elam(A2, body2))) Bool.true) (h2 : Eq.{1} Bool (isAll(FTy.tarrow A2 B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isTlam(FExp.elam(A2, body2))) Bool.true) (ff_ne_tt h2)
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (h1 : Eq.{1} Bool (isValue(FExp.eapp(f2, a2))) Bool.true) (h2 : Eq.{1} Bool (isAll(B2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isTlam(FExp.eapp(f2, a2))) Bool.true) (ff_ne_tt h1)
          | FHasTy.fttlam(G2, body2, B2, dbody) => fun (h1 : Eq.{1} Bool (isValue(FExp.etlam(body2))) Bool.true) (h2 : Eq.{1} Bool (isAll(FTy.tall B2)) Bool.true) =>
              Eq.refl.{1} Bool Bool.true
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (h1 : Eq.{1} Bool (isValue(FExp.etapp(f2, T2))) Bool.true) (h2 : Eq.{1} Bool (isAll(tsubst B2 Nat.zero T2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (isTlam(FExp.etapp(f2, T2))) Bool.true) (ff_ne_tt h1)
        }
    }

    -- A lookup in the empty context is impossible.
    fn flookup_nil_false(G: FCtx, n: Nat, T: FTy, d: FLookup G n T)
      -> (Eq.{1} Bool (isNil(G)) Bool.true -> False) {
        match d {
          | FLookup.here(G2, T2) => fun (h : Eq.{1} Bool (isNil(FCtx.cons(T2, G2))) Bool.true) =>
              ff_ne_tt h
          | FLookup.there(G2, n2, T2, U2, lk2) => fun (h : Eq.{1} Bool (isNil(FCtx.cons(U2, G2))) Bool.true) =>
              ff_ne_tt h
        }
    }

    -- PROGRESS.
    fn progress(G: FCtx, e: FExp, T: FTy, d: FHasTy G e T)
      -> (Eq.{1} Bool (isNil(G)) Bool.true -> Eq.{1} Bool (orB(isValue(e))(canStep(e))) Bool.true) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (orB(isValue(FExp.evar(n2)))(canStep(FExp.evar(n2)))) Bool.true) (flookup_nil_false G2 n2 T2 lk2 hnil)
          | FHasTy.ftnat(G2, n2) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) => Eq.refl.{1} Bool Bool.true
          | FHasTy.ftlam(G2, A2, body2, B2, dbody) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) => Eq.refl.{1} Bool Bool.true
          | FHasTy.fttlam(G2, body2, B2, dbody) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) => Eq.refl.{1} Bool Bool.true
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              match bool_cases(isValue(f2)) {
                | Or.inr(evf) =>
                    orB_true_left (canStep(f2)) (orB(and(isValue(f2), canStep(a2)))(and(isValue(f2), and(isValue(a2), isLam(f2)))))
                      (orB_false_left (isValue(f2)) (canStep(f2)) (df.rec hnil) evf)
                | Or.inl(evf) =>
                    match bool_cases(isValue(a2)) {
                      | Or.inr(eva) =>
                          orB_true_right (canStep(f2)) (orB(and(isValue(f2), canStep(a2)))(and(isValue(f2), and(isValue(a2), isLam(f2)))))
                            (orB_true_left (and(isValue(f2), canStep(a2))) (and(isValue(f2), and(isValue(a2), isLam(f2))))
                               (and_true (isValue(f2)) (canStep(a2)) evf
                                  (orB_false_left (isValue(a2)) (canStep(a2)) (da.rec hnil) eva)))
                      | Or.inl(eva) =>
                          orB_true_right (canStep(f2)) (orB(and(isValue(f2), canStep(a2)))(and(isValue(f2), and(isValue(a2), isLam(f2)))))
                            (orB_true_right (and(isValue(f2), canStep(a2))) (and(isValue(f2), and(isValue(a2), isLam(f2))))
                               (and_true (isValue(f2)) (and(isValue(a2), isLam(f2))) evf
                                  (and_true (isValue(a2)) (isLam(f2)) eva
                                     (canon_arrow G2 f2 (FTy.tarrow A2 B2) df evf (Eq.refl.{1} Bool Bool.true)))))
                    }
              }
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (hnil : Eq.{1} Bool (isNil(G2)) Bool.true) =>
              match bool_cases(isValue(f2)) {
                | Or.inr(evf) =>
                    orB_true_left (canStep(f2)) (and(isValue(f2), isTlam(f2)))
                      (orB_false_left (isValue(f2)) (canStep(f2)) (df.rec hnil) evf)
                | Or.inl(evf) =>
                    orB_true_right (canStep(f2)) (and(isValue(f2), isTlam(f2)))
                      (and_true (isValue(f2)) (isTlam(f2)) evf
                         (canon_all G2 f2 (FTy.tall B2) df evf (Eq.refl.{1} Bool Bool.true)))
              }
        }
    }
"#;

/// **Step relation + inversion scaffolding** for preservation. The small-step relation
/// `Step` mirrors the executable `step`; the no-confusion principle (`exp_noconf` via a
/// constructor tag) and the projection/injectivity helpers let the preservation proof
/// invert a typing derivation whose subject is a concrete constructor application.
pub const SF_STEP: &str = r#"
    -- Nat equality reflexivity (eqNat n n = true) for the tag no-confusion.
    fn eqNat_refl(n: Nat) -> Eq.{1} Bool (eqNat(n)(n)) Bool.true {
        match n { | Nat.zero => Eq.refl.{1} Bool Bool.true | Nat.succ(k) => k.rec }
    }
    -- A constructor tag + reflexivity give a generic no-confusion: distinct heads are unequal.
    fn expTag(e: FExp) -> Nat {
        match e {
          | FExp.evar(n)     => Nat.zero
          | FExp.enat(n)     => Nat.succ(Nat.zero)
          | FExp.elam(A, b)  => Nat.succ(Nat.succ(Nat.zero))
          | FExp.eapp(f, a)  => Nat.succ(Nat.succ(Nat.succ(Nat.zero)))
          | FExp.etlam(b)    => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero))))
          | FExp.etapp(f, T) => Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.succ(Nat.zero)))))
        }
    }
    def exp_noconf (e1 : FExp) (e2 : FExp)
        (htag : Eq.{1} Bool (eqNat(expTag(e1))(expTag(e2))) Bool.false)
        (heq : Eq.{1} FExp e1 e2) : False :=
      ff_ne_tt (Eq.trans.{1} Bool Bool.false (eqNat(expTag(e1))(expTag(e2))) Bool.true
                  (Eq.symm.{1} Bool (eqNat(expTag(e1))(expTag(e2))) Bool.false htag)
                  (Eq.subst.{1} Nat (fun (t : Nat) => Eq.{1} Bool (eqNat(expTag(e1))(t)) Bool.true)
                     (expTag(e1)) (expTag(e2))
                     (Eq.subst.{1} FExp (fun (x : FExp) => Eq.{1} Nat (expTag(e1)) (expTag(x))) e1 e2 heq (Eq.refl.{1} Nat (expTag(e1))))
                     (eqNat_refl (expTag(e1)))))

    -- Argument projections (junk catch-alls) + their injectivity.
    fn appFof(e: FExp) -> FExp { match e { | FExp.eapp(f, a) => f | FExp.evar(n) => e | FExp.enat(n) => e | FExp.elam(A, b) => e | FExp.etlam(b) => e | FExp.etapp(f, T) => e } }
    fn appAof(e: FExp) -> FExp { match e { | FExp.eapp(f, a) => a | FExp.evar(n) => e | FExp.enat(n) => e | FExp.elam(A, b) => e | FExp.etlam(b) => e | FExp.etapp(f, T) => e } }
    fn lamTyOf(e: FExp) -> FTy { match e { | FExp.elam(A, b) => A | FExp.evar(n) => FTy.tnat | FExp.enat(n) => FTy.tnat | FExp.eapp(f, a) => FTy.tnat | FExp.etlam(b) => FTy.tnat | FExp.etapp(f, T) => FTy.tnat } }
    fn lamBodyOf(e: FExp) -> FExp { match e { | FExp.elam(A, b) => b | FExp.evar(n) => e | FExp.enat(n) => e | FExp.eapp(f, a) => e | FExp.etlam(b) => e | FExp.etapp(f, T) => e } }
    fn tlamBodyOf(e: FExp) -> FExp { match e { | FExp.etlam(b) => b | FExp.evar(n) => e | FExp.enat(n) => e | FExp.elam(A, b) => e | FExp.eapp(f, a) => e | FExp.etapp(f, T) => e } }
    fn tappFof(e: FExp) -> FExp { match e { | FExp.etapp(f, T) => f | FExp.evar(n) => e | FExp.enat(n) => e | FExp.elam(A, b) => e | FExp.eapp(f, a) => e | FExp.etlam(b) => e } }
    fn tappTyOf(e: FExp) -> FTy { match e { | FExp.etapp(f, T) => T | FExp.evar(n) => FTy.tnat | FExp.enat(n) => FTy.tnat | FExp.elam(A, b) => FTy.tnat | FExp.eapp(f, a) => FTy.tnat | FExp.etlam(b) => FTy.tnat } }
    def eproj_inj (proj : FExp -> FExp) (x : FExp) (y : FExp) (h : Eq.{1} FExp x y) : Eq.{1} FExp (proj x) (proj y) :=
      Eq.subst.{1} FExp (fun (z : FExp) => Eq.{1} FExp (proj x) (proj z)) x y h (Eq.refl.{1} FExp (proj x))
    def etproj_inj (proj : FExp -> FTy) (x : FExp) (y : FExp) (h : Eq.{1} FExp x y) : Eq.{1} FTy (proj x) (proj y) :=
      Eq.subst.{1} FExp (fun (z : FExp) => Eq.{1} FTy (proj x) (proj z)) x y h (Eq.refl.{1} FTy (proj x))

    -- The small-step relation (CBV; mirrors the executable `step`).
    inductive Step : FExp -> FExp -> Prop
      | s_app_l  : (f : FExp) -> (f2 : FExp) -> (a : FExp) -> Step f f2 -> Step (FExp.eapp f a) (FExp.eapp f2 a)
      | s_app_r  : (f : FExp) -> (a : FExp) -> (a2 : FExp) -> Step a a2 -> Step (FExp.eapp f a) (FExp.eapp f a2)
      | s_beta   : (A : FTy) -> (b : FExp) -> (v : FExp) -> Step (FExp.eapp (FExp.elam A b) v) (esubstTm b Nat.zero v)
      | s_tapp   : (f : FExp) -> (f2 : FExp) -> (T : FTy) -> Step f f2 -> Step (FExp.etapp f T) (FExp.etapp f2 T)
      | s_ttbeta : (b : FExp) -> (T : FTy) -> Step (FExp.etapp (FExp.etlam b) T) (esubstTy b Nat.zero T)
"#;

/// **FHasTy inversions + type-constructor injectivity.** From a typing derivation whose
/// subject is a concrete constructor application, recover the premises — the core of the
/// preservation proof's redex cases. Each inverts by matching the derivation over a
/// *variable* index with the concreteness supplied as an `Eq` hypothesis (impossible
/// constructors discharged by `exp_noconf`).
pub const SF_INV: &str = r#"
    inductive And2 (a : Prop) (b : Prop) : Prop | mk : a -> b -> And2 a b
    inductive ExTy (P : FTy -> Prop) : Prop | mk : (A : FTy) -> P A -> ExTy P

    -- Type-constructor injectivity (junk projections + proj_inj).
    fn arrowDom(t: FTy) -> FTy { match t { | FTy.tarrow(a, b) => a | FTy.tvar(n) => FTy.tnat | FTy.tnat => FTy.tnat | FTy.tall(a) => FTy.tnat } }
    fn arrowCod(t: FTy) -> FTy { match t { | FTy.tarrow(a, b) => b | FTy.tvar(n) => FTy.tnat | FTy.tnat => FTy.tnat | FTy.tall(a) => FTy.tnat } }
    fn allBody(t: FTy) -> FTy { match t { | FTy.tall(a) => a | FTy.tvar(n) => FTy.tnat | FTy.tnat => FTy.tnat | FTy.tarrow(a, b) => FTy.tnat } }
    def typroj_inj (proj : FTy -> FTy) (x : FTy) (y : FTy) (h : Eq.{1} FTy x y) : Eq.{1} FTy (proj x) (proj y) :=
      Eq.subst.{1} FTy (fun (z : FTy) => Eq.{1} FTy (proj x) (proj z)) x y h (Eq.refl.{1} FTy (proj x))
    def tarrow_inj_dom (a : FTy) (b : FTy) (c : FTy) (d : FTy) (h : Eq.{1} FTy (FTy.tarrow a b) (FTy.tarrow c d)) : Eq.{1} FTy a c :=
      typroj_inj arrowDom (FTy.tarrow a b) (FTy.tarrow c d) h
    def tarrow_inj_cod (a : FTy) (b : FTy) (c : FTy) (d : FTy) (h : Eq.{1} FTy (FTy.tarrow a b) (FTy.tarrow c d)) : Eq.{1} FTy b d :=
      typroj_inj arrowCod (FTy.tarrow a b) (FTy.tarrow c d) h
    def tall_inj (a : FTy) (b : FTy) (h : Eq.{1} FTy (FTy.tall a) (FTy.tall b)) : Eq.{1} FTy a b :=
      typroj_inj allBody (FTy.tall a) (FTy.tall b) h

    -- λ inversion: a typed `elam A0 b0` has an arrow type with body typed under `cons A0`.
    fn hasty_lam_inv(G: FCtx, e: FExp, T: FTy, d: FHasTy G e T)
      -> ((A0 : FTy) -> (b0 : FExp) -> Eq.{1} FExp e (FExp.elam A0 b0)
            -> ExTy (fun (B : FTy) => And2 (Eq.{1} FTy T (FTy.tarrow A0 B)) (FHasTy (FCtx.cons A0 G) b0 B))) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (A0 : FTy) (b0 : FExp) (heq : Eq.{1} FExp (FExp.evar n2) (FExp.elam A0 b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy T2 (FTy.tarrow A0 B)) (FHasTy (FCtx.cons A0 G2) b0 B))) (exp_noconf (FExp.evar n2) (FExp.elam A0 b0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftnat(G2, n2) => fun (A0 : FTy) (b0 : FExp) (heq : Eq.{1} FExp (FExp.enat n2) (FExp.elam A0 b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy FTy.tnat (FTy.tarrow A0 B)) (FHasTy (FCtx.cons A0 G2) b0 B))) (exp_noconf (FExp.enat n2) (FExp.elam A0 b0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftlam(G2, A2, body2, B2, dbody) => fun (A0 : FTy) (b0 : FExp) (heq : Eq.{1} FExp (FExp.elam A2 body2) (FExp.elam A0 b0)) =>
              ExTy.mk (fun (B : FTy) => And2 (Eq.{1} FTy (FTy.tarrow A2 B2) (FTy.tarrow A0 B)) (FHasTy (FCtx.cons A0 G2) b0 B)) B2
                (And2.mk (Eq.{1} FTy (FTy.tarrow A2 B2) (FTy.tarrow A0 B2)) (FHasTy (FCtx.cons A0 G2) b0 B2)
                  (Eq.subst.{1} FTy (fun (x : FTy) => Eq.{1} FTy (FTy.tarrow A2 B2) (FTy.tarrow x B2)) A2 A0 (etproj_inj lamTyOf (FExp.elam A2 body2) (FExp.elam A0 b0) heq) (Eq.refl.{1} FTy (FTy.tarrow A2 B2)))
                  (Eq.subst.{1} FExp (fun (x : FExp) => FHasTy (FCtx.cons A0 G2) x B2) body2 b0 (eproj_inj lamBodyOf (FExp.elam A2 body2) (FExp.elam A0 b0) heq)
                    (Eq.subst.{1} FTy (fun (x : FTy) => FHasTy (FCtx.cons x G2) body2 B2) A2 A0 (etproj_inj lamTyOf (FExp.elam A2 body2) (FExp.elam A0 b0) heq) dbody)))
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (A0 : FTy) (b0 : FExp) (heq : Eq.{1} FExp (FExp.eapp f2 a2) (FExp.elam A0 b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy B2 (FTy.tarrow A0 B)) (FHasTy (FCtx.cons A0 G2) b0 B))) (exp_noconf (FExp.eapp f2 a2) (FExp.elam A0 b0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.fttlam(G2, body2, B2, dbody) => fun (A0 : FTy) (b0 : FExp) (heq : Eq.{1} FExp (FExp.etlam body2) (FExp.elam A0 b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy (FTy.tall B2) (FTy.tarrow A0 B)) (FHasTy (FCtx.cons A0 G2) b0 B))) (exp_noconf (FExp.etlam body2) (FExp.elam A0 b0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (A0 : FTy) (b0 : FExp) (heq : Eq.{1} FExp (FExp.etapp f2 T2) (FExp.elam A0 b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy (tsubst B2 Nat.zero T2) (FTy.tarrow A0 B)) (FHasTy (FCtx.cons A0 G2) b0 B))) (exp_noconf (FExp.etapp f2 T2) (FExp.elam A0 b0) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }

    -- application inversion: `eapp f0 a0 : T` ⇒ ∃A, f0 : A→T and a0 : A.
    fn hasty_app_inv(G: FCtx, e: FExp, T: FTy, d: FHasTy G e T)
      -> ((f0 : FExp) -> (a0 : FExp) -> Eq.{1} FExp e (FExp.eapp f0 a0)
            -> ExTy (fun (A : FTy) => And2 (FHasTy G f0 (FTy.tarrow A T)) (FHasTy G a0 A))) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (f0 : FExp) (a0 : FExp) (heq : Eq.{1} FExp (FExp.evar n2) (FExp.eapp f0 a0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : FTy) => And2 (FHasTy G2 f0 (FTy.tarrow A T2)) (FHasTy G2 a0 A))) (exp_noconf (FExp.evar n2) (FExp.eapp f0 a0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftnat(G2, n2) => fun (f0 : FExp) (a0 : FExp) (heq : Eq.{1} FExp (FExp.enat n2) (FExp.eapp f0 a0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : FTy) => And2 (FHasTy G2 f0 (FTy.tarrow A FTy.tnat)) (FHasTy G2 a0 A))) (exp_noconf (FExp.enat n2) (FExp.eapp f0 a0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftlam(G2, A2, body2, B2, dbody) => fun (f0 : FExp) (a0 : FExp) (heq : Eq.{1} FExp (FExp.elam A2 body2) (FExp.eapp f0 a0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : FTy) => And2 (FHasTy G2 f0 (FTy.tarrow A (FTy.tarrow A2 B2))) (FHasTy G2 a0 A))) (exp_noconf (FExp.elam A2 body2) (FExp.eapp f0 a0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (f0 : FExp) (a0 : FExp) (heq : Eq.{1} FExp (FExp.eapp f2 a2) (FExp.eapp f0 a0)) =>
              ExTy.mk (fun (A : FTy) => And2 (FHasTy G2 f0 (FTy.tarrow A B2)) (FHasTy G2 a0 A)) A2
                (And2.mk (FHasTy G2 f0 (FTy.tarrow A2 B2)) (FHasTy G2 a0 A2)
                  (Eq.subst.{1} FExp (fun (x : FExp) => FHasTy G2 x (FTy.tarrow A2 B2)) f2 f0 (eproj_inj appFof (FExp.eapp f2 a2) (FExp.eapp f0 a0) heq) df)
                  (Eq.subst.{1} FExp (fun (x : FExp) => FHasTy G2 x A2) a2 a0 (eproj_inj appAof (FExp.eapp f2 a2) (FExp.eapp f0 a0) heq) da))
          | FHasTy.fttlam(G2, body2, B2, dbody) => fun (f0 : FExp) (a0 : FExp) (heq : Eq.{1} FExp (FExp.etlam body2) (FExp.eapp f0 a0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : FTy) => And2 (FHasTy G2 f0 (FTy.tarrow A (FTy.tall B2))) (FHasTy G2 a0 A))) (exp_noconf (FExp.etlam body2) (FExp.eapp f0 a0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (f0 : FExp) (a0 : FExp) (heq : Eq.{1} FExp (FExp.etapp f2 T2) (FExp.eapp f0 a0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (A : FTy) => And2 (FHasTy G2 f0 (FTy.tarrow A (tsubst B2 Nat.zero T2))) (FHasTy G2 a0 A))) (exp_noconf (FExp.etapp f2 T2) (FExp.eapp f0 a0) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }

    -- Λ inversion: `etlam b0 : T` ⇒ ∃B, T = ∀B and b0 : B under shiftCtx.
    fn hasty_tlam_inv(G: FCtx, e: FExp, T: FTy, d: FHasTy G e T)
      -> ((b0 : FExp) -> Eq.{1} FExp e (FExp.etlam b0)
            -> ExTy (fun (B : FTy) => And2 (Eq.{1} FTy T (FTy.tall B)) (FHasTy (shiftCtx G) b0 B))) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (b0 : FExp) (heq : Eq.{1} FExp (FExp.evar n2) (FExp.etlam b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy T2 (FTy.tall B)) (FHasTy (shiftCtx G2) b0 B))) (exp_noconf (FExp.evar n2) (FExp.etlam b0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftnat(G2, n2) => fun (b0 : FExp) (heq : Eq.{1} FExp (FExp.enat n2) (FExp.etlam b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy FTy.tnat (FTy.tall B)) (FHasTy (shiftCtx G2) b0 B))) (exp_noconf (FExp.enat n2) (FExp.etlam b0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftlam(G2, A2, body2, B2, dbody) => fun (b0 : FExp) (heq : Eq.{1} FExp (FExp.elam A2 body2) (FExp.etlam b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy (FTy.tarrow A2 B2) (FTy.tall B)) (FHasTy (shiftCtx G2) b0 B))) (exp_noconf (FExp.elam A2 body2) (FExp.etlam b0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (b0 : FExp) (heq : Eq.{1} FExp (FExp.eapp f2 a2) (FExp.etlam b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy B2 (FTy.tall B)) (FHasTy (shiftCtx G2) b0 B))) (exp_noconf (FExp.eapp f2 a2) (FExp.etlam b0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.fttlam(G2, body2, B2, dbody) => fun (b0 : FExp) (heq : Eq.{1} FExp (FExp.etlam body2) (FExp.etlam b0)) =>
              ExTy.mk (fun (B : FTy) => And2 (Eq.{1} FTy (FTy.tall B2) (FTy.tall B)) (FHasTy (shiftCtx G2) b0 B)) B2
                (And2.mk (Eq.{1} FTy (FTy.tall B2) (FTy.tall B2)) (FHasTy (shiftCtx G2) b0 B2)
                  (Eq.refl.{1} FTy (FTy.tall B2))
                  (Eq.subst.{1} FExp (fun (x : FExp) => FHasTy (shiftCtx G2) x B2) body2 b0 (eproj_inj tlamBodyOf (FExp.etlam body2) (FExp.etlam b0) heq) dbody))
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (b0 : FExp) (heq : Eq.{1} FExp (FExp.etapp f2 T2) (FExp.etlam b0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (Eq.{1} FTy (tsubst B2 Nat.zero T2) (FTy.tall B)) (FHasTy (shiftCtx G2) b0 B))) (exp_noconf (FExp.etapp f2 T2) (FExp.etlam b0) (Eq.refl.{1} Bool Bool.false) heq)
        }
    }

    -- type-application inversion: `etapp f0 T0 : T` ⇒ ∃B, f0 : ∀B and T = B{T0/0}.
    fn hasty_tapp_inv(G: FCtx, e: FExp, T: FTy, d: FHasTy G e T)
      -> ((f0 : FExp) -> (T0 : FTy) -> Eq.{1} FExp e (FExp.etapp f0 T0)
            -> ExTy (fun (B : FTy) => And2 (FHasTy G f0 (FTy.tall B)) (Eq.{1} FTy T (tsubst B Nat.zero T0)))) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (f0 : FExp) (T0 : FTy) (heq : Eq.{1} FExp (FExp.evar n2) (FExp.etapp f0 T0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (FHasTy G2 f0 (FTy.tall B)) (Eq.{1} FTy T2 (tsubst B Nat.zero T0)))) (exp_noconf (FExp.evar n2) (FExp.etapp f0 T0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftnat(G2, n2) => fun (f0 : FExp) (T0 : FTy) (heq : Eq.{1} FExp (FExp.enat n2) (FExp.etapp f0 T0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (FHasTy G2 f0 (FTy.tall B)) (Eq.{1} FTy FTy.tnat (tsubst B Nat.zero T0)))) (exp_noconf (FExp.enat n2) (FExp.etapp f0 T0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftlam(G2, A2, body2, B2, dbody) => fun (f0 : FExp) (T0 : FTy) (heq : Eq.{1} FExp (FExp.elam A2 body2) (FExp.etapp f0 T0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (FHasTy G2 f0 (FTy.tall B)) (Eq.{1} FTy (FTy.tarrow A2 B2) (tsubst B Nat.zero T0)))) (exp_noconf (FExp.elam A2 body2) (FExp.etapp f0 T0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (f0 : FExp) (T0 : FTy) (heq : Eq.{1} FExp (FExp.eapp f2 a2) (FExp.etapp f0 T0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (FHasTy G2 f0 (FTy.tall B)) (Eq.{1} FTy B2 (tsubst B Nat.zero T0)))) (exp_noconf (FExp.eapp f2 a2) (FExp.etapp f0 T0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.fttlam(G2, body2, B2, dbody) => fun (f0 : FExp) (T0 : FTy) (heq : Eq.{1} FExp (FExp.etlam body2) (FExp.etapp f0 T0)) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (B : FTy) => And2 (FHasTy G2 f0 (FTy.tall B)) (Eq.{1} FTy (FTy.tall B2) (tsubst B Nat.zero T0)))) (exp_noconf (FExp.etlam body2) (FExp.etapp f0 T0) (Eq.refl.{1} Bool Bool.false) heq)
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (f0 : FExp) (T0 : FTy) (heq : Eq.{1} FExp (FExp.etapp f2 T2) (FExp.etapp f0 T0)) =>
              ExTy.mk (fun (B : FTy) => And2 (FHasTy G2 f0 (FTy.tall B)) (Eq.{1} FTy (tsubst B2 Nat.zero T2) (tsubst B Nat.zero T0))) B2
                (And2.mk (FHasTy G2 f0 (FTy.tall B2)) (Eq.{1} FTy (tsubst B2 Nat.zero T2) (tsubst B2 Nat.zero T0))
                  (Eq.subst.{1} FExp (fun (x : FExp) => FHasTy G2 x (FTy.tall B2)) f2 f0 (eproj_inj tappFof (FExp.etapp f2 T2) (FExp.etapp f0 T0) heq) df)
                  (Eq.subst.{1} FTy (fun (x : FTy) => Eq.{1} FTy (tsubst B2 Nat.zero T2) (tsubst B2 Nat.zero x)) T2 T0 (etproj_inj tappTyOf (FExp.etapp f2 T2) (FExp.etapp f0 T0) heq) (Eq.refl.{1} FTy (tsubst B2 Nat.zero T2))))
        }
    }
"#;

/// **de Bruijn type-operation lemmas** — the Nat-ordering facts and the
/// shift/substitution commutation lemmas that the type-weakening and type-substitution
/// preservation lemmas rest on. The classic (intricate) core of mechanized System F.
pub const SF_TYLEMMAS: &str = r#"
    inductive Or2 (a : Prop) (b : Prop) : Prop | inl : a -> Or2 a b | inr : b -> Or2 a b
    def bcases (b : Bool) : Or2 (Eq.{1} Bool b Bool.true) (Eq.{1} Bool b Bool.false) :=
      match b {
        | Bool.true  => Or2.inl (Eq.{1} Bool Bool.true Bool.true) (Eq.{1} Bool Bool.true Bool.false) (Eq.refl.{1} Bool Bool.true)
        | Bool.false => Or2.inr (Eq.{1} Bool Bool.false Bool.true) (Eq.{1} Bool Bool.false Bool.false) (Eq.refl.{1} Bool Bool.false)
      }
    fn leNat(x: Nat) -> (Nat -> Bool) {
        match x {
          | Nat.zero    => fun (y : Nat) => Bool.true
          | Nat.succ(x2) => fun (y : Nat) => match y { | Nat.zero => Bool.false | Nat.succ(y2) => leNat(x2)(y2) }
        }
    }
    -- (tarrow_cong / tall_cong / eqNat_sound reused from SF_SAFETY.)

    -- Nat-ordering facts (the gnarly ones recurse on the cutoff).
    fn ltNat_n_0(n: Nat) -> Eq.{1} Bool (ltNat(n)(Nat.zero)) Bool.false {
        match n { | Nat.zero => Eq.refl.{1} Bool Bool.false | Nat.succ(k) => Eq.refl.{1} Bool Bool.false }
    }
    fn ltNat_succ_false(d: Nat)
      -> ((n : Nat) -> Eq.{1} Bool (ltNat(n)(d)) Bool.false -> Eq.{1} Bool (ltNat(Nat.succ(n))(d)) Bool.false) {
        match d {
          | Nat.zero => fun (n : Nat) (h : Eq.{1} Bool (ltNat(n)(Nat.zero)) Bool.false) => Eq.refl.{1} Bool Bool.false
          | Nat.succ(d2) => fun (n : Nat) =>
              match n {
                | Nat.zero    => fun (h : Eq.{1} Bool (ltNat(Nat.zero)(Nat.succ(d2))) Bool.false) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(Nat.succ(Nat.zero))(Nat.succ(d2))) Bool.false)
                      (ff_ne_tt (Eq.symm.{1} Bool (ltNat(Nat.zero)(Nat.succ(d2))) Bool.false h))
                | Nat.succ(n2) => fun (h : Eq.{1} Bool (ltNat(Nat.succ(n2))(Nat.succ(d2))) Bool.false) =>
                    ltNat_succ_false(d2)(n2)(h)
              }
        }
    }
    fn lt_le_trans(d: Nat)
      -> ((n : Nat) -> (c : Nat) -> Eq.{1} Bool (ltNat(n)(d)) Bool.true -> Eq.{1} Bool (leNat(d)(c)) Bool.true -> Eq.{1} Bool (ltNat(n)(c)) Bool.true) {
        match d {
          | Nat.zero => fun (n : Nat) (c : Nat) (h1 : Eq.{1} Bool (ltNat(n)(Nat.zero)) Bool.true) (h2 : Eq.{1} Bool (leNat(Nat.zero)(c)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(n)(c)) Bool.true)
                (ff_ne_tt (Eq.trans.{1} Bool Bool.false (ltNat(n)(Nat.zero)) Bool.true (Eq.symm.{1} Bool (ltNat(n)(Nat.zero)) Bool.false (ltNat_n_0 n)) h1))
          | Nat.succ(d2) => fun (n : Nat) (c : Nat) =>
              match c {
                | Nat.zero => fun (h1 : Eq.{1} Bool (ltNat(n)(Nat.succ(d2))) Bool.true) (h2 : Eq.{1} Bool (leNat(Nat.succ(d2))(Nat.zero)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(n)(Nat.zero)) Bool.true) (ff_ne_tt h2)
                | Nat.succ(c2) =>
                    match n {
                      | Nat.zero    => fun (h1 : Eq.{1} Bool (ltNat(Nat.zero)(Nat.succ(d2))) Bool.true) (h2 : Eq.{1} Bool (leNat(Nat.succ(d2))(Nat.succ(c2))) Bool.true) => Eq.refl.{1} Bool Bool.true
                      | Nat.succ(n2) => fun (h1 : Eq.{1} Bool (ltNat(Nat.succ(n2))(Nat.succ(d2))) Bool.true) (h2 : Eq.{1} Bool (leNat(Nat.succ(d2))(Nat.succ(c2))) Bool.true) => lt_le_trans(d2)(n2)(c2)(h1)(h2)
                    }
              }
        }
    }

    -- congruence + the two shift-on-a-variable rewrites.
    def tshift_cong (a : FTy) (b : FTy) (c : Nat) (h : Eq.{1} FTy a b) : Eq.{1} FTy (tshift(a)(c)) (tshift(b)(c)) :=
      congrArg.{1, 1} FTy FTy (fun (x : FTy) => tshift(x)(c)) a b h
    def tshift_tvar_lt (n : Nat) (c : Nat) (h : Eq.{1} Bool (ltNat(n)(c)) Bool.true) : Eq.{1} FTy (tshift(FTy.tvar(n))(c)) (FTy.tvar n) :=
      Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FTy (match b { | Bool.true => FTy.tvar(n) | Bool.false => FTy.tvar(Nat.succ(n)) }) (FTy.tvar n)) Bool.true (ltNat(n)(c)) (Eq.symm.{1} Bool (ltNat(n)(c)) Bool.true h) (Eq.refl.{1} FTy (FTy.tvar n))
    def tshift_tvar_ge (n : Nat) (c : Nat) (h : Eq.{1} Bool (ltNat(n)(c)) Bool.false) : Eq.{1} FTy (tshift(FTy.tvar(n))(c)) (FTy.tvar (Nat.succ n)) :=
      Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FTy (match b { | Bool.true => FTy.tvar(n) | Bool.false => FTy.tvar(Nat.succ(n)) }) (FTy.tvar (Nat.succ n))) Bool.false (ltNat(n)(c)) (Eq.symm.{1} Bool (ltNat(n)(c)) Bool.false h) (Eq.refl.{1} FTy (FTy.tvar (Nat.succ n)))
    fn leNat_succ_self(n: Nat) -> Eq.{1} Bool (leNat(n)(Nat.succ(n))) Bool.true {
        match n { | Nat.zero => Eq.refl.{1} Bool Bool.true | Nat.succ(k) => leNat_succ_self(k) }
    }
    -- (eqNat_refl reused from SF_STEP.)
    -- If j < n then n is a successor (n = succ (pred n)).
    fn ltNat_pos(n: Nat) -> ((j : Nat) -> Eq.{1} Bool (ltNat(j)(n)) Bool.true -> Eq.{1} Nat n (Nat.succ (pred n))) {
        match n {
          | Nat.zero    => fun (j : Nat) (h : Eq.{1} Bool (ltNat(j)(Nat.zero)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Nat Nat.zero (Nat.succ (pred Nat.zero)))
                (ff_ne_tt (Eq.trans.{1} Bool Bool.false (ltNat(j)(Nat.zero)) Bool.true (Eq.symm.{1} Bool (ltNat(j)(Nat.zero)) Bool.false (ltNat_n_0 j)) h))
          | Nat.succ(m) => fun (j : Nat) (h : Eq.{1} Bool (ltNat(j)(Nat.succ(m))) Bool.true) => Eq.refl.{1} Nat (Nat.succ m)
        }
    }
    -- a ≤ b  ⇒  a < b+1.
    fn le_lt_succ(a: Nat) -> ((b : Nat) -> Eq.{1} Bool (leNat(a)(b)) Bool.true -> Eq.{1} Bool (ltNat(a)(Nat.succ(b))) Bool.true) {
        match a {
          | Nat.zero => fun (b : Nat) (h : Eq.{1} Bool (leNat(Nat.zero)(b)) Bool.true) => Eq.refl.{1} Bool Bool.true
          | Nat.succ(a2) => fun (b : Nat) =>
              match b {
                | Nat.zero    => fun (h : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.zero)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(Nat.succ(a2))(Nat.succ(Nat.zero))) Bool.true) (ff_ne_tt h)
                | Nat.succ(b2) => fun (h : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.succ(b2))) Bool.true) => le_lt_succ(a2)(b2)(h)
              }
        }
    }
    -- a < b  ⇒  a < b+1.
    def lt_succ_weaken (a : Nat) (b : Nat) (h : Eq.{1} Bool (ltNat(a)(b)) Bool.true) : Eq.{1} Bool (ltNat(a)(Nat.succ(b))) Bool.true :=
      lt_le_trans b a (Nat.succ b) h (leNat_succ_self b)
    -- a < b  ⇒  b ≠ a.
    fn ne_of_lt(b: Nat) -> ((a : Nat) -> Eq.{1} Bool (ltNat(a)(b)) Bool.true -> Eq.{1} Bool (eqNat(b)(a)) Bool.false) {
        match b {
          | Nat.zero => fun (a : Nat) (h : Eq.{1} Bool (ltNat(a)(Nat.zero)) Bool.true) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} Bool (eqNat(Nat.zero)(a)) Bool.false)
                (ff_ne_tt (Eq.trans.{1} Bool Bool.false (ltNat(a)(Nat.zero)) Bool.true (Eq.symm.{1} Bool (ltNat(a)(Nat.zero)) Bool.false (ltNat_n_0 a)) h))
          | Nat.succ(b2) => fun (a : Nat) =>
              match a {
                | Nat.zero    => fun (h : Eq.{1} Bool (ltNat(Nat.zero)(Nat.succ(b2))) Bool.true) => Eq.refl.{1} Bool Bool.false
                | Nat.succ(a2) => fun (h : Eq.{1} Bool (ltNat(Nat.succ(a2))(Nat.succ(b2))) Bool.true) => ne_of_lt(b2)(a2)(h)
              }
        }
    }
    -- trichotomy: not-equal and not-greater ⇒ less.
    fn trich(n: Nat) -> ((j : Nat) -> Eq.{1} Bool (eqNat(n)(j)) Bool.false -> Eq.{1} Bool (ltNat(j)(n)) Bool.false -> Eq.{1} Bool (ltNat(n)(j)) Bool.true) {
        match n {
          | Nat.zero => fun (j : Nat) =>
              match j {
                | Nat.zero    => fun (he : Eq.{1} Bool (eqNat(Nat.zero)(Nat.zero)) Bool.false) (hl : Eq.{1} Bool (ltNat(Nat.zero)(Nat.zero)) Bool.false) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(Nat.zero)(Nat.zero)) Bool.true) (ff_ne_tt (Eq.symm.{1} Bool (eqNat(Nat.zero)(Nat.zero)) Bool.false he))
                | Nat.succ(j2) => fun (he : Eq.{1} Bool (eqNat(Nat.zero)(Nat.succ(j2))) Bool.false) (hl : Eq.{1} Bool (ltNat(Nat.succ(j2))(Nat.zero)) Bool.false) =>
                    Eq.refl.{1} Bool Bool.true
              }
          | Nat.succ(n2) => fun (j : Nat) =>
              match j {
                | Nat.zero    => fun (he : Eq.{1} Bool (eqNat(Nat.succ(n2))(Nat.zero)) Bool.false) (hl : Eq.{1} Bool (ltNat(Nat.zero)(Nat.succ(n2))) Bool.false) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(Nat.succ(n2))(Nat.zero)) Bool.true) (ff_ne_tt (Eq.symm.{1} Bool (ltNat(Nat.zero)(Nat.succ(n2))) Bool.false hl))
                | Nat.succ(j2) => fun (he : Eq.{1} Bool (eqNat(Nat.succ(n2))(Nat.succ(j2))) Bool.false) (hl : Eq.{1} Bool (ltNat(Nat.succ(j2))(Nat.succ(n2))) Bool.false) =>
                    trich(n2)(j2)(he)(hl)
              }
        }
    }
    fn eqNat_comm(a: Nat) -> ((b : Nat) -> Eq.{1} Bool (eqNat(a)(b)) (eqNat(b)(a))) {
        match a {
          | Nat.zero => fun (b : Nat) => match b { | Nat.zero => Eq.refl.{1} Bool Bool.true | Nat.succ(b2) => Eq.refl.{1} Bool Bool.false }
          | Nat.succ(a2) => fun (b : Nat) => match b { | Nat.zero => Eq.refl.{1} Bool Bool.false | Nat.succ(b2) => eqNat_comm(a2)(b2) }
        }
    }
    fn le_trans(a: Nat) -> ((b : Nat) -> (c : Nat) -> Eq.{1} Bool (leNat(a)(b)) Bool.true -> Eq.{1} Bool (leNat(b)(c)) Bool.true -> Eq.{1} Bool (leNat(a)(c)) Bool.true) {
        match a {
          | Nat.zero => fun (b : Nat) (c : Nat) (h1 : Eq.{1} Bool (leNat(Nat.zero)(b)) Bool.true) (h2 : Eq.{1} Bool (leNat(b)(c)) Bool.true) => Eq.refl.{1} Bool Bool.true
          | Nat.succ(a2) => fun (b : Nat) =>
              match b {
                | Nat.zero => fun (c : Nat) (h1 : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.zero)) Bool.true) (h2 : Eq.{1} Bool (leNat(Nat.zero)(c)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (leNat(Nat.succ(a2))(c)) Bool.true) (ff_ne_tt h1)
                | Nat.succ(b2) => fun (c : Nat) =>
                    match c {
                      | Nat.zero => fun (h1 : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.succ(b2))) Bool.true) (h2 : Eq.{1} Bool (leNat(Nat.succ(b2))(Nat.zero)) Bool.true) =>
                          False.rec.{0} (fun (_ : False) => Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.zero)) Bool.true) (ff_ne_tt h2)
                      | Nat.succ(c2) => fun (h1 : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.succ(b2))) Bool.true) (h2 : Eq.{1} Bool (leNat(Nat.succ(b2))(Nat.succ(c2))) Bool.true) =>
                          le_trans(a2)(b2)(c2)(h1)(h2)
                    }
              }
        }
    }
    fn le_lt_trans(a: Nat) -> ((b : Nat) -> (c : Nat) -> Eq.{1} Bool (leNat(a)(b)) Bool.true -> Eq.{1} Bool (ltNat(b)(c)) Bool.true -> Eq.{1} Bool (ltNat(a)(c)) Bool.true) {
        match a {
          | Nat.zero => fun (b : Nat) (c : Nat) =>
              match c {
                | Nat.zero => fun (h1 : Eq.{1} Bool (leNat(Nat.zero)(b)) Bool.true) (h2 : Eq.{1} Bool (ltNat(b)(Nat.zero)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(Nat.zero)(Nat.zero)) Bool.true)
                      (ff_ne_tt (Eq.trans.{1} Bool Bool.false (ltNat(b)(Nat.zero)) Bool.true (Eq.symm.{1} Bool (ltNat(b)(Nat.zero)) Bool.false (ltNat_n_0 b)) h2))
                | Nat.succ(c2) => fun (h1 : Eq.{1} Bool (leNat(Nat.zero)(b)) Bool.true) (h2 : Eq.{1} Bool (ltNat(b)(Nat.succ(c2))) Bool.true) => Eq.refl.{1} Bool Bool.true
              }
          | Nat.succ(a2) => fun (b : Nat) =>
              match b {
                | Nat.zero => fun (c : Nat) (h1 : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.zero)) Bool.true) (h2 : Eq.{1} Bool (ltNat(Nat.zero)(c)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(Nat.succ(a2))(c)) Bool.true) (ff_ne_tt h1)
                | Nat.succ(b2) => fun (c : Nat) =>
                    match c {
                      | Nat.zero => fun (h1 : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.succ(b2))) Bool.true) (h2 : Eq.{1} Bool (ltNat(Nat.succ(b2))(Nat.zero)) Bool.true) =>
                          False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(Nat.succ(a2))(Nat.zero)) Bool.true) (ff_ne_tt h2)
                      | Nat.succ(c2) => fun (h1 : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.succ(b2))) Bool.true) (h2 : Eq.{1} Bool (ltNat(Nat.succ(b2))(Nat.succ(c2))) Bool.true) =>
                          le_lt_trans(a2)(b2)(c2)(h1)(h2)
                    }
              }
        }
    }
    fn le_not_lt(a: Nat) -> ((b : Nat) -> Eq.{1} Bool (leNat(a)(b)) Bool.true -> Eq.{1} Bool (ltNat(b)(a)) Bool.false) {
        match a {
          | Nat.zero => fun (b : Nat) (h : Eq.{1} Bool (leNat(Nat.zero)(b)) Bool.true) => ltNat_n_0 b
          | Nat.succ(a2) => fun (b : Nat) =>
              match b {
                | Nat.zero => fun (h : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.zero)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (ltNat(Nat.zero)(Nat.succ(a2))) Bool.false) (ff_ne_tt h)
                | Nat.succ(b2) => fun (h : Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.succ(b2))) Bool.true) => le_not_lt(a2)(b2)(h)
              }
        }
    }
    fn not_lt_imp_le(a: Nat) -> ((b : Nat) -> Eq.{1} Bool (ltNat(a)(b)) Bool.false -> Eq.{1} Bool (leNat(b)(a)) Bool.true) {
        match a {
          | Nat.zero => fun (b : Nat) =>
              match b {
                | Nat.zero => fun (h : Eq.{1} Bool (ltNat(Nat.zero)(Nat.zero)) Bool.false) => Eq.refl.{1} Bool Bool.true
                | Nat.succ(b2) => fun (h : Eq.{1} Bool (ltNat(Nat.zero)(Nat.succ(b2))) Bool.false) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (leNat(Nat.succ(b2))(Nat.zero)) Bool.true) (ff_ne_tt (Eq.symm.{1} Bool (ltNat(Nat.zero)(Nat.succ(b2))) Bool.false h))
              }
          | Nat.succ(a2) => fun (b : Nat) =>
              match b {
                | Nat.zero => fun (h : Eq.{1} Bool (ltNat(Nat.succ(a2))(Nat.zero)) Bool.false) => Eq.refl.{1} Bool Bool.true
                | Nat.succ(b2) => fun (h : Eq.{1} Bool (ltNat(Nat.succ(a2))(Nat.succ(b2))) Bool.false) => not_lt_imp_le(a2)(b2)(h)
              }
        }
    }
    fn lt_imp_le(a: Nat) -> ((b : Nat) -> Eq.{1} Bool (ltNat(a)(b)) Bool.true -> Eq.{1} Bool (leNat(a)(b)) Bool.true) {
        match a {
          | Nat.zero => fun (b : Nat) (h : Eq.{1} Bool (ltNat(Nat.zero)(b)) Bool.true) => Eq.refl.{1} Bool Bool.true
          | Nat.succ(a2) => fun (b : Nat) =>
              match b {
                | Nat.zero => fun (h : Eq.{1} Bool (ltNat(Nat.succ(a2))(Nat.zero)) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.zero)) Bool.true)
                      (ff_ne_tt (Eq.trans.{1} Bool Bool.false (ltNat(Nat.succ(a2))(Nat.zero)) Bool.true (Eq.symm.{1} Bool (ltNat(Nat.succ(a2))(Nat.zero)) Bool.false (ltNat_n_0 (Nat.succ a2))) h))
                | Nat.succ(b2) => fun (h : Eq.{1} Bool (ltNat(Nat.succ(a2))(Nat.succ(b2))) Bool.true) => lt_imp_le(a2)(b2)(h)
              }
        }
    }
    fn lt_succ_le(a: Nat) -> ((b : Nat) -> Eq.{1} Bool (ltNat(a)(Nat.succ(b))) Bool.true -> Eq.{1} Bool (leNat(a)(b)) Bool.true) {
        match a {
          | Nat.zero => fun (b : Nat) (h : Eq.{1} Bool (ltNat(Nat.zero)(Nat.succ(b))) Bool.true) => Eq.refl.{1} Bool Bool.true
          | Nat.succ(a2) => fun (b : Nat) =>
              match b {
                | Nat.zero => fun (h : Eq.{1} Bool (ltNat(Nat.succ(a2))(Nat.succ(Nat.zero))) Bool.true) =>
                    False.rec.{0} (fun (_ : False) => Eq.{1} Bool (leNat(Nat.succ(a2))(Nat.zero)) Bool.true)
                      (ff_ne_tt (Eq.trans.{1} Bool Bool.false (ltNat(a2)(Nat.zero)) Bool.true (Eq.symm.{1} Bool (ltNat(a2)(Nat.zero)) Bool.false (ltNat_n_0 a2)) h))
                | Nat.succ(b2) => fun (h : Eq.{1} Bool (ltNat(Nat.succ(a2))(Nat.succ(Nat.succ(b2)))) Bool.true) => lt_succ_le(a2)(b2)(h)
              }
        }
    }
    -- tsubstVar rewrites (= tsubst on a tvar).
    def tsubstVar_eq (n : Nat) (j : Nat) (s : FTy) (h : Eq.{1} Bool (eqNat(n)(j)) Bool.true) : Eq.{1} FTy (tsubstVar(j, s, n)) s :=
      Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FTy (match b { | Bool.true => s | Bool.false => match ltNat(j)(n) { | Bool.true => FTy.tvar(pred(n)) | Bool.false => FTy.tvar(n) } }) s) Bool.true (eqNat(n)(j)) (Eq.symm.{1} Bool (eqNat(n)(j)) Bool.true h) (Eq.refl.{1} FTy s)
    def tsubstVar_gt (n : Nat) (j : Nat) (s : FTy) (he : Eq.{1} Bool (eqNat(n)(j)) Bool.false) (hl : Eq.{1} Bool (ltNat(j)(n)) Bool.true) : Eq.{1} FTy (tsubstVar(j, s, n)) (FTy.tvar (pred n)) :=
      Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FTy (match b { | Bool.true => s | Bool.false => match ltNat(j)(n) { | Bool.true => FTy.tvar(pred(n)) | Bool.false => FTy.tvar(n) } }) (FTy.tvar (pred n))) Bool.false (eqNat(n)(j)) (Eq.symm.{1} Bool (eqNat(n)(j)) Bool.false he)
        (Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FTy (match b { | Bool.true => FTy.tvar(pred(n)) | Bool.false => FTy.tvar(n) }) (FTy.tvar (pred n))) Bool.true (ltNat(j)(n)) (Eq.symm.{1} Bool (ltNat(j)(n)) Bool.true hl) (Eq.refl.{1} FTy (FTy.tvar (pred n))))
    def tsubstVar_lt (n : Nat) (j : Nat) (s : FTy) (he : Eq.{1} Bool (eqNat(n)(j)) Bool.false) (hl : Eq.{1} Bool (ltNat(j)(n)) Bool.false) : Eq.{1} FTy (tsubstVar(j, s, n)) (FTy.tvar n) :=
      Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FTy (match b { | Bool.true => s | Bool.false => match ltNat(j)(n) { | Bool.true => FTy.tvar(pred(n)) | Bool.false => FTy.tvar(n) } }) (FTy.tvar n)) Bool.false (eqNat(n)(j)) (Eq.symm.{1} Bool (eqNat(n)(j)) Bool.false he)
        (Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FTy (match b { | Bool.true => FTy.tvar(pred(n)) | Bool.false => FTy.tvar(n) }) (FTy.tvar n)) Bool.false (ltNat(j)(n)) (Eq.symm.{1} Bool (ltNat(j)(n)) Bool.false hl) (Eq.refl.{1} FTy (FTy.tvar n)))

    -- SHIFT-SHIFT EXCHANGE: for d ≤ c,  ↑c then ↑d  =  ↑d then ↑(c+1).
    fn tshift_exchange(t: FTy)
      -> ((c : Nat) -> (d : Nat) -> Eq.{1} Bool (leNat(d)(c)) Bool.true
            -> Eq.{1} FTy (tshift(tshift(t)(c))(d)) (tshift(tshift(t)(d))(Nat.succ(c)))) {
        match t {
          | FTy.tnat => fun (c : Nat) (d : Nat) (hle : Eq.{1} Bool (leNat(d)(c)) Bool.true) => Eq.refl.{1} FTy FTy.tnat
          | FTy.tarrow(a, b) => fun (c : Nat) (d : Nat) (hle : Eq.{1} Bool (leNat(d)(c)) Bool.true) =>
              tarrow_cong (tshift(tshift(a)(c))(d)) (tshift(tshift(a)(d))(Nat.succ(c))) (tshift(tshift(b)(c))(d)) (tshift(tshift(b)(d))(Nat.succ(c)))
                (tshift_exchange(a)(c)(d)(hle)) (tshift_exchange(b)(c)(d)(hle))
          | FTy.tall(a) => fun (c : Nat) (d : Nat) (hle : Eq.{1} Bool (leNat(d)(c)) Bool.true) =>
              tall_cong (tshift(tshift(a)(Nat.succ(c)))(Nat.succ(d))) (tshift(tshift(a)(Nat.succ(d)))(Nat.succ(Nat.succ(c))))
                (tshift_exchange(a)(Nat.succ(c))(Nat.succ(d))(hle))
          | FTy.tvar(n) => fun (c : Nat) (d : Nat) (hle : Eq.{1} Bool (leNat(d)(c)) Bool.true) =>
              match bcases(ltNat(n)(d)) {
                | Or2.inl(hd) =>
                    -- n < d ≤ c, so n < c too. Both sides reduce to tvar n.
                    Eq.trans.{1} FTy (tshift(tshift(FTy.tvar(n))(c))(d)) (FTy.tvar n) (tshift(tshift(FTy.tvar(n))(d))(Nat.succ(c)))
                      (Eq.trans.{1} FTy (tshift(tshift(FTy.tvar(n))(c))(d)) (tshift(FTy.tvar(n))(d)) (FTy.tvar n)
                         (tshift_cong (tshift(FTy.tvar(n))(c)) (FTy.tvar n) d (tshift_tvar_lt n c (lt_le_trans d n c hd hle)))
                         (tshift_tvar_lt n d hd))
                      (Eq.symm.{1} FTy (tshift(tshift(FTy.tvar(n))(d))(Nat.succ(c))) (FTy.tvar n)
                         (Eq.trans.{1} FTy (tshift(tshift(FTy.tvar(n))(d))(Nat.succ(c))) (tshift(FTy.tvar(n))(Nat.succ(c))) (FTy.tvar n)
                            (tshift_cong (tshift(FTy.tvar(n))(d)) (FTy.tvar n) (Nat.succ(c)) (tshift_tvar_lt n d hd))
                            (tshift_tvar_lt n (Nat.succ(c)) (lt_le_trans c n (Nat.succ(c)) (lt_le_trans d n c hd hle) (leNat_succ_self c)))))
                | Or2.inr(hd) =>
                    match bcases(ltNat(n)(c)) {
                      | Or2.inl(hc) =>
                          -- d ≤ n < c.  LHS = tvar (succ n); RHS = tvar (succ n).
                          Eq.trans.{1} FTy (tshift(tshift(FTy.tvar(n))(c))(d)) (FTy.tvar (Nat.succ n)) (tshift(tshift(FTy.tvar(n))(d))(Nat.succ(c)))
                            (Eq.trans.{1} FTy (tshift(tshift(FTy.tvar(n))(c))(d)) (tshift(FTy.tvar(n))(d)) (FTy.tvar (Nat.succ n))
                               (tshift_cong (tshift(FTy.tvar(n))(c)) (FTy.tvar n) d (tshift_tvar_lt n c hc))
                               (tshift_tvar_ge n d hd))
                            (Eq.symm.{1} FTy (tshift(tshift(FTy.tvar(n))(d))(Nat.succ(c))) (FTy.tvar (Nat.succ n))
                               (Eq.trans.{1} FTy (tshift(tshift(FTy.tvar(n))(d))(Nat.succ(c))) (tshift(FTy.tvar(Nat.succ(n)))(Nat.succ(c))) (FTy.tvar (Nat.succ n))
                                  (tshift_cong (tshift(FTy.tvar(n))(d)) (FTy.tvar (Nat.succ n)) (Nat.succ(c)) (tshift_tvar_ge n d hd))
                                  (tshift_tvar_lt (Nat.succ n) (Nat.succ(c)) hc)))
                      | Or2.inr(hc) =>
                          -- n ≥ c ≥ d.  LHS = tvar (succ (succ n)); RHS = tvar (succ (succ n)).
                          Eq.trans.{1} FTy (tshift(tshift(FTy.tvar(n))(c))(d)) (FTy.tvar (Nat.succ (Nat.succ n))) (tshift(tshift(FTy.tvar(n))(d))(Nat.succ(c)))
                            (Eq.trans.{1} FTy (tshift(tshift(FTy.tvar(n))(c))(d)) (tshift(FTy.tvar(Nat.succ(n)))(d)) (FTy.tvar (Nat.succ (Nat.succ n)))
                               (tshift_cong (tshift(FTy.tvar(n))(c)) (FTy.tvar (Nat.succ n)) d (tshift_tvar_ge n c hc))
                               (tshift_tvar_ge (Nat.succ n) d (ltNat_succ_false d n hd)))
                            (Eq.symm.{1} FTy (tshift(tshift(FTy.tvar(n))(d))(Nat.succ(c))) (FTy.tvar (Nat.succ (Nat.succ n)))
                               (Eq.trans.{1} FTy (tshift(tshift(FTy.tvar(n))(d))(Nat.succ(c))) (tshift(FTy.tvar(Nat.succ(n)))(Nat.succ(c))) (FTy.tvar (Nat.succ (Nat.succ n)))
                                  (tshift_cong (tshift(FTy.tvar(n))(d)) (FTy.tvar (Nat.succ n)) (Nat.succ(c)) (tshift_tvar_ge n d hd))
                                  (tshift_tvar_ge (Nat.succ n) (Nat.succ(c)) hc)))
                    }
              }
        }
    }

    def tsubst1_cong (T1 : FTy) (T2 : FTy) (j : Nat) (s : FTy) (h : Eq.{1} FTy T1 T2) : Eq.{1} FTy (tsubst(T1)(j)(s)) (tsubst(T2)(j)(s)) :=
      congrArg.{1, 1} FTy FTy (fun (z : FTy) => tsubst(z)(j)(s)) T1 T2 h
    def tsubst3_cong (T : FTy) (j : Nat) (x : FTy) (y : FTy) (h : Eq.{1} FTy x y) : Eq.{1} FTy (tsubst(T)(j)(x)) (tsubst(T)(j)(y)) :=
      congrArg.{1, 1} FTy FTy (fun (z : FTy) => tsubst(T)(j)(z)) x y h

    -- SHIFT-SUBST COMMUTE: for j ≤ c,  ↑c (t{s/j})  =  (↑(c+1) t){↑c s / j}.
    fn shift_subst_comm(t: FTy)
      -> ((j : Nat) -> (s : FTy) -> (c : Nat) -> Eq.{1} Bool (leNat(j)(c)) Bool.true
            -> Eq.{1} FTy (tshift(tsubst(t)(j)(s))(c)) (tsubst(tshift(t)(Nat.succ(c)))(j)(tshift(s)(c)))) {
        match t {
          | FTy.tnat => fun (j : Nat) (s : FTy) (c : Nat) (hle : Eq.{1} Bool (leNat(j)(c)) Bool.true) => Eq.refl.{1} FTy FTy.tnat
          | FTy.tarrow(a, b) => fun (j : Nat) (s : FTy) (c : Nat) (hle : Eq.{1} Bool (leNat(j)(c)) Bool.true) =>
              tarrow_cong (tshift(tsubst(a)(j)(s))(c)) (tsubst(tshift(a)(Nat.succ(c)))(j)(tshift(s)(c))) (tshift(tsubst(b)(j)(s))(c)) (tsubst(tshift(b)(Nat.succ(c)))(j)(tshift(s)(c)))
                (shift_subst_comm(a)(j)(s)(c)(hle)) (shift_subst_comm(b)(j)(s)(c)(hle))
          | FTy.tall(a) => fun (j : Nat) (s : FTy) (c : Nat) (hle : Eq.{1} Bool (leNat(j)(c)) Bool.true) =>
              tall_cong (tshift(tsubst(a)(Nat.succ(j))(tshift(s)(Nat.zero)))(Nat.succ(c))) (tsubst(tshift(a)(Nat.succ(Nat.succ(c))))(Nat.succ(j))(tshift(tshift(s)(c))(Nat.zero)))
                (Eq.trans.{1} FTy (tshift(tsubst(a)(Nat.succ(j))(tshift(s)(Nat.zero)))(Nat.succ(c))) (tsubst(tshift(a)(Nat.succ(Nat.succ(c))))(Nat.succ(j))(tshift(tshift(s)(Nat.zero))(Nat.succ(c)))) (tsubst(tshift(a)(Nat.succ(Nat.succ(c))))(Nat.succ(j))(tshift(tshift(s)(c))(Nat.zero)))
                   (shift_subst_comm(a)(Nat.succ(j))(tshift(s)(Nat.zero))(Nat.succ(c))(hle))
                   (tsubst3_cong (tshift(a)(Nat.succ(Nat.succ(c)))) (Nat.succ(j)) (tshift(tshift(s)(Nat.zero))(Nat.succ(c))) (tshift(tshift(s)(c))(Nat.zero))
                      (Eq.symm.{1} FTy (tshift(tshift(s)(c))(Nat.zero)) (tshift(tshift(s)(Nat.zero))(Nat.succ(c))) (tshift_exchange(s)(c)(Nat.zero)(Eq.refl.{1} Bool Bool.true)))))
          | FTy.tvar(n) => fun (j : Nat) (s : FTy) (c : Nat) (hle : Eq.{1} Bool (leNat(j)(c)) Bool.true) =>
              match bcases(eqNat(n)(j)) {
                | Or2.inl(he) =>
                    Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(s))(c)) (tshift(s)(c)) (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c)))
                      (tshift_cong (tsubst(FTy.tvar(n))(j)(s)) s c (tsubstVar_eq n j s he))
                      (Eq.symm.{1} FTy (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c))) (tshift(s)(c))
                         (Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c))) (tsubst(FTy.tvar(n))(j)(tshift(s)(c))) (tshift(s)(c))
                            (tsubst1_cong (tshift(FTy.tvar(n))(Nat.succ(c))) (FTy.tvar n) j (tshift(s)(c)) (tshift_tvar_lt n (Nat.succ(c)) (le_lt_succ n c (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (leNat(x)(c)) Bool.true) j n (Eq.symm.{1} Nat n j (eqNat_sound(n)(j)(he))) hle))))
                            (tsubstVar_eq n j (tshift(s)(c)) he)))
                | Or2.inr(he) =>
                    match bcases(ltNat(j)(n)) {
                      | Or2.inl(hl) =>
                          match bcases(ltNat(pred(n))(c)) {
                            | Or2.inl(hpc) =>
                                Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(s))(c)) (FTy.tvar (pred n)) (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c)))
                                  (Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(s))(c)) (tshift(FTy.tvar(pred(n)))(c)) (FTy.tvar (pred n))
                                     (tshift_cong (tsubst(FTy.tvar(n))(j)(s)) (FTy.tvar (pred n)) c (tsubstVar_gt n j s he hl))
                                     (tshift_tvar_lt (pred n) c hpc))
                                  (Eq.symm.{1} FTy (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c))) (FTy.tvar (pred n))
                                     (Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c))) (tsubst(FTy.tvar(n))(j)(tshift(s)(c))) (FTy.tvar (pred n))
                                        (tsubst1_cong (tshift(FTy.tvar(n))(Nat.succ(c))) (FTy.tvar n) j (tshift(s)(c)) (tshift_tvar_lt n (Nat.succ(c)) (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (ltNat(x)(Nat.succ(c))) Bool.true) (Nat.succ (pred n)) n (Eq.symm.{1} Nat n (Nat.succ (pred n)) (ltNat_pos(n)(j)(hl))) hpc)))
                                        (tsubstVar_gt n j (tshift(s)(c)) he hl)))
                            | Or2.inr(hpcf) =>
                                Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(s))(c)) (FTy.tvar n) (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c)))
                                  (Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(s))(c)) (FTy.tvar (Nat.succ (pred n))) (FTy.tvar n)
                                     (Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(s))(c)) (tshift(FTy.tvar(pred(n)))(c)) (FTy.tvar (Nat.succ (pred n)))
                                        (tshift_cong (tsubst(FTy.tvar(n))(j)(s)) (FTy.tvar (pred n)) c (tsubstVar_gt n j s he hl))
                                        (tshift_tvar_ge (pred n) c hpcf))
                                     (tvar_cong (Nat.succ (pred n)) n (Eq.symm.{1} Nat n (Nat.succ (pred n)) (ltNat_pos(n)(j)(hl)))))
                                  (Eq.symm.{1} FTy (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c))) (FTy.tvar n)
                                     (Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c))) (tsubst(FTy.tvar(Nat.succ(n)))(j)(tshift(s)(c))) (FTy.tvar n)
                                        (tsubst1_cong (tshift(FTy.tvar(n))(Nat.succ(c))) (FTy.tvar (Nat.succ n)) j (tshift(s)(c)) (tshift_tvar_ge n (Nat.succ(c)) (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (ltNat(x)(Nat.succ(c))) Bool.false) (Nat.succ (pred n)) n (Eq.symm.{1} Nat n (Nat.succ (pred n)) (ltNat_pos(n)(j)(hl))) hpcf)))
                                        (tsubstVar_gt (Nat.succ n) j (tshift(s)(c)) (ne_of_lt (Nat.succ n) j (lt_succ_weaken j n hl)) (lt_succ_weaken j n hl))))
                          }
                      | Or2.inr(hlf) =>
                          Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(s))(c)) (FTy.tvar n) (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c)))
                            (Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(s))(c)) (tshift(FTy.tvar(n))(c)) (FTy.tvar n)
                               (tshift_cong (tsubst(FTy.tvar(n))(j)(s)) (FTy.tvar n) c (tsubstVar_lt n j s he hlf))
                               (tshift_tvar_lt n c (lt_le_trans j n c (trich n j he hlf) hle)))
                            (Eq.symm.{1} FTy (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c))) (FTy.tvar n)
                               (Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(Nat.succ(c)))(j)(tshift(s)(c))) (tsubst(FTy.tvar(n))(j)(tshift(s)(c))) (FTy.tvar n)
                                  (tsubst1_cong (tshift(FTy.tvar(n))(Nat.succ(c))) (FTy.tvar n) j (tshift(s)(c)) (tshift_tvar_lt n (Nat.succ(c)) (lt_succ_weaken n c (lt_le_trans j n c (trich n j he hlf) hle))))
                                  (tsubstVar_lt n j (tshift(s)(c)) he hlf)))
                    }
              }
        }
    }

    -- SUBST-SHIFT COMMUTE: for c ≤ j,  (↑c t){↑c S / (j+1)}  =  ↑c (t{S/j}).
    fn subst_shift_comm(t: FTy)
      -> ((j : Nat) -> (S : FTy) -> (c : Nat) -> Eq.{1} Bool (leNat(c)(j)) Bool.true
            -> Eq.{1} FTy (tsubst(tshift(t)(c))(Nat.succ(j))(tshift(S)(c))) (tshift(tsubst(t)(j)(S))(c))) {
        match t {
          | FTy.tnat => fun (j : Nat) (S : FTy) (c : Nat) (hcj : Eq.{1} Bool (leNat(c)(j)) Bool.true) => Eq.refl.{1} FTy FTy.tnat
          | FTy.tarrow(a, b) => fun (j : Nat) (S : FTy) (c : Nat) (hcj : Eq.{1} Bool (leNat(c)(j)) Bool.true) =>
              tarrow_cong (tsubst(tshift(a)(c))(Nat.succ(j))(tshift(S)(c))) (tshift(tsubst(a)(j)(S))(c)) (tsubst(tshift(b)(c))(Nat.succ(j))(tshift(S)(c))) (tshift(tsubst(b)(j)(S))(c))
                (subst_shift_comm(a)(j)(S)(c)(hcj)) (subst_shift_comm(b)(j)(S)(c)(hcj))
          | FTy.tall(a) => fun (j : Nat) (S : FTy) (c : Nat) (hcj : Eq.{1} Bool (leNat(c)(j)) Bool.true) =>
              tall_cong (tsubst(tshift(a)(Nat.succ(c)))(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(c))(Nat.zero))) (tshift(tsubst(a)(Nat.succ(j))(tshift(S)(Nat.zero)))(Nat.succ(c)))
                (Eq.trans.{1} FTy (tsubst(tshift(a)(Nat.succ(c)))(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(c))(Nat.zero))) (tsubst(tshift(a)(Nat.succ(c)))(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(Nat.zero))(Nat.succ(c)))) (tshift(tsubst(a)(Nat.succ(j))(tshift(S)(Nat.zero)))(Nat.succ(c)))
                   (tsubst3_cong (tshift(a)(Nat.succ(c))) (Nat.succ(Nat.succ(j))) (tshift(tshift(S)(c))(Nat.zero)) (tshift(tshift(S)(Nat.zero))(Nat.succ(c))) (tshift_exchange(S)(c)(Nat.zero)(Eq.refl.{1} Bool Bool.true)))
                   (subst_shift_comm(a)(Nat.succ(j))(tshift(S)(Nat.zero))(Nat.succ(c))(hcj)))
          | FTy.tvar(n) => fun (j : Nat) (S : FTy) (c : Nat) (hcj : Eq.{1} Bool (leNat(c)(j)) Bool.true) =>
              match bcases(eqNat(n)(j)) {
                | Or2.inl(he) =>
                    Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(c))(Nat.succ(j))(tshift(S)(c))) (tshift(S)(c)) (tshift(tsubst(FTy.tvar(n))(j)(S))(c))
                      (Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(c))(Nat.succ(j))(tshift(S)(c))) (tsubst(FTy.tvar(Nat.succ(n)))(Nat.succ(j))(tshift(S)(c))) (tshift(S)(c))
                         (tsubst1_cong (tshift(FTy.tvar(n))(c)) (FTy.tvar (Nat.succ n)) (Nat.succ(j)) (tshift(S)(c)) (tshift_tvar_ge n c (le_not_lt c n (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (leNat(c)(x)) Bool.true) j n (Eq.symm.{1} Nat n j (eqNat_sound(n)(j)(he))) hcj))))
                         (tsubstVar_eq (Nat.succ n) (Nat.succ j) (tshift(S)(c)) he))
                      (Eq.symm.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(S))(c)) (tshift(S)(c))
                         (tshift_cong (tsubst(FTy.tvar(n))(j)(S)) S c (tsubstVar_eq n j S he)))
                | Or2.inr(he) =>
                    match bcases(ltNat(j)(n)) {
                      | Or2.inl(hl) =>
                          Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(c))(Nat.succ(j))(tshift(S)(c))) (FTy.tvar n) (tshift(tsubst(FTy.tvar(n))(j)(S))(c))
                            (Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(c))(Nat.succ(j))(tshift(S)(c))) (tsubst(FTy.tvar(Nat.succ(n)))(Nat.succ(j))(tshift(S)(c))) (FTy.tvar n)
                               (tsubst1_cong (tshift(FTy.tvar(n))(c)) (FTy.tvar (Nat.succ n)) (Nat.succ(j)) (tshift(S)(c)) (tshift_tvar_ge n c (le_not_lt c n (le_trans c j n hcj (lt_imp_le j n hl)))))
                               (tsubstVar_gt (Nat.succ n) (Nat.succ j) (tshift(S)(c)) he hl))
                            (Eq.symm.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(S))(c)) (FTy.tvar n)
                               (Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(S))(c)) (FTy.tvar (Nat.succ (pred n))) (FTy.tvar n)
                                  (Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(S))(c)) (tshift(FTy.tvar(pred(n)))(c)) (FTy.tvar (Nat.succ (pred n)))
                                     (tshift_cong (tsubst(FTy.tvar(n))(j)(S)) (FTy.tvar (pred n)) c (tsubstVar_gt n j S he hl))
                                     (tshift_tvar_ge (pred n) c (le_not_lt c (pred n) (le_trans c j (pred n) hcj (lt_succ_le j (pred n) (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (ltNat(j)(x)) Bool.true) n (Nat.succ (pred n)) (ltNat_pos(n)(j)(hl)) hl))))))
                                  (tvar_cong (Nat.succ (pred n)) n (Eq.symm.{1} Nat n (Nat.succ (pred n)) (ltNat_pos(n)(j)(hl))))))
                      | Or2.inr(hlf) =>
                          match bcases(ltNat(n)(c)) {
                            | Or2.inl(hc) =>
                                Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(c))(Nat.succ(j))(tshift(S)(c))) (FTy.tvar n) (tshift(tsubst(FTy.tvar(n))(j)(S))(c))
                                  (Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(c))(Nat.succ(j))(tshift(S)(c))) (tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(c))) (FTy.tvar n)
                                     (tsubst1_cong (tshift(FTy.tvar(n))(c)) (FTy.tvar n) (Nat.succ(j)) (tshift(S)(c)) (tshift_tvar_lt n c hc))
                                     (tsubstVar_lt n (Nat.succ j) (tshift(S)(c)) (Eq.trans.{1} Bool (eqNat(n)(Nat.succ(j))) (eqNat(Nat.succ(j))(n)) Bool.false (eqNat_comm n (Nat.succ j)) (ne_of_lt (Nat.succ j) n (lt_succ_weaken n j (trich n j he hlf)))) (le_not_lt n (Nat.succ j) (lt_imp_le n (Nat.succ j) (lt_succ_weaken n j (trich n j he hlf))))))
                                  (Eq.symm.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(S))(c)) (FTy.tvar n)
                                     (Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(S))(c)) (tshift(FTy.tvar(n))(c)) (FTy.tvar n)
                                        (tshift_cong (tsubst(FTy.tvar(n))(j)(S)) (FTy.tvar n) c (tsubstVar_lt n j S he hlf))
                                        (tshift_tvar_lt n c hc)))
                            | Or2.inr(hcf) =>
                                Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(c))(Nat.succ(j))(tshift(S)(c))) (FTy.tvar (Nat.succ n)) (tshift(tsubst(FTy.tvar(n))(j)(S))(c))
                                  (Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(c))(Nat.succ(j))(tshift(S)(c))) (tsubst(FTy.tvar(Nat.succ(n)))(Nat.succ(j))(tshift(S)(c))) (FTy.tvar (Nat.succ n))
                                     (tsubst1_cong (tshift(FTy.tvar(n))(c)) (FTy.tvar (Nat.succ n)) (Nat.succ(j)) (tshift(S)(c)) (tshift_tvar_ge n c hcf))
                                     (tsubstVar_lt (Nat.succ n) (Nat.succ j) (tshift(S)(c)) he hlf))
                                  (Eq.symm.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(S))(c)) (FTy.tvar (Nat.succ n))
                                     (Eq.trans.{1} FTy (tshift(tsubst(FTy.tvar(n))(j)(S))(c)) (tshift(FTy.tvar(n))(c)) (FTy.tvar (Nat.succ n))
                                        (tshift_cong (tsubst(FTy.tvar(n))(j)(S)) (FTy.tvar n) c (tsubstVar_lt n j S he hlf))
                                        (tshift_tvar_ge n c hcf)))
                          }
                    }
              }
        }
    }

    -- CANCEL: substituting at the position you just shifted at undoes it:  (↑i t){s / i} = t.
    fn tcancel(t: FTy)
      -> ((i : Nat) -> (s : FTy) -> Eq.{1} FTy (tsubst(tshift(t)(i))(i)(s)) t) {
        match t {
          | FTy.tnat => fun (i : Nat) (s : FTy) => Eq.refl.{1} FTy FTy.tnat
          | FTy.tarrow(a, b) => fun (i : Nat) (s : FTy) =>
              tarrow_cong (tsubst(tshift(a)(i))(i)(s)) a (tsubst(tshift(b)(i))(i)(s)) b (tcancel(a)(i)(s)) (tcancel(b)(i)(s))
          | FTy.tall(a) => fun (i : Nat) (s : FTy) =>
              tall_cong (tsubst(tshift(a)(Nat.succ(i)))(Nat.succ(i))(tshift(s)(Nat.zero))) a (tcancel(a)(Nat.succ(i))(tshift(s)(Nat.zero)))
          | FTy.tvar(n) => fun (i : Nat) (s : FTy) =>
              match bcases(ltNat(n)(i)) {
                | Or2.inl(hlt) =>
                    Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(i))(i)(s)) (tsubst(FTy.tvar(n))(i)(s)) (FTy.tvar n)
                      (tsubst1_cong (tshift(FTy.tvar(n))(i)) (FTy.tvar n) i s (tshift_tvar_lt n i hlt))
                      (tsubstVar_lt n i s (Eq.trans.{1} Bool (eqNat(n)(i)) (eqNat(i)(n)) Bool.false (eqNat_comm n i) (ne_of_lt i n hlt)) (le_not_lt n i (lt_imp_le n i hlt)))
                | Or2.inr(hge) =>
                    Eq.trans.{1} FTy (tsubst(tshift(FTy.tvar(n))(i))(i)(s)) (tsubst(FTy.tvar(Nat.succ(n)))(i)(s)) (FTy.tvar n)
                      (tsubst1_cong (tshift(FTy.tvar(n))(i)) (FTy.tvar (Nat.succ n)) i s (tshift_tvar_ge n i hge))
                      (tsubstVar_gt (Nat.succ n) i s (ne_of_lt (Nat.succ n) i (le_lt_succ i n (not_lt_imp_le n i hge))) (le_lt_succ i n (not_lt_imp_le n i hge)))
              }
        }
    }

    -- SUBST-SUBST COMMUTE (the type substitution lemma): for i ≤ j,
    --   (t{U/i}){S/j}  =  (t{↑i S / (j+1)}){ U{S/j} / i }.
    fn subst_subst_comm(t: FTy)
      -> ((i : Nat) -> (U : FTy) -> (j : Nat) -> (S : FTy) -> Eq.{1} Bool (leNat(i)(j)) Bool.true
            -> Eq.{1} FTy (tsubst(tsubst(t)(i)(U))(j)(S)) (tsubst(tsubst(t)(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S)))) {
        match t {
          | FTy.tnat => fun (i : Nat) (U : FTy) (j : Nat) (S : FTy) (hij : Eq.{1} Bool (leNat(i)(j)) Bool.true) => Eq.refl.{1} FTy FTy.tnat
          | FTy.tarrow(a, b) => fun (i : Nat) (U : FTy) (j : Nat) (S : FTy) (hij : Eq.{1} Bool (leNat(i)(j)) Bool.true) =>
              tarrow_cong (tsubst(tsubst(a)(i)(U))(j)(S)) (tsubst(tsubst(a)(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (tsubst(tsubst(b)(i)(U))(j)(S)) (tsubst(tsubst(b)(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S)))
                (subst_subst_comm(a)(i)(U)(j)(S)(hij)) (subst_subst_comm(b)(i)(U)(j)(S)(hij))
          | FTy.tall(a) => fun (i : Nat) (U : FTy) (j : Nat) (S : FTy) (hij : Eq.{1} Bool (leNat(i)(j)) Bool.true) =>
              tall_cong (tsubst(tsubst(a)(Nat.succ(i))(tshift(U)(Nat.zero)))(Nat.succ(j))(tshift(S)(Nat.zero))) (tsubst(tsubst(a)(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(i))(Nat.zero)))(Nat.succ(i))(tshift(tsubst(U)(j)(S))(Nat.zero)))
                (Eq.trans.{1} FTy (tsubst(tsubst(a)(Nat.succ(i))(tshift(U)(Nat.zero)))(Nat.succ(j))(tshift(S)(Nat.zero))) (tsubst(tsubst(a)(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(Nat.zero))(Nat.succ(i))))(Nat.succ(i))(tsubst(tshift(U)(Nat.zero))(Nat.succ(j))(tshift(S)(Nat.zero)))) (tsubst(tsubst(a)(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(i))(Nat.zero)))(Nat.succ(i))(tshift(tsubst(U)(j)(S))(Nat.zero)))
                   (subst_subst_comm(a)(Nat.succ(i))(tshift(U)(Nat.zero))(Nat.succ(j))(tshift(S)(Nat.zero))(hij))
                   (Eq.trans.{1} FTy (tsubst(tsubst(a)(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(Nat.zero))(Nat.succ(i))))(Nat.succ(i))(tsubst(tshift(U)(Nat.zero))(Nat.succ(j))(tshift(S)(Nat.zero)))) (tsubst(tsubst(a)(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(Nat.zero))(Nat.succ(i))))(Nat.succ(i))(tshift(tsubst(U)(j)(S))(Nat.zero))) (tsubst(tsubst(a)(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(i))(Nat.zero)))(Nat.succ(i))(tshift(tsubst(U)(j)(S))(Nat.zero)))
                      (tsubst3_cong (tsubst(a)(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(Nat.zero))(Nat.succ(i)))) (Nat.succ(i)) (tsubst(tshift(U)(Nat.zero))(Nat.succ(j))(tshift(S)(Nat.zero))) (tshift(tsubst(U)(j)(S))(Nat.zero)) (subst_shift_comm(U)(j)(S)(Nat.zero)(Eq.refl.{1} Bool Bool.true)))
                      (tsubst1_cong (tsubst(a)(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(Nat.zero))(Nat.succ(i)))) (tsubst(a)(Nat.succ(Nat.succ(j)))(tshift(tshift(S)(i))(Nat.zero))) (Nat.succ(i)) (tshift(tsubst(U)(j)(S))(Nat.zero)) (tsubst3_cong a (Nat.succ(Nat.succ(j))) (tshift(tshift(S)(Nat.zero))(Nat.succ(i))) (tshift(tshift(S)(i))(Nat.zero)) (Eq.symm.{1} FTy (tshift(tshift(S)(i))(Nat.zero)) (tshift(tshift(S)(Nat.zero))(Nat.succ(i))) (tshift_exchange(S)(i)(Nat.zero)(Eq.refl.{1} Bool Bool.true)))))))
          | FTy.tvar(n) => fun (i : Nat) (U : FTy) (j : Nat) (S : FTy) (hij : Eq.{1} Bool (leNat(i)(j)) Bool.true) =>
              match bcases(eqNat(n)(i)) {
                | Or2.inl(hei) =>
                    -- n = i.  LHS = U{S/j};  RHS = U{S/j}.
                    Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(i)(U))(j)(S)) (tsubst(U)(j)(S)) (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S)))
                      (tsubst1_cong (tsubst(FTy.tvar(n))(i)(U)) U j S (tsubstVar_eq n i U hei))
                      (Eq.symm.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (tsubst(U)(j)(S))
                         (Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (tsubst(FTy.tvar(n))(i)(tsubst(U)(j)(S))) (tsubst(U)(j)(S))
                            (tsubst1_cong (tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i))) (FTy.tvar n) i (tsubst(U)(j)(S)) (tsubstVar_lt n (Nat.succ j) (tshift(S)(i)) (Eq.trans.{1} Bool (eqNat(n)(Nat.succ(j))) (eqNat(Nat.succ(j))(n)) Bool.false (eqNat_comm n (Nat.succ j)) (ne_of_lt (Nat.succ j) n (le_lt_succ n j (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (leNat(x)(j)) Bool.true) i n (Eq.symm.{1} Nat n i (eqNat_sound(n)(i)(hei))) hij)))) (le_not_lt n (Nat.succ j) (lt_imp_le n (Nat.succ j) (le_lt_succ n j (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (leNat(x)(j)) Bool.true) i n (Eq.symm.{1} Nat n i (eqNat_sound(n)(i)(hei))) hij))))))
                            (tsubstVar_eq n i (tsubst(U)(j)(S)) hei)))
                | Or2.inr(hei) =>
                    match bcases(ltNat(i)(n)) {
                      | Or2.inl(hli) =>
                          match bcases(ltNat(pred(n))(j)) {
                            | Or2.inl(hpj) =>
                                -- i < n < (j+1).  LHS = tvar (pred n);  RHS = tvar (pred n).
                                Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(i)(U))(j)(S)) (FTy.tvar (pred n)) (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S)))
                                  (Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(i)(U))(j)(S)) (tsubst(FTy.tvar(pred(n)))(j)(S)) (FTy.tvar (pred n))
                                     (tsubst1_cong (tsubst(FTy.tvar(n))(i)(U)) (FTy.tvar (pred n)) j S (tsubstVar_gt n i U hei hli))
                                     (tsubstVar_lt (pred n) j S (Eq.trans.{1} Bool (eqNat(pred(n))(j)) (eqNat(j)(pred(n))) Bool.false (eqNat_comm (pred n) j) (ne_of_lt j (pred n) hpj)) (le_not_lt (pred n) j (lt_imp_le (pred n) j hpj))))
                                  (Eq.symm.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (FTy.tvar (pred n))
                                     (Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (tsubst(FTy.tvar(n))(i)(tsubst(U)(j)(S))) (FTy.tvar (pred n))
                                        (tsubst1_cong (tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i))) (FTy.tvar n) i (tsubst(U)(j)(S)) (tsubstVar_lt n (Nat.succ j) (tshift(S)(i)) (Eq.trans.{1} Bool (eqNat(n)(Nat.succ(j))) (eqNat(Nat.succ(j))(n)) Bool.false (eqNat_comm n (Nat.succ j)) (ne_of_lt (Nat.succ j) n (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (ltNat(x)(Nat.succ(j))) Bool.true) (Nat.succ (pred n)) n (Eq.symm.{1} Nat n (Nat.succ (pred n)) (ltNat_pos(n)(i)(hli))) hpj))) (le_not_lt n (Nat.succ j) (lt_imp_le n (Nat.succ j) (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (ltNat(x)(Nat.succ(j))) Bool.true) (Nat.succ (pred n)) n (Eq.symm.{1} Nat n (Nat.succ (pred n)) (ltNat_pos(n)(i)(hli))) hpj)))))
                                        (tsubstVar_gt n i (tsubst(U)(j)(S)) hei hli)))
                            | Or2.inr(hpjf) =>
                                match bcases(eqNat(pred(n))(j)) {
                                  | Or2.inl(hpej) =>
                                      -- n = j+1.  LHS = S;  RHS = (↑i S){U{S/j}/i} = S.
                                      Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(i)(U))(j)(S)) S (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S)))
                                        (Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(i)(U))(j)(S)) (tsubst(FTy.tvar(pred(n)))(j)(S)) S
                                           (tsubst1_cong (tsubst(FTy.tvar(n))(i)(U)) (FTy.tvar (pred n)) j S (tsubstVar_gt n i U hei hli))
                                           (tsubstVar_eq (pred n) j S hpej))
                                        (Eq.symm.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) S
                                           (Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (tsubst(tshift(S)(i))(i)(tsubst(U)(j)(S))) S
                                              (tsubst1_cong (tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i))) (tshift(S)(i)) i (tsubst(U)(j)(S)) (tsubstVar_eq n (Nat.succ j) (tshift(S)(i)) (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (eqNat(x)(Nat.succ(j))) Bool.true) (Nat.succ (pred n)) n (Eq.symm.{1} Nat n (Nat.succ (pred n)) (ltNat_pos(n)(i)(hli))) hpej)))
                                              (tcancel S i (tsubst(U)(j)(S)))))
                                  | Or2.inr(hpejf) =>
                                      -- n > j+1.  LHS = tvar (pred (pred n));  RHS = tvar (pred (pred n)).
                                      Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(i)(U))(j)(S)) (FTy.tvar (pred (pred n))) (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S)))
                                        (Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(i)(U))(j)(S)) (tsubst(FTy.tvar(pred(n)))(j)(S)) (FTy.tvar (pred (pred n)))
                                           (tsubst1_cong (tsubst(FTy.tvar(n))(i)(U)) (FTy.tvar (pred n)) j S (tsubstVar_gt n i U hei hli))
                                           (tsubstVar_gt (pred n) j S hpejf (trich j (pred n) (Eq.trans.{1} Bool (eqNat(j)(pred(n))) (eqNat(pred(n))(j)) Bool.false (eqNat_comm j (pred n)) hpejf) hpjf)))
                                        (Eq.symm.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (FTy.tvar (pred (pred n)))
                                           (Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (tsubst(FTy.tvar(pred(n)))(i)(tsubst(U)(j)(S))) (FTy.tvar (pred (pred n)))
                                              (tsubst1_cong (tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i))) (FTy.tvar (pred n)) i (tsubst(U)(j)(S)) (tsubstVar_gt n (Nat.succ j) (tshift(S)(i)) (ne_of_lt n (Nat.succ j) (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (ltNat(Nat.succ(j))(x)) Bool.true) (Nat.succ (pred n)) n (Eq.symm.{1} Nat n (Nat.succ (pred n)) (ltNat_pos(n)(i)(hli))) (trich j (pred n) (Eq.trans.{1} Bool (eqNat(j)(pred(n))) (eqNat(pred(n))(j)) Bool.false (eqNat_comm j (pred n)) hpejf) hpjf))) (Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Bool (ltNat(Nat.succ(j))(x)) Bool.true) (Nat.succ (pred n)) n (Eq.symm.{1} Nat n (Nat.succ (pred n)) (ltNat_pos(n)(i)(hli))) (trich j (pred n) (Eq.trans.{1} Bool (eqNat(j)(pred(n))) (eqNat(pred(n))(j)) Bool.false (eqNat_comm j (pred n)) hpejf) hpjf))))
                                              (tsubstVar_gt (pred n) i (tsubst(U)(j)(S)) (ne_of_lt (pred n) i (le_lt_trans i j (pred n) hij (trich j (pred n) (Eq.trans.{1} Bool (eqNat(j)(pred(n))) (eqNat(pred(n))(j)) Bool.false (eqNat_comm j (pred n)) hpejf) hpjf))) (le_lt_trans i j (pred n) hij (trich j (pred n) (Eq.trans.{1} Bool (eqNat(j)(pred(n))) (eqNat(pred(n))(j)) Bool.false (eqNat_comm j (pred n)) hpejf) hpjf)))))
                                }
                          }
                      | Or2.inr(hlif) =>
                          -- n < i.  LHS = tvar n;  RHS = tvar n.
                          Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(i)(U))(j)(S)) (FTy.tvar n) (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S)))
                            (Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(i)(U))(j)(S)) (tsubst(FTy.tvar(n))(j)(S)) (FTy.tvar n)
                               (tsubst1_cong (tsubst(FTy.tvar(n))(i)(U)) (FTy.tvar n) j S (tsubstVar_lt n i U hei hlif))
                               (tsubstVar_lt n j S (Eq.trans.{1} Bool (eqNat(n)(j)) (eqNat(j)(n)) Bool.false (eqNat_comm n j) (ne_of_lt j n (lt_le_trans i n j (trich n i hei hlif) hij))) (le_not_lt n j (lt_imp_le n j (lt_le_trans i n j (trich n i hei hlif) hij)))))
                            (Eq.symm.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (FTy.tvar n)
                               (Eq.trans.{1} FTy (tsubst(tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i)))(i)(tsubst(U)(j)(S))) (tsubst(FTy.tvar(n))(i)(tsubst(U)(j)(S))) (FTy.tvar n)
                                  (tsubst1_cong (tsubst(FTy.tvar(n))(Nat.succ(j))(tshift(S)(i))) (FTy.tvar n) i (tsubst(U)(j)(S)) (tsubstVar_lt n (Nat.succ j) (tshift(S)(i)) (Eq.trans.{1} Bool (eqNat(n)(Nat.succ(j))) (eqNat(Nat.succ(j))(n)) Bool.false (eqNat_comm n (Nat.succ j)) (ne_of_lt (Nat.succ j) n (lt_succ_weaken n j (lt_le_trans i n j (trich n i hei hlif) hij)))) (le_not_lt n (Nat.succ j) (lt_imp_le n (Nat.succ j) (lt_succ_weaken n j (lt_le_trans i n j (trich n i hei hlif) hij))))))
                                  (tsubstVar_lt n i (tsubst(U)(j)(S)) hei hlif)))
                    }
              }
        }
    }
"#;

/// **Context operations + lookup weakening/inversion** — the structural plumbing the
/// substitution lemmas need: inserting a binding (`insertCtxF`), shifting/substituting the
/// types in a context (`shiftCtxAt`/`tysubstCtx`), and the `FLookup` weakening + inversion
/// lemmas (ported from the STLC's parallel-substitution development, adapted to System F's
/// two-sorted de Bruijn contexts).
pub const SF_CTXOPS: &str = r#"
    -- ===== Index + context operations =====
    -- de Bruijn index weakening (insert a slot at position k): n < k stays, else +1.
    -- Phrased so that shiftIdx(succ k)(succ n) ≡ succ(shiftIdx k n) holds DEFINITIONALLY.
    fn shiftIdx(k: Nat) -> (Nat -> Nat) {
        match k {
          | Nat.zero    => fun (n : Nat) => Nat.succ(n)
          | Nat.succ(k2) => fun (n : Nat) =>
              match n { | Nat.zero => Nat.zero | Nat.succ(n2) => Nat.succ(shiftIdx(k2)(n2)) }
        }
    }
    -- Insert a term-variable binding of type B at de Bruijn position k.
    fn insertCtxF(k: Nat) -> (FTy -> FCtx -> FCtx) {
        match k {
          | Nat.zero    => fun (B : FTy) (G : FCtx) => FCtx.cons(B, G)
          | Nat.succ(k2) => fun (B : FTy) (G : FCtx) =>
              match G { | FCtx.nil => FCtx.cons(B, FCtx.nil) | FCtx.cons(T, G2) => FCtx.cons(T, insertCtxF(k2)(B)(G2)) }
        }
    }
    -- Shift every type in the context at cutoff c (generalised `shiftCtx`).
    fn shiftCtxAt(G: FCtx) -> (Nat -> FCtx) {
        match G {
          | FCtx.nil => fun (c : Nat) => FCtx.nil
          | FCtx.cons(t, rest) => fun (c : Nat) => FCtx.cons(tshift(t)(c), shiftCtxAt(rest)(c))
        }
    }
    -- Substitute S for type-variable j in every type in the context.
    fn tysubstCtx(G: FCtx) -> (Nat -> (FTy -> FCtx)) {
        match G {
          | FCtx.nil => fun (j : Nat) (S : FTy) => FCtx.nil
          | FCtx.cons(t, rest) => fun (j : Nat) (S : FTy) => FCtx.cons(tsubst(t)(j)(S), tysubstCtx(rest)(j)(S))
        }
    }
    -- Bump a term variable's index by one (used as a congruence for index arithmetic).
    fn bumpVar(e: FExp) -> FExp {
        match e { | FExp.evar(k) => FExp.evar(Nat.succ k) | FExp.enat(n) => e | FExp.elam(A, b) => e | FExp.eapp(f, a) => e | FExp.etlam(b) => e | FExp.etapp(f, T) => e }
    }

    -- ===== Congruences + no-confusion =====
    def fcons_cong (t : FTy) (t2 : FTy) (G : FCtx) (G2 : FCtx) (ht : Eq.{1} FTy t t2) (hG : Eq.{1} FCtx G G2)
        : Eq.{1} FCtx (FCtx.cons t G) (FCtx.cons t2 G2) :=
      Eq.subst.{1} FCtx (fun (x : FCtx) => Eq.{1} FCtx (FCtx.cons t G) (FCtx.cons t2 x)) G G2 hG
        (Eq.subst.{1} FTy (fun (x : FTy) => Eq.{1} FCtx (FCtx.cons t G) (FCtx.cons x G)) t t2 ht
          (Eq.refl.{1} FCtx (FCtx.cons t G)))
    def isZeroPF (n : Nat) : Prop := Nat.rec.{1} (fun (_ : Nat) => Prop) True (fun (_ : Nat) (_ : Prop) => False) n
    def succ_ne_zero (n : Nat) (h : Eq.{1} Nat (Nat.succ n) Nat.zero) : False :=
      Eq.subst.{1} Nat isZeroPF Nat.zero (Nat.succ n) (Eq.symm.{1} Nat (Nat.succ n) Nat.zero h) True.intro
    def succ_inj (n : Nat) (m : Nat) (h : Eq.{1} Nat (Nat.succ n) (Nat.succ m)) : Eq.{1} Nat n m :=
      Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} Nat n (pred x)) (Nat.succ n) (Nat.succ m) h (Eq.refl.{1} Nat n)
    def fheadTy (G : FCtx) : FTy := FCtx.rec.{1} (fun (_ : FCtx) => FTy) FTy.tnat (fun (T : FTy) (G2 : FCtx) (_ : FTy) => T) G
    def ftailCtx (G : FCtx) : FCtx := FCtx.rec.{1} (fun (_ : FCtx) => FCtx) FCtx.nil (fun (T : FTy) (G2 : FCtx) (_ : FCtx) => G2) G
    def fcons_inj_head (X : FTy) (Y : FCtx) (X2 : FTy) (Y2 : FCtx) (h : Eq.{1} FCtx (FCtx.cons X Y) (FCtx.cons X2 Y2)) : Eq.{1} FTy X X2 :=
      Eq.subst.{1} FCtx (fun (G : FCtx) => Eq.{1} FTy X (fheadTy G)) (FCtx.cons X Y) (FCtx.cons X2 Y2) h (Eq.refl.{1} FTy X)
    def fcons_inj_tail (X : FTy) (Y : FCtx) (X2 : FTy) (Y2 : FCtx) (h : Eq.{1} FCtx (FCtx.cons X Y) (FCtx.cons X2 Y2)) : Eq.{1} FCtx Y Y2 :=
      Eq.subst.{1} FCtx (fun (G : FCtx) => Eq.{1} FCtx Y (ftailCtx G)) (FCtx.cons X Y) (FCtx.cons X2 Y2) h (Eq.refl.{1} FCtx Y)

    -- eshiftTm on a variable agrees with shiftIdx-inside-evar (reconciles the `ltNat`-match
    -- form of `eshiftTm` with the structurally-recursive `shiftIdx`).
    fn eshiftTm_var(c: Nat) -> ((n : Nat) -> Eq.{1} FExp (eshiftTm(FExp.evar n)(c)) (FExp.evar (shiftIdx(c)(n)))) {
        match c {
          | Nat.zero => fun (n : Nat) =>
              Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FExp (match b { | Bool.true => FExp.evar n | Bool.false => FExp.evar(Nat.succ n) }) (FExp.evar(Nat.succ n)))
                Bool.false (ltNat(n)(Nat.zero)) (Eq.symm.{1} Bool (ltNat(n)(Nat.zero)) Bool.false (ltNat_n_0 n))
                (Eq.refl.{1} FExp (FExp.evar(Nat.succ n)))
          | Nat.succ(c2) => fun (n : Nat) =>
              match n {
                | Nat.zero => Eq.refl.{1} FExp (FExp.evar Nat.zero)
                | Nat.succ(n2) =>
                    match bcases (ltNat(n2)(c2)) {
                      | Or2.inl(ht) =>
                          Eq.subst.{1} Bool
                            (fun (b : Bool) => Eq.{1} FExp (match b { | Bool.true => FExp.evar(Nat.succ n2) | Bool.false => FExp.evar(Nat.succ(Nat.succ n2)) }) (FExp.evar(Nat.succ(shiftIdx(c2)(n2)))))
                            Bool.true (ltNat(n2)(c2)) (Eq.symm.{1} Bool (ltNat(n2)(c2)) Bool.true ht)
                            (eproj_inj bumpVar (FExp.evar n2) (FExp.evar(shiftIdx(c2)(n2)))
                              (Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FExp (match b { | Bool.true => FExp.evar n2 | Bool.false => FExp.evar(Nat.succ n2) }) (FExp.evar(shiftIdx(c2)(n2))))
                                (ltNat(n2)(c2)) Bool.true ht (eshiftTm_var(c2)(n2))))
                      | Or2.inr(hf) =>
                          Eq.subst.{1} Bool
                            (fun (b : Bool) => Eq.{1} FExp (match b { | Bool.true => FExp.evar(Nat.succ n2) | Bool.false => FExp.evar(Nat.succ(Nat.succ n2)) }) (FExp.evar(Nat.succ(shiftIdx(c2)(n2)))))
                            Bool.false (ltNat(n2)(c2)) (Eq.symm.{1} Bool (ltNat(n2)(c2)) Bool.false hf)
                            (eproj_inj bumpVar (FExp.evar(Nat.succ n2)) (FExp.evar(shiftIdx(c2)(n2)))
                              (Eq.subst.{1} Bool (fun (b : Bool) => Eq.{1} FExp (match b { | Bool.true => FExp.evar n2 | Bool.false => FExp.evar(Nat.succ n2) }) (FExp.evar(shiftIdx(c2)(n2))))
                                (ltNat(n2)(c2)) Bool.false hf (eshiftTm_var(c2)(n2))))
                    }
              }
        }
    }

    -- ===== FLookup weakening + inversions =====
    -- Inserting a binding shifts every existing lookup index by `shiftIdx`.
    fn flookup_weaken(G: FCtx, n: Nat, T: FTy, lk: FLookup G n T)
      -> ((c : Nat) -> (C : FTy) -> FLookup (insertCtxF(c)(C)(G)) (shiftIdx(c)(n)) T) {
        match lk {
          | FLookup.here(G0, T0) => fun (c : Nat) (C : FTy) =>
              match c {
                | Nat.zero    => FLookup.there (FCtx.cons T0 G0) Nat.zero T0 C (FLookup.here G0 T0)
                | Nat.succ(c2) => FLookup.here (insertCtxF(c2)(C)(G0)) T0
              }
          | FLookup.there(G0, n0, T0, U0, lk0) => fun (c : Nat) (C : FTy) =>
              match c {
                | Nat.zero    => FLookup.there (FCtx.cons U0 G0) (Nat.succ n0) T0 C (FLookup.there G0 n0 T0 U0 lk0)
                | Nat.succ(c2) => FLookup.there (insertCtxF(c2)(C)(G0)) (shiftIdx(c2)(n0)) T0 U0 (lk0.rec c2 C)
              }
        }
    }
    -- A lookup over `nil` is impossible.
    fn isNil(G: FCtx) -> Bool { match G { | FCtx.nil => Bool.true | FCtx.cons(t, rest) => Bool.false } }
    fn flookup_nil_absurd(G: FCtx, n: Nat, T: FTy, lk: FLookup G n T)
      -> (Eq.{1} Bool (isNil(G)) Bool.true -> False) {
        match lk {
          | FLookup.here(G0, T0) => fun (h : Eq.{1} Bool (isNil(FCtx.cons T0 G0)) Bool.true) => ff_ne_tt h
          | FLookup.there(G0, n0, T0, U0, lk0) => fun (h : Eq.{1} Bool (isNil(FCtx.cons U0 G0)) Bool.true) => ff_ne_tt h
        }
    }
    -- Lookup inversions at concrete indices (cf. the STLC lookup_zero_inv/succ_inv).
    fn flookup_zero_inv(Gc: FCtx, n: Nat, U: FTy, lk: FLookup Gc n U)
      -> ((A : FTy) -> (G0 : FCtx) -> Eq.{1} FCtx Gc (FCtx.cons A G0) -> Eq.{1} Nat n Nat.zero -> Eq.{1} FTy U A) {
        match lk {
          | FLookup.here(G00, T0) => fun (A : FTy) (G0 : FCtx) (hG : Eq.{1} FCtx (FCtx.cons T0 G00) (FCtx.cons A G0)) (hn : Eq.{1} Nat Nat.zero Nat.zero) =>
              fcons_inj_head T0 G00 A G0 hG
          | FLookup.there(G00, n0, T0, U0, lk0) => fun (A : FTy) (G0 : FCtx) (hG : Eq.{1} FCtx (FCtx.cons U0 G00) (FCtx.cons A G0)) (hn : Eq.{1} Nat (Nat.succ n0) Nat.zero) =>
              False.rec.{0} (fun (_ : False) => Eq.{1} FTy T0 A) (succ_ne_zero n0 hn)
        }
    }
    fn flookup_succ_inv(Gc: FCtx, n: Nat, U: FTy, lk: FLookup Gc n U)
      -> ((A : FTy) -> (G0 : FCtx) -> (m : Nat) -> Eq.{1} FCtx Gc (FCtx.cons A G0) -> Eq.{1} Nat n (Nat.succ m) -> FLookup G0 m U) {
        match lk {
          | FLookup.here(G00, T0) => fun (A : FTy) (G0 : FCtx) (m : Nat) (hG : Eq.{1} FCtx (FCtx.cons T0 G00) (FCtx.cons A G0)) (hn : Eq.{1} Nat Nat.zero (Nat.succ m)) =>
              False.rec.{0} (fun (_ : False) => FLookup G0 m T0) (succ_ne_zero m (Eq.symm.{1} Nat Nat.zero (Nat.succ m) hn))
          | FLookup.there(G00, n0, T0, U0, lk0) => fun (A : FTy) (G0 : FCtx) (m : Nat) (hG : Eq.{1} FCtx (FCtx.cons U0 G00) (FCtx.cons A G0)) (hn : Eq.{1} Nat (Nat.succ n0) (Nat.succ m)) =>
              Eq.subst.{1} Nat (fun (x : Nat) => FLookup G0 x T0) n0 m (succ_inj n0 m hn)
                (Eq.subst.{1} FCtx (fun (g : FCtx) => FLookup g n0 T0) G00 G0 (fcons_inj_tail U0 G00 A G0 hG) lk0)
        }
    }
"#;

/// **Context-level commutation lemmas + `FLookup` type-shift/subst + shiftCtx inversion.**
/// Lifts the de Bruijn commutation lemmas (`tshift_exchange`/`subst_shift_comm`/`tcancel`)
/// from single types to whole contexts, and proves how `FLookup` interacts with shifting and
/// substituting the context's types — the facts the type-weakening / type-substitution
/// preservation lemmas need.
pub const SF_CTXCOMM: &str = r#"
    -- shiftCtx is shiftCtxAt at cutoff 0.
    fn shiftCtxAt0_eq(G: FCtx) -> Eq.{1} FCtx (shiftCtxAt(G)(Nat.zero)) (shiftCtx(G)) {
        match G {
          | FCtx.nil => Eq.refl.{1} FCtx FCtx.nil
          | FCtx.cons(t, rest) =>
              fcons_cong (tshift(t)(Nat.zero)) (tshift(t)(Nat.zero)) (shiftCtxAt(rest)(Nat.zero)) (shiftCtx(rest))
                (Eq.refl.{1} FTy (tshift(t)(Nat.zero))) (shiftCtxAt0_eq(rest))
        }
    }
    -- Context-level shift/shift exchange (for the fttlam arm of type-weakening).
    fn shiftCtx_at_comm(G: FCtx) -> ((c : Nat) -> Eq.{1} FCtx (shiftCtxAt(shiftCtx(G))(Nat.succ c)) (shiftCtx(shiftCtxAt(G)(c)))) {
        match G {
          | FCtx.nil => fun (c : Nat) => Eq.refl.{1} FCtx FCtx.nil
          | FCtx.cons(t, rest) => fun (c : Nat) =>
              fcons_cong (tshift(tshift(t)(Nat.zero))(Nat.succ c)) (tshift(tshift(t)(c))(Nat.zero)) (shiftCtxAt(shiftCtx(rest))(Nat.succ c)) (shiftCtx(shiftCtxAt(rest)(c)))
                (Eq.symm.{1} FTy (tshift(tshift(t)(c))(Nat.zero)) (tshift(tshift(t)(Nat.zero))(Nat.succ c)) (tshift_exchange(t)(c)(Nat.zero)(Eq.refl.{1} Bool Bool.true)))
                (shiftCtx_at_comm(rest)(c))
        }
    }
    -- Context-level subst/shift commute (for the fttlam arm of type-substitution).
    fn tysubstCtx_shiftCtx_comm(G: FCtx) -> ((j : Nat) -> (S : FTy) -> Eq.{1} FCtx (tysubstCtx(shiftCtx(G))(Nat.succ j)(tshift(S)(Nat.zero))) (shiftCtx(tysubstCtx(G)(j)(S)))) {
        match G {
          | FCtx.nil => fun (j : Nat) (S : FTy) => Eq.refl.{1} FCtx FCtx.nil
          | FCtx.cons(t, rest) => fun (j : Nat) (S : FTy) =>
              fcons_cong (tsubst(tshift(t)(Nat.zero))(Nat.succ j)(tshift(S)(Nat.zero))) (tshift(tsubst(t)(j)(S))(Nat.zero)) (tysubstCtx(shiftCtx(rest))(Nat.succ j)(tshift(S)(Nat.zero))) (shiftCtx(tysubstCtx(rest)(j)(S)))
                (subst_shift_comm(t)(j)(S)(Nat.zero)(Eq.refl.{1} Bool Bool.true))
                (tysubstCtx_shiftCtx_comm(rest)(j)(S))
        }
    }
    -- Substituting at 0 into a freshly-shifted context is the identity (for type-β).
    fn tysubstCtx_shiftCtx_cancel(G: FCtx) -> ((S : FTy) -> Eq.{1} FCtx (tysubstCtx(shiftCtx(G))(Nat.zero)(S)) G) {
        match G {
          | FCtx.nil => fun (S : FTy) => Eq.refl.{1} FCtx FCtx.nil
          | FCtx.cons(t, rest) => fun (S : FTy) =>
              fcons_cong (tsubst(tshift(t)(Nat.zero))(Nat.zero)(S)) t (tysubstCtx(shiftCtx(rest))(Nat.zero)(S)) rest
                (tcancel(t)(Nat.zero)(S)) (tysubstCtx_shiftCtx_cancel(rest)(S))
        }
    }
    -- Inserting a (shifted) binding commutes with shifting the whole context.
    fn insertCtxF_shiftCtx_comm(c: Nat) -> ((C : FTy) -> (G : FCtx) -> Eq.{1} FCtx (insertCtxF(c)(tshift(C)(Nat.zero))(shiftCtx(G))) (shiftCtx(insertCtxF(c)(C)(G)))) {
        match c {
          | Nat.zero => fun (C : FTy) (G : FCtx) => Eq.refl.{1} FCtx (FCtx.cons (tshift(C)(Nat.zero)) (shiftCtx(G)))
          | Nat.succ(c2) => fun (C : FTy) (G : FCtx) =>
              match G {
                | FCtx.nil => Eq.refl.{1} FCtx (FCtx.cons (tshift(C)(Nat.zero)) FCtx.nil)
                | FCtx.cons(t, rest) =>
                    fcons_cong (tshift(t)(Nat.zero)) (tshift(t)(Nat.zero)) (insertCtxF(c2)(tshift(C)(Nat.zero))(shiftCtx(rest))) (shiftCtx(insertCtxF(c2)(C)(rest)))
                      (Eq.refl.{1} FTy (tshift(t)(Nat.zero))) (insertCtxF_shiftCtx_comm(c2)(C)(rest))
              }
        }
    }

    -- ===== FLookup vs. type-shift / type-subst on the context =====
    fn flookup_tyshift(G: FCtx, n: Nat, T: FTy, lk: FLookup G n T)
      -> ((c : Nat) -> FLookup (shiftCtxAt(G)(c)) n (tshift(T)(c))) {
        match lk {
          | FLookup.here(G0, T0) => fun (c : Nat) => FLookup.here (shiftCtxAt(G0)(c)) (tshift(T0)(c))
          | FLookup.there(G0, n0, T0, U0, lk0) => fun (c : Nat) =>
              FLookup.there (shiftCtxAt(G0)(c)) n0 (tshift(T0)(c)) (tshift(U0)(c)) (lk0.rec c)
        }
    }
    fn flookup_tysubst(G: FCtx, n: Nat, T: FTy, lk: FLookup G n T)
      -> ((j : Nat) -> (S : FTy) -> FLookup (tysubstCtx(G)(j)(S)) n (tsubst(T)(j)(S))) {
        match lk {
          | FLookup.here(G0, T0) => fun (j : Nat) (S : FTy) => FLookup.here (tysubstCtx(G0)(j)(S)) (tsubst(T0)(j)(S))
          | FLookup.there(G0, n0, T0, U0, lk0) => fun (j : Nat) (S : FTy) =>
              FLookup.there (tysubstCtx(G0)(j)(S)) n0 (tsubst(T0)(j)(S)) (tsubst(U0)(j)(S)) (lk0.rec j S)
        }
    }
    -- Inverting a lookup through a freshly type-shifted context: the looked-up type is some
    -- original type shifted, and the original lookup holds.
    fn flookup_shiftCtx_inv(G: FCtx)
      -> ((n : Nat) -> (U : FTy) -> FLookup (shiftCtx(G)) n U
            -> ExTy (fun (T0 : FTy) => And2 (Eq.{1} FTy U (tshift(T0)(Nat.zero))) (FLookup G n T0))) {
        match G {
          | FCtx.nil => fun (n : Nat) (U : FTy) (lk : FLookup FCtx.nil n U) =>
              False.rec.{0} (fun (_ : False) => ExTy (fun (T0 : FTy) => And2 (Eq.{1} FTy U (tshift(T0)(Nat.zero))) (FLookup FCtx.nil n T0)))
                (flookup_nil_absurd FCtx.nil n U lk (Eq.refl.{1} Bool Bool.true))
          | FCtx.cons(t, rest) => fun (n : Nat) (U : FTy) =>
              match n {
                | Nat.zero => fun (lk : FLookup (FCtx.cons (tshift(t)(Nat.zero)) (shiftCtx(rest))) Nat.zero U) =>
                    ExTy.mk (fun (T0 : FTy) => And2 (Eq.{1} FTy U (tshift(T0)(Nat.zero))) (FLookup (FCtx.cons t rest) Nat.zero T0)) t
                      (And2.mk (Eq.{1} FTy U (tshift(t)(Nat.zero))) (FLookup (FCtx.cons t rest) Nat.zero t)
                        (flookup_zero_inv (FCtx.cons (tshift(t)(Nat.zero)) (shiftCtx(rest))) Nat.zero U lk (tshift(t)(Nat.zero)) (shiftCtx(rest)) (Eq.refl.{1} FCtx (FCtx.cons (tshift(t)(Nat.zero)) (shiftCtx(rest)))) (Eq.refl.{1} Nat Nat.zero))
                        (FLookup.here rest t))
                | Nat.succ(m) => fun (lk : FLookup (FCtx.cons (tshift(t)(Nat.zero)) (shiftCtx(rest))) (Nat.succ m) U) =>
                    match flookup_shiftCtx_inv(rest)(m)(U)
                            (flookup_succ_inv (FCtx.cons (tshift(t)(Nat.zero)) (shiftCtx(rest))) (Nat.succ m) U lk (tshift(t)(Nat.zero)) (shiftCtx(rest)) m (Eq.refl.{1} FCtx (FCtx.cons (tshift(t)(Nat.zero)) (shiftCtx(rest)))) (Eq.refl.{1} Nat (Nat.succ m))) {
                      | ExTy.mk(T0, And2.mk(eqU, lk0)) =>
                          ExTy.mk (fun (T0b : FTy) => And2 (Eq.{1} FTy U (tshift(T0b)(Nat.zero))) (FLookup (FCtx.cons t rest) (Nat.succ m) T0b)) T0
                            (And2.mk (Eq.{1} FTy U (tshift(T0)(Nat.zero))) (FLookup (FCtx.cons t rest) (Nat.succ m) T0)
                              eqU (FLookup.there rest m T0 t lk0))
                    }
              }
        }
    }
"#;

/// **Weakening theorems.** Term weakening (`FHasTy_tmweaken`: inserting a term binding
/// anywhere preserves typing, with the term shifted) and type weakening (`FHasTy_tyweaken`:
/// inserting a fresh type variable shifts the context's types, the term's annotations, and
/// the result type together). Both by 6-arm induction on the `FHasTy` derivation; the type
/// binder (`fttlam`) and type application (`fttapp`) arms discharge via the context-level
/// commutation lemmas and `shift_subst_comm`.
pub const SF_WEAKEN: &str = r#"
    fn FHasTy_tmweaken(G: FCtx, e: FExp, T: FTy, d: FHasTy G e T)
      -> ((c : Nat) -> (C : FTy) -> FHasTy (insertCtxF(c)(C)(G)) (eshiftTm(e)(c)) T) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (c : Nat) (C : FTy) =>
              Eq.subst.{1} FExp (fun (x : FExp) => FHasTy (insertCtxF(c)(C)(G2)) x T2)
                (FExp.evar (shiftIdx(c)(n2))) (eshiftTm(FExp.evar n2)(c))
                (Eq.symm.{1} FExp (eshiftTm(FExp.evar n2)(c)) (FExp.evar (shiftIdx(c)(n2))) (eshiftTm_var(c)(n2)))
                (FHasTy.ftvar (insertCtxF(c)(C)(G2)) (shiftIdx(c)(n2)) T2 (flookup_weaken G2 n2 T2 lk2 c C))
          | FHasTy.ftnat(G2, n2) => fun (c : Nat) (C : FTy) =>
              FHasTy.ftnat (insertCtxF(c)(C)(G2)) n2
          | FHasTy.ftlam(G2, A2, b2, B2, dbody) => fun (c : Nat) (C : FTy) =>
              FHasTy.ftlam (insertCtxF(c)(C)(G2)) A2 (eshiftTm(b2)(Nat.succ c)) B2 (dbody.rec (Nat.succ c) C)
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (c : Nat) (C : FTy) =>
              FHasTy.ftapp (insertCtxF(c)(C)(G2)) (eshiftTm(f2)(c)) (eshiftTm(a2)(c)) A2 B2 (df.rec c C) (da.rec c C)
          | FHasTy.fttlam(G2, b2, B2, dbody) => fun (c : Nat) (C : FTy) =>
              FHasTy.fttlam (insertCtxF(c)(C)(G2)) (eshiftTm(b2)(c)) B2
                (Eq.subst.{1} FCtx (fun (g : FCtx) => FHasTy g (eshiftTm(b2)(c)) B2)
                   (insertCtxF(c)(tshift(C)(Nat.zero))(shiftCtx(G2))) (shiftCtx(insertCtxF(c)(C)(G2)))
                   (insertCtxF_shiftCtx_comm(c)(C)(G2))
                   (dbody.rec c (tshift(C)(Nat.zero))))
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (c : Nat) (C : FTy) =>
              FHasTy.fttapp (insertCtxF(c)(C)(G2)) (eshiftTm(f2)(c)) B2 T2 (df.rec c C)
        }
    }

    fn FHasTy_tyweaken(G: FCtx, e: FExp, T: FTy, d: FHasTy G e T)
      -> ((c : Nat) -> FHasTy (shiftCtxAt(G)(c)) (eshiftTy(e)(c)) (tshift(T)(c))) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (c : Nat) =>
              FHasTy.ftvar (shiftCtxAt(G2)(c)) n2 (tshift(T2)(c)) (flookup_tyshift G2 n2 T2 lk2 c)
          | FHasTy.ftnat(G2, n2) => fun (c : Nat) =>
              FHasTy.ftnat (shiftCtxAt(G2)(c)) n2
          | FHasTy.ftlam(G2, A2, b2, B2, dbody) => fun (c : Nat) =>
              FHasTy.ftlam (shiftCtxAt(G2)(c)) (tshift(A2)(c)) (eshiftTy(b2)(c)) (tshift(B2)(c)) (dbody.rec c)
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (c : Nat) =>
              FHasTy.ftapp (shiftCtxAt(G2)(c)) (eshiftTy(f2)(c)) (eshiftTy(a2)(c)) (tshift(A2)(c)) (tshift(B2)(c)) (df.rec c) (da.rec c)
          | FHasTy.fttlam(G2, b2, B2, dbody) => fun (c : Nat) =>
              FHasTy.fttlam (shiftCtxAt(G2)(c)) (eshiftTy(b2)(Nat.succ c)) (tshift(B2)(Nat.succ c))
                (Eq.subst.{1} FCtx (fun (g : FCtx) => FHasTy g (eshiftTy(b2)(Nat.succ c)) (tshift(B2)(Nat.succ c)))
                   (shiftCtxAt(shiftCtx(G2))(Nat.succ c)) (shiftCtx(shiftCtxAt(G2)(c)))
                   (shiftCtx_at_comm(G2)(c))
                   (dbody.rec (Nat.succ c)))
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (c : Nat) =>
              Eq.subst.{1} FTy (fun (x : FTy) => FHasTy (shiftCtxAt(G2)(c)) (FExp.etapp (eshiftTy(f2)(c)) (tshift(T2)(c))) x)
                (tsubst(tshift(B2)(Nat.succ c))(Nat.zero)(tshift(T2)(c))) (tshift(tsubst(B2)(Nat.zero)(T2))(c))
                (Eq.symm.{1} FTy (tshift(tsubst(B2)(Nat.zero)(T2))(c)) (tsubst(tshift(B2)(Nat.succ c))(Nat.zero)(tshift(T2)(c)))
                   (shift_subst_comm(B2)(Nat.zero)(T2)(c)(Eq.refl.{1} Bool Bool.true)))
                (FHasTy.fttapp (shiftCtxAt(G2)(c)) (eshiftTy(f2)(c)) (tshift(B2)(Nat.succ c)) (tshift(T2)(c)) (df.rec c))
        }
    }
"#;

/// **Parallel term substitution + the bridge to the recursive `esubstTm`.** Following the
/// STLC's parallel-substitution technique (a substitution is a `Nat -> FExp`), `applySub`
/// applies one, lifting under term binders (`liftSubF`) and type binders (`liftSubTyF`). The
/// bridge `subst_bridge` proves `esubstTm e j v = applySub e (atSubjF j v)`, so the
/// substitution lemma (proved cleanly over the original context for `applySub`) transfers to
/// the `esubstTm` used by the operational semantics. Its two index lemmas reconcile the
/// single-substitution assignment under a lift with a shifted assignment.
pub const SF_TSUBSTA: &str = r#"
    -- Substitution as a function; single-variable assignment is `atSubjF`.
    def atSubjF (j : Nat) (v : FExp) (n : Nat) : FExp := esubstVar(j, v, n)
    def liftSubF (s : Nat -> FExp) (n : Nat) : FExp :=
      match n { | Nat.zero => FExp.evar(Nat.zero) | Nat.succ(m) => eshiftTm(s(m))(Nat.zero) }
    def liftSubTyF (s : Nat -> FExp) (n : Nat) : FExp := eshiftTy(s(n))(Nat.zero)
    fn applySub(e: FExp) -> ((Nat -> FExp) -> FExp) {
        match e {
          | FExp.evar(n)     => fun (s : Nat -> FExp) => s(n)
          | FExp.enat(n)     => fun (s : Nat -> FExp) => FExp.enat(n)
          | FExp.elam(A, b)  => fun (s : Nat -> FExp) => FExp.elam(A, applySub(b)(liftSubF(s)))
          | FExp.eapp(f, a)  => fun (s : Nat -> FExp) => FExp.eapp(applySub(f)(s), applySub(a)(s))
          | FExp.etlam(b)    => fun (s : Nat -> FExp) => FExp.etlam(applySub(b)(liftSubTyF(s)))
          | FExp.etapp(f, T) => fun (s : Nat -> FExp) => FExp.etapp(applySub(f)(s), T)
        }
    }

    -- Congruences.
    def evar_cong (a : Nat) (b : Nat) (h : Eq.{1} Nat a b) : Eq.{1} FExp (FExp.evar a) (FExp.evar b) :=
      Eq.subst.{1} Nat (fun (x : Nat) => Eq.{1} FExp (FExp.evar a) (FExp.evar x)) a b h (Eq.refl.{1} FExp (FExp.evar a))
    def elam_cong (A : FTy) (b : FExp) (b2 : FExp) (h : Eq.{1} FExp b b2) : Eq.{1} FExp (FExp.elam A b) (FExp.elam A b2) :=
      Eq.subst.{1} FExp (fun (x : FExp) => Eq.{1} FExp (FExp.elam A b) (FExp.elam A x)) b b2 h (Eq.refl.{1} FExp (FExp.elam A b))
    def etlam_cong (b : FExp) (b2 : FExp) (h : Eq.{1} FExp b b2) : Eq.{1} FExp (FExp.etlam b) (FExp.etlam b2) :=
      Eq.subst.{1} FExp (fun (x : FExp) => Eq.{1} FExp (FExp.etlam b) (FExp.etlam x)) b b2 h (Eq.refl.{1} FExp (FExp.etlam b))
    def etapp_cong (f : FExp) (f2 : FExp) (T : FTy) (h : Eq.{1} FExp f f2) : Eq.{1} FExp (FExp.etapp f T) (FExp.etapp f2 T) :=
      Eq.subst.{1} FExp (fun (x : FExp) => Eq.{1} FExp (FExp.etapp f T) (FExp.etapp x T)) f f2 h (Eq.refl.{1} FExp (FExp.etapp f T))
    def eapp_cong (f : FExp) (f2 : FExp) (a : FExp) (a2 : FExp) (hf : Eq.{1} FExp f f2) (ha : Eq.{1} FExp a a2) : Eq.{1} FExp (FExp.eapp f a) (FExp.eapp f2 a2) :=
      Eq.subst.{1} FExp (fun (x : FExp) => Eq.{1} FExp (FExp.eapp f a) (FExp.eapp f2 x)) a a2 ha
        (Eq.subst.{1} FExp (fun (x : FExp) => Eq.{1} FExp (FExp.eapp f a) (FExp.eapp x a)) f f2 hf (Eq.refl.{1} FExp (FExp.eapp f a)))
    def eshiftTm_cong (a : FExp) (b : FExp) (c : Nat) (h : Eq.{1} FExp a b) : Eq.{1} FExp (eshiftTm(a)(c)) (eshiftTm(b)(c)) :=
      Eq.subst.{1} FExp (fun (x : FExp) => Eq.{1} FExp (eshiftTm(a)(c)) (eshiftTm(x)(c))) a b h (Eq.refl.{1} FExp (eshiftTm(a)(c)))
    def eshiftTy_cong (a : FExp) (b : FExp) (c : Nat) (h : Eq.{1} FExp a b) : Eq.{1} FExp (eshiftTy(a)(c)) (eshiftTy(b)(c)) :=
      Eq.subst.{1} FExp (fun (x : FExp) => Eq.{1} FExp (eshiftTy(a)(c)) (eshiftTy(x)(c))) a b h (Eq.refl.{1} FExp (eshiftTy(a)(c)))

    -- Generic Bool-match reducers (to fold the `esubstVar` case analysis cleanly).
    def boolMatchFE (b : Bool) (X : FExp) (Y : FExp) : FExp := match b { | Bool.true => X | Bool.false => Y }
    def boolMatch_true (X : FExp) (Y : FExp) (Z : FExp) (b : Bool) (hb : Eq.{1} Bool b Bool.true) (hXZ : Eq.{1} FExp X Z) : Eq.{1} FExp (boolMatchFE b X Y) Z :=
      Eq.subst.{1} Bool (fun (x : Bool) => Eq.{1} FExp (boolMatchFE x X Y) Z) Bool.true b (Eq.symm.{1} Bool b Bool.true hb) hXZ
    def boolMatch_false (X : FExp) (Y : FExp) (Z : FExp) (b : Bool) (hb : Eq.{1} Bool b Bool.false) (hYZ : Eq.{1} FExp Y Z) : Eq.{1} FExp (boolMatchFE b X Y) Z :=
      Eq.subst.{1} Bool (fun (x : Bool) => Eq.{1} FExp (boolMatchFE x X Y) Z) Bool.false b (Eq.symm.{1} Bool b Bool.false hb) hYZ

    -- applySub respects pointwise-equal substitutions (congruence; no funext needed).
    fn applySub_ext(e: FExp)
      -> ((s1 : Nat -> FExp) -> (s2 : Nat -> FExp) -> ((n : Nat) -> Eq.{1} FExp (s1 n) (s2 n))
            -> Eq.{1} FExp (applySub(e)(s1)) (applySub(e)(s2))) {
        match e {
          | FExp.evar(n) => fun (s1 : Nat -> FExp) (s2 : Nat -> FExp) (pw : (n : Nat) -> Eq.{1} FExp (s1 n) (s2 n)) => pw n
          | FExp.enat(n) => fun (s1 : Nat -> FExp) (s2 : Nat -> FExp) (pw : (n : Nat) -> Eq.{1} FExp (s1 n) (s2 n)) => Eq.refl.{1} FExp (FExp.enat n)
          | FExp.elam(A, b) => fun (s1 : Nat -> FExp) (s2 : Nat -> FExp) (pw : (n : Nat) -> Eq.{1} FExp (s1 n) (s2 n)) =>
              elam_cong A (applySub(b)(liftSubF(s1))) (applySub(b)(liftSubF(s2)))
                (applySub_ext(b)(liftSubF(s1))(liftSubF(s2))
                  (fun (n : Nat) => match n {
                     | Nat.zero => Eq.refl.{1} FExp (FExp.evar Nat.zero)
                     | Nat.succ(m) => eshiftTm_cong (s1 m) (s2 m) Nat.zero (pw m)
                   }))
          | FExp.eapp(f, a) => fun (s1 : Nat -> FExp) (s2 : Nat -> FExp) (pw : (n : Nat) -> Eq.{1} FExp (s1 n) (s2 n)) =>
              eapp_cong (applySub(f)(s1)) (applySub(f)(s2)) (applySub(a)(s1)) (applySub(a)(s2))
                (applySub_ext(f)(s1)(s2)(pw)) (applySub_ext(a)(s1)(s2)(pw))
          | FExp.etlam(b) => fun (s1 : Nat -> FExp) (s2 : Nat -> FExp) (pw : (n : Nat) -> Eq.{1} FExp (s1 n) (s2 n)) =>
              etlam_cong (applySub(b)(liftSubTyF(s1))) (applySub(b)(liftSubTyF(s2)))
                (applySub_ext(b)(liftSubTyF(s1))(liftSubTyF(s2))
                  (fun (n : Nat) => eshiftTy_cong (s1 n) (s2 n) Nat.zero (pw n)))
          | FExp.etapp(f, T) => fun (s1 : Nat -> FExp) (s2 : Nat -> FExp) (pw : (n : Nat) -> Eq.{1} FExp (s1 n) (s2 n)) =>
              etapp_cong (applySub(f)(s1)) (applySub(f)(s2)) T (applySub_ext(f)(s1)(s2)(pw))
        }
    }

"#;

/// The index lemmas + the bridge (split out for isolation).
pub const SF_TSUBSTB: &str = r#"
    -- Index lemma (term-binder lift): atSubjF (succ j)(eshiftTm v 0) = liftSubF (atSubjF j v).
    fn esubstVar_shift_lift(j: Nat)
      -> ((v : FExp) -> (n : Nat) -> Eq.{1} FExp (esubstVar(Nat.succ j, eshiftTm(v)(Nat.zero), n)) (liftSubF(atSubjF(j)(v))(n))) {
        fun (v : FExp) (n : Nat) =>
          match n {
            | Nat.zero => Eq.refl.{1} FExp (FExp.evar Nat.zero)
            | Nat.succ(m) =>
                match bcases(eqNat(m)(j)) {
                  | Or2.inl(he) =>
                      Eq.trans.{1} FExp
                        (esubstVar(Nat.succ j, eshiftTm(v)(Nat.zero), Nat.succ m))
                        (eshiftTm(v)(Nat.zero))
                        (liftSubF(atSubjF(j)(v))(Nat.succ m))
                        (boolMatch_true (eshiftTm(v)(Nat.zero)) (boolMatchFE (ltNat(j)(m)) (FExp.evar m) (FExp.evar(Nat.succ m))) (eshiftTm(v)(Nat.zero)) (eqNat(m)(j)) he (Eq.refl.{1} FExp (eshiftTm(v)(Nat.zero))))
                        (Eq.symm.{1} FExp (liftSubF(atSubjF(j)(v))(Nat.succ m)) (eshiftTm(v)(Nat.zero))
                          (eshiftTm_cong (esubstVar(j, v, m)) v Nat.zero
                            (boolMatch_true v (boolMatchFE (ltNat(j)(m)) (FExp.evar(pred m)) (FExp.evar m)) v (eqNat(m)(j)) he (Eq.refl.{1} FExp v))))
                  | Or2.inr(he) =>
                      match bcases(ltNat(j)(m)) {
                        | Or2.inl(hl) =>
                            Eq.trans.{1} FExp
                              (esubstVar(Nat.succ j, eshiftTm(v)(Nat.zero), Nat.succ m))
                              (FExp.evar m)
                              (liftSubF(atSubjF(j)(v))(Nat.succ m))
                              (boolMatch_false (eshiftTm(v)(Nat.zero)) (boolMatchFE (ltNat(j)(m)) (FExp.evar m) (FExp.evar(Nat.succ m))) (FExp.evar m) (eqNat(m)(j)) he
                                (boolMatch_true (FExp.evar m) (FExp.evar(Nat.succ m)) (FExp.evar m) (ltNat(j)(m)) hl (Eq.refl.{1} FExp (FExp.evar m))))
                              (Eq.symm.{1} FExp (liftSubF(atSubjF(j)(v))(Nat.succ m)) (FExp.evar m)
                                (Eq.trans.{1} FExp (eshiftTm(esubstVar(j, v, m))(Nat.zero)) (eshiftTm(FExp.evar(pred m))(Nat.zero)) (FExp.evar m)
                                  (eshiftTm_cong (esubstVar(j, v, m)) (FExp.evar(pred m)) Nat.zero
                                    (boolMatch_false v (boolMatchFE (ltNat(j)(m)) (FExp.evar(pred m)) (FExp.evar m)) (FExp.evar(pred m)) (eqNat(m)(j)) he
                                      (boolMatch_true (FExp.evar(pred m)) (FExp.evar m) (FExp.evar(pred m)) (ltNat(j)(m)) hl (Eq.refl.{1} FExp (FExp.evar(pred m))))))
                                  (Eq.trans.{1} FExp (eshiftTm(FExp.evar(pred m))(Nat.zero)) (FExp.evar (Nat.succ (pred m))) (FExp.evar m)
                                    (eshiftTm_var(Nat.zero)(pred m))
                                    (evar_cong (Nat.succ (pred m)) m (Eq.symm.{1} Nat m (Nat.succ (pred m)) (ltNat_pos m j hl))))))
                        | Or2.inr(hl) =>
                            Eq.trans.{1} FExp
                              (esubstVar(Nat.succ j, eshiftTm(v)(Nat.zero), Nat.succ m))
                              (FExp.evar(Nat.succ m))
                              (liftSubF(atSubjF(j)(v))(Nat.succ m))
                              (boolMatch_false (eshiftTm(v)(Nat.zero)) (boolMatchFE (ltNat(j)(m)) (FExp.evar m) (FExp.evar(Nat.succ m))) (FExp.evar(Nat.succ m)) (eqNat(m)(j)) he
                                (boolMatch_false (FExp.evar m) (FExp.evar(Nat.succ m)) (FExp.evar(Nat.succ m)) (ltNat(j)(m)) hl (Eq.refl.{1} FExp (FExp.evar(Nat.succ m)))))
                              (Eq.symm.{1} FExp (liftSubF(atSubjF(j)(v))(Nat.succ m)) (FExp.evar(Nat.succ m))
                                (Eq.trans.{1} FExp (eshiftTm(esubstVar(j, v, m))(Nat.zero)) (eshiftTm(FExp.evar m)(Nat.zero)) (FExp.evar(Nat.succ m))
                                  (eshiftTm_cong (esubstVar(j, v, m)) (FExp.evar m) Nat.zero
                                    (boolMatch_false v (boolMatchFE (ltNat(j)(m)) (FExp.evar(pred m)) (FExp.evar m)) (FExp.evar m) (eqNat(m)(j)) he
                                      (boolMatch_false (FExp.evar(pred m)) (FExp.evar m) (FExp.evar m) (ltNat(j)(m)) hl (Eq.refl.{1} FExp (FExp.evar m)))))
                                  (eshiftTm_var(Nat.zero)(m))))
                      }
                }
          }
    }

"#;
pub const SF_TSUBSTC: &str = r#"
    -- Index lemma (type-binder lift): atSubjF j (eshiftTy v 0) = liftSubTyF (atSubjF j v).
    fn esubstVar_shiftTy_lift(j: Nat)
      -> ((v : FExp) -> (n : Nat) -> Eq.{1} FExp (esubstVar(j, eshiftTy(v)(Nat.zero), n)) (liftSubTyF(atSubjF(j)(v))(n))) {
        fun (v : FExp) (n : Nat) =>
          match bcases(eqNat(n)(j)) {
            | Or2.inl(he) =>
                Eq.trans.{1} FExp (esubstVar(j, eshiftTy(v)(Nat.zero), n)) (eshiftTy(v)(Nat.zero)) (liftSubTyF(atSubjF(j)(v))(n))
                  (boolMatch_true (eshiftTy(v)(Nat.zero)) (boolMatchFE (ltNat(j)(n)) (FExp.evar(pred n)) (FExp.evar n)) (eshiftTy(v)(Nat.zero)) (eqNat(n)(j)) he (Eq.refl.{1} FExp (eshiftTy(v)(Nat.zero))))
                  (Eq.symm.{1} FExp (liftSubTyF(atSubjF(j)(v))(n)) (eshiftTy(v)(Nat.zero))
                    (eshiftTy_cong (esubstVar(j, v, n)) v Nat.zero
                      (boolMatch_true v (boolMatchFE (ltNat(j)(n)) (FExp.evar(pred n)) (FExp.evar n)) v (eqNat(n)(j)) he (Eq.refl.{1} FExp v))))
            | Or2.inr(he) =>
                match bcases(ltNat(j)(n)) {
                  | Or2.inl(hl) =>
                      Eq.trans.{1} FExp (esubstVar(j, eshiftTy(v)(Nat.zero), n)) (FExp.evar(pred n)) (liftSubTyF(atSubjF(j)(v))(n))
                        (boolMatch_false (eshiftTy(v)(Nat.zero)) (boolMatchFE (ltNat(j)(n)) (FExp.evar(pred n)) (FExp.evar n)) (FExp.evar(pred n)) (eqNat(n)(j)) he
                          (boolMatch_true (FExp.evar(pred n)) (FExp.evar n) (FExp.evar(pred n)) (ltNat(j)(n)) hl (Eq.refl.{1} FExp (FExp.evar(pred n)))))
                        (Eq.symm.{1} FExp (liftSubTyF(atSubjF(j)(v))(n)) (FExp.evar(pred n))
                          (eshiftTy_cong (esubstVar(j, v, n)) (FExp.evar(pred n)) Nat.zero
                            (boolMatch_false v (boolMatchFE (ltNat(j)(n)) (FExp.evar(pred n)) (FExp.evar n)) (FExp.evar(pred n)) (eqNat(n)(j)) he
                              (boolMatch_true (FExp.evar(pred n)) (FExp.evar n) (FExp.evar(pred n)) (ltNat(j)(n)) hl (Eq.refl.{1} FExp (FExp.evar(pred n)))))))
                  | Or2.inr(hl) =>
                      Eq.trans.{1} FExp (esubstVar(j, eshiftTy(v)(Nat.zero), n)) (FExp.evar n) (liftSubTyF(atSubjF(j)(v))(n))
                        (boolMatch_false (eshiftTy(v)(Nat.zero)) (boolMatchFE (ltNat(j)(n)) (FExp.evar(pred n)) (FExp.evar n)) (FExp.evar n) (eqNat(n)(j)) he
                          (boolMatch_false (FExp.evar(pred n)) (FExp.evar n) (FExp.evar n) (ltNat(j)(n)) hl (Eq.refl.{1} FExp (FExp.evar n))))
                        (Eq.symm.{1} FExp (liftSubTyF(atSubjF(j)(v))(n)) (FExp.evar n)
                          (eshiftTy_cong (esubstVar(j, v, n)) (FExp.evar n) Nat.zero
                            (boolMatch_false v (boolMatchFE (ltNat(j)(n)) (FExp.evar(pred n)) (FExp.evar n)) (FExp.evar n) (eqNat(n)(j)) he
                              (boolMatch_false (FExp.evar(pred n)) (FExp.evar n) (FExp.evar n) (ltNat(j)(n)) hl (Eq.refl.{1} FExp (FExp.evar n))))))
                }
          }
    }

"#;
pub const SF_TSUBSTD: &str = r#"
    -- THE BRIDGE: the recursive single substitution equals applying the assignment `atSubjF j v`.
    fn subst_bridge(e: FExp)
      -> ((j : Nat) -> (v : FExp) -> Eq.{1} FExp (esubstTm(e)(j)(v)) (applySub(e)(atSubjF(j)(v)))) {
        match e {
          | FExp.evar(n) => fun (j : Nat) (v : FExp) => Eq.refl.{1} FExp (esubstVar(j, v, n))
          | FExp.enat(n) => fun (j : Nat) (v : FExp) => Eq.refl.{1} FExp (FExp.enat n)
          | FExp.elam(A, b) => fun (j : Nat) (v : FExp) =>
              elam_cong A (esubstTm(b)(Nat.succ j)(eshiftTm(v)(Nat.zero))) (applySub(b)(liftSubF(atSubjF(j)(v))))
                (Eq.trans.{1} FExp (esubstTm(b)(Nat.succ j)(eshiftTm(v)(Nat.zero))) (applySub(b)(atSubjF(Nat.succ j)(eshiftTm(v)(Nat.zero)))) (applySub(b)(liftSubF(atSubjF(j)(v))))
                  (subst_bridge(b)(Nat.succ j)(eshiftTm(v)(Nat.zero)))
                  (applySub_ext(b)(atSubjF(Nat.succ j)(eshiftTm(v)(Nat.zero)))(liftSubF(atSubjF(j)(v))) (esubstVar_shift_lift(j)(v))))
          | FExp.eapp(f, a) => fun (j : Nat) (v : FExp) =>
              eapp_cong (esubstTm(f)(j)(v)) (applySub(f)(atSubjF(j)(v))) (esubstTm(a)(j)(v)) (applySub(a)(atSubjF(j)(v)))
                (subst_bridge(f)(j)(v)) (subst_bridge(a)(j)(v))
          | FExp.etlam(b) => fun (j : Nat) (v : FExp) =>
              etlam_cong (esubstTm(b)(j)(eshiftTy(v)(Nat.zero))) (applySub(b)(liftSubTyF(atSubjF(j)(v))))
                (Eq.trans.{1} FExp (esubstTm(b)(j)(eshiftTy(v)(Nat.zero))) (applySub(b)(atSubjF(j)(eshiftTy(v)(Nat.zero)))) (applySub(b)(liftSubTyF(atSubjF(j)(v))))
                  (subst_bridge(b)(j)(eshiftTy(v)(Nat.zero)))
                  (applySub_ext(b)(atSubjF(j)(eshiftTy(v)(Nat.zero)))(liftSubTyF(atSubjF(j)(v))) (esubstVar_shiftTy_lift(j)(v))))
          | FExp.etapp(f, T) => fun (j : Nat) (v : FExp) =>
              etapp_cong (esubstTm(f)(j)(v)) (applySub(f)(atSubjF(j)(v))) T (subst_bridge(f)(j)(v))
        }
    }
"#;

/// **The term substitution lemma + `subst_preserves`.** A well-typed term stays well-typed
/// under any substitution mapping the context's variables to well-typed terms in a target
/// context (`subst_lemma`, proved over the original context so the variable case is trivial).
/// Term binders extend the substitution with `liftSubF` (typed by `liftSub_respects`), type
/// binders with `liftSubTyF` (typed by `liftSubTy_respects`, which crosses the type-shift via
/// `FHasTy_tyweaken`). `esubstTm_preserves` transports the single-variable instance back to
/// the operational `esubstTm` through the bridge — the β-redex case of preservation.
pub const SF_TSUBSTE: &str = r#"
    -- liftSubF preserves the "respects" relation across a term binder.
    def liftSub_respects (A : FTy) (G : FCtx) (G2 : FCtx) (s : Nat -> FExp)
        (resp : (n : Nat) -> (U : FTy) -> FLookup G n U -> FHasTy G2 (s n) U)
        (n : Nat) (U : FTy) : FLookup (FCtx.cons A G) n U -> FHasTy (FCtx.cons A G2) (liftSubF(s)(n)) U :=
      match n {
        | Nat.zero => fun (lk : FLookup (FCtx.cons A G) Nat.zero U) =>
            Eq.subst.{1} FTy (fun (x : FTy) => FHasTy (FCtx.cons A G2) (FExp.evar Nat.zero) x) A U
              (Eq.symm.{1} FTy U A (flookup_zero_inv (FCtx.cons A G) Nat.zero U lk A G (Eq.refl.{1} FCtx (FCtx.cons A G)) (Eq.refl.{1} Nat Nat.zero)))
              (FHasTy.ftvar (FCtx.cons A G2) Nat.zero A (FLookup.here G2 A))
        | Nat.succ(m) => fun (lk : FLookup (FCtx.cons A G) (Nat.succ m) U) =>
            FHasTy_tmweaken G2 (s m) U
              (resp m U (flookup_succ_inv (FCtx.cons A G) (Nat.succ m) U lk A G m (Eq.refl.{1} FCtx (FCtx.cons A G)) (Eq.refl.{1} Nat (Nat.succ m))))
              Nat.zero A
      }

    -- liftSubTyF preserves the "respects" relation across a type binder (uses type weakening).
    def liftSubTy_respects (G : FCtx) (G2 : FCtx) (s : Nat -> FExp)
        (resp : (n : Nat) -> (U : FTy) -> FLookup G n U -> FHasTy G2 (s n) U)
        (n : Nat) (U : FTy) : FLookup (shiftCtx G) n U -> FHasTy (shiftCtx G2) (liftSubTyF(s)(n)) U :=
      fun (lk : FLookup (shiftCtx G) n U) =>
        match flookup_shiftCtx_inv(G)(n)(U)(lk) {
          | ExTy.mk(T0, And2.mk(eqU, lk0)) =>
              Eq.subst.{1} FTy (fun (x : FTy) => FHasTy (shiftCtx G2) (eshiftTy(s(n))(Nat.zero)) x) (tshift(T0)(Nat.zero)) U
                (Eq.symm.{1} FTy U (tshift(T0)(Nat.zero)) eqU)
                (Eq.subst.{1} FCtx (fun (g : FCtx) => FHasTy g (eshiftTy(s(n))(Nat.zero)) (tshift(T0)(Nat.zero)))
                   (shiftCtxAt(G2)(Nat.zero)) (shiftCtx G2) (shiftCtxAt0_eq G2)
                   (FHasTy_tyweaken G2 (s(n)) T0 (resp n T0 lk0) Nat.zero))
        }

    -- THE SUBSTITUTION LEMMA (parallel form), by induction on the typing derivation.
    fn subst_lemma(G: FCtx, e: FExp, T: FTy, d: FHasTy G e T)
      -> ((G2 : FCtx) -> (s : Nat -> FExp)
            -> ((n : Nat) -> (U : FTy) -> FLookup G n U -> FHasTy G2 (s n) U)
            -> FHasTy G2 (applySub(e)(s)) T) {
        match d {
          | FHasTy.ftvar(Gv, n2, T2, lk2) => fun (G2 : FCtx) (s : Nat -> FExp) (resp : (n : Nat) -> (U : FTy) -> FLookup Gv n U -> FHasTy G2 (s n) U) =>
              resp n2 T2 lk2
          | FHasTy.ftnat(Gv, n2) => fun (G2 : FCtx) (s : Nat -> FExp) (resp : (n : Nat) -> (U : FTy) -> FLookup Gv n U -> FHasTy G2 (s n) U) =>
              FHasTy.ftnat G2 n2
          | FHasTy.ftlam(Gv, A2, b2, B2, dbody) => fun (G2 : FCtx) (s : Nat -> FExp) (resp : (n : Nat) -> (U : FTy) -> FLookup Gv n U -> FHasTy G2 (s n) U) =>
              FHasTy.ftlam G2 A2 (applySub(b2)(liftSubF(s))) B2
                (dbody.rec (FCtx.cons A2 G2) (liftSubF(s)) (liftSub_respects A2 Gv G2 s resp))
          | FHasTy.ftapp(Gv, f2, a2, A2, B2, df, da) => fun (G2 : FCtx) (s : Nat -> FExp) (resp : (n : Nat) -> (U : FTy) -> FLookup Gv n U -> FHasTy G2 (s n) U) =>
              FHasTy.ftapp G2 (applySub(f2)(s)) (applySub(a2)(s)) A2 B2 (df.rec G2 s resp) (da.rec G2 s resp)
          | FHasTy.fttlam(Gv, b2, B2, dbody) => fun (G2 : FCtx) (s : Nat -> FExp) (resp : (n : Nat) -> (U : FTy) -> FLookup Gv n U -> FHasTy G2 (s n) U) =>
              FHasTy.fttlam G2 (applySub(b2)(liftSubTyF(s))) B2
                (dbody.rec (shiftCtx G2) (liftSubTyF(s)) (liftSubTy_respects Gv G2 s resp))
          | FHasTy.fttapp(Gv, f2, B2, T2, df) => fun (G2 : FCtx) (s : Nat -> FExp) (resp : (n : Nat) -> (U : FTy) -> FLookup Gv n U -> FHasTy G2 (s n) U) =>
              FHasTy.fttapp G2 (applySub(f2)(s)) B2 T2 (df.rec G2 s resp)
        }
    }

    -- The single substitution `atSubjF 0 v` respects (cons A G) ⇝ G when v : A.
    def atSub0_respects (A : FTy) (G : FCtx) (v : FExp) (dv : FHasTy G v A)
        (n : Nat) (U : FTy) : FLookup (FCtx.cons A G) n U -> FHasTy G (atSubjF(Nat.zero)(v)(n)) U :=
      match n {
        | Nat.zero => fun (lk : FLookup (FCtx.cons A G) Nat.zero U) =>
            Eq.subst.{1} FTy (fun (x : FTy) => FHasTy G v x) A U
              (Eq.symm.{1} FTy U A (flookup_zero_inv (FCtx.cons A G) Nat.zero U lk A G (Eq.refl.{1} FCtx (FCtx.cons A G)) (Eq.refl.{1} Nat Nat.zero)))
              dv
        | Nat.succ(m) => fun (lk : FLookup (FCtx.cons A G) (Nat.succ m) U) =>
            FHasTy.ftvar G m U (flookup_succ_inv (FCtx.cons A G) (Nat.succ m) U lk A G m (Eq.refl.{1} FCtx (FCtx.cons A G)) (Eq.refl.{1} Nat (Nat.succ m)))
      }

    -- Substitution preserves typing (β case), in applySub form then bridged to esubstTm.
    def subst_preserves (A : FTy) (G : FCtx) (b : FExp) (T : FTy) (v : FExp)
        (dbody : FHasTy (FCtx.cons A G) b T) (dv : FHasTy G v A)
        : FHasTy G (applySub(b)(atSubjF(Nat.zero)(v))) T :=
      subst_lemma (FCtx.cons A G) b T dbody G (atSubjF(Nat.zero)(v)) (atSub0_respects A G v dv)
    def esubstTm_preserves (A : FTy) (G : FCtx) (b : FExp) (T : FTy) (v : FExp)
        (dbody : FHasTy (FCtx.cons A G) b T) (dv : FHasTy G v A)
        : FHasTy G (esubstTm(b)(Nat.zero)(v)) T :=
      Eq.subst.{1} FExp (fun (x : FExp) => FHasTy G x T) (applySub(b)(atSubjF(Nat.zero)(v))) (esubstTm(b)(Nat.zero)(v))
        (Eq.symm.{1} FExp (esubstTm(b)(Nat.zero)(v)) (applySub(b)(atSubjF(Nat.zero)(v))) (subst_bridge(b)(Nat.zero)(v)))
        (subst_preserves A G b T v dbody dv)
"#;

/// **The type substitution lemma + type-β preservation.** Substituting a type `S` for a
/// type variable in a well-typed term preserves typing, substituting `S` through the context
/// and result type too (`tysubst_lemma`, 6-arm induction; the `fttlam` arm uses the
/// context-level `subst_shift_comm`, the `fttapp` arm uses `subst_subst_comm`). Specialising
/// at variable 0 over a freshly-shifted context (cancelled by `tysubstCtx_shiftCtx_cancel`)
/// yields `tysubst_preserves` — the type-β redex case of preservation.
pub const SF_TYSUBST: &str = r#"
    fn tysubst_lemma(G: FCtx, e: FExp, T: FTy, d: FHasTy G e T)
      -> ((j : Nat) -> (S : FTy) -> FHasTy (tysubstCtx(G)(j)(S)) (esubstTy(e)(j)(S)) (tsubst(T)(j)(S))) {
        match d {
          | FHasTy.ftvar(G2, n2, T2, lk2) => fun (j : Nat) (S : FTy) =>
              FHasTy.ftvar (tysubstCtx(G2)(j)(S)) n2 (tsubst(T2)(j)(S)) (flookup_tysubst G2 n2 T2 lk2 j S)
          | FHasTy.ftnat(G2, n2) => fun (j : Nat) (S : FTy) =>
              FHasTy.ftnat (tysubstCtx(G2)(j)(S)) n2
          | FHasTy.ftlam(G2, A2, b2, B2, dbody) => fun (j : Nat) (S : FTy) =>
              FHasTy.ftlam (tysubstCtx(G2)(j)(S)) (tsubst(A2)(j)(S)) (esubstTy(b2)(j)(S)) (tsubst(B2)(j)(S)) (dbody.rec j S)
          | FHasTy.ftapp(G2, f2, a2, A2, B2, df, da) => fun (j : Nat) (S : FTy) =>
              FHasTy.ftapp (tysubstCtx(G2)(j)(S)) (esubstTy(f2)(j)(S)) (esubstTy(a2)(j)(S)) (tsubst(A2)(j)(S)) (tsubst(B2)(j)(S)) (df.rec j S) (da.rec j S)
          | FHasTy.fttlam(G2, b2, B2, dbody) => fun (j : Nat) (S : FTy) =>
              FHasTy.fttlam (tysubstCtx(G2)(j)(S)) (esubstTy(b2)(Nat.succ j)(tshift(S)(Nat.zero))) (tsubst(B2)(Nat.succ j)(tshift(S)(Nat.zero)))
                (Eq.subst.{1} FCtx (fun (g : FCtx) => FHasTy g (esubstTy(b2)(Nat.succ j)(tshift(S)(Nat.zero))) (tsubst(B2)(Nat.succ j)(tshift(S)(Nat.zero))))
                   (tysubstCtx(shiftCtx(G2))(Nat.succ j)(tshift(S)(Nat.zero))) (shiftCtx(tysubstCtx(G2)(j)(S)))
                   (tysubstCtx_shiftCtx_comm(G2)(j)(S))
                   (dbody.rec (Nat.succ j) (tshift(S)(Nat.zero))))
          | FHasTy.fttapp(G2, f2, B2, T2, df) => fun (j : Nat) (S : FTy) =>
              Eq.subst.{1} FTy (fun (x : FTy) => FHasTy (tysubstCtx(G2)(j)(S)) (FExp.etapp (esubstTy(f2)(j)(S)) (tsubst(T2)(j)(S))) x)
                (tsubst(tsubst(B2)(Nat.succ j)(tshift(S)(Nat.zero)))(Nat.zero)(tsubst(T2)(j)(S))) (tsubst(tsubst(B2)(Nat.zero)(T2))(j)(S))
                (Eq.symm.{1} FTy (tsubst(tsubst(B2)(Nat.zero)(T2))(j)(S)) (tsubst(tsubst(B2)(Nat.succ j)(tshift(S)(Nat.zero)))(Nat.zero)(tsubst(T2)(j)(S)))
                   (subst_subst_comm(B2)(Nat.zero)(T2)(j)(S)(Eq.refl.{1} Bool Bool.true)))
                (FHasTy.fttapp (tysubstCtx(G2)(j)(S)) (esubstTy(f2)(j)(S)) (tsubst(B2)(Nat.succ j)(tshift(S)(Nat.zero))) (tsubst(T2)(j)(S)) (df.rec j S))
        }
    }

    -- Type-β preserves typing: specialise at variable 0 over a freshly-shifted context.
    def tysubst_preserves (G : FCtx) (b : FExp) (B : FTy) (S : FTy) (dbody : FHasTy (shiftCtx G) b B)
        : FHasTy G (esubstTy(b)(Nat.zero)(S)) (tsubst(B)(Nat.zero)(S)) :=
      Eq.subst.{1} FCtx (fun (g : FCtx) => FHasTy g (esubstTy(b)(Nat.zero)(S)) (tsubst(B)(Nat.zero)(S)))
        (tysubstCtx(shiftCtx(G))(Nat.zero)(S)) G (tysubstCtx_shiftCtx_cancel G S)
        (tysubst_lemma (shiftCtx G) b B dbody Nat.zero S)
"#;

/// **PRESERVATION** — the capstone. `Step e e2 → FHasTy G e T → FHasTy G e2 T`. By induction
/// on the reduction: congruences re-apply typing after inverting the compound term (and use
/// the IH `.rec`), the β-redex is discharged by `esubstTm_preserves` (after inverting the
/// λ and rewriting domain/codomain via arrow injectivity), and the type-β redex by
/// `tysubst_preserves` (after inverting the Λ and rewriting via `tall` injectivity). Together
/// with `progress`, this is full type safety for System F in the verified kernel.
pub const SF_PRES: &str = r#"
    fn preservation(e: FExp, e2: FExp, st: Step e e2)
      -> ((G : FCtx) -> (T : FTy) -> FHasTy G e T -> FHasTy G e2 T) {
        match st {
          | Step.s_app_l(f, f2, a, stf) => fun (G : FCtx) (T : FTy) (d : FHasTy G (FExp.eapp f a) T) =>
              match hasty_app_inv G (FExp.eapp f a) T d f a (Eq.refl.{1} FExp (FExp.eapp f a)) {
                | ExTy.mk(A, And2.mk(df, da)) =>
                    FHasTy.ftapp G f2 a A T (stf.rec G (FTy.tarrow A T) df) da
              }
          | Step.s_app_r(f, a, a2, sta) => fun (G : FCtx) (T : FTy) (d : FHasTy G (FExp.eapp f a) T) =>
              match hasty_app_inv G (FExp.eapp f a) T d f a (Eq.refl.{1} FExp (FExp.eapp f a)) {
                | ExTy.mk(A, And2.mk(df, da)) =>
                    FHasTy.ftapp G f a2 A T df (sta.rec G A da)
              }
          | Step.s_beta(A0, b, v) => fun (G : FCtx) (T : FTy) (d : FHasTy G (FExp.eapp (FExp.elam A0 b) v) T) =>
              match hasty_app_inv G (FExp.eapp (FExp.elam A0 b) v) T d (FExp.elam A0 b) v (Eq.refl.{1} FExp (FExp.eapp (FExp.elam A0 b) v)) {
                | ExTy.mk(A2, And2.mk(df, dv)) =>
                    match hasty_lam_inv G (FExp.elam A0 b) (FTy.tarrow A2 T) df A0 b (Eq.refl.{1} FExp (FExp.elam A0 b)) {
                      | ExTy.mk(B, And2.mk(eqArrow, dbody)) =>
                          esubstTm_preserves A0 G b T v
                            (Eq.subst.{1} FTy (fun (x : FTy) => FHasTy (FCtx.cons A0 G) b x) B T
                               (Eq.symm.{1} FTy T B (tarrow_inj_cod A2 T A0 B eqArrow)) dbody)
                            (Eq.subst.{1} FTy (fun (x : FTy) => FHasTy G v x) A2 A0
                               (tarrow_inj_dom A2 T A0 B eqArrow) dv)
                    }
              }
          | Step.s_tapp(f, f2, T0, stf) => fun (G : FCtx) (T : FTy) (d : FHasTy G (FExp.etapp f T0) T) =>
              match hasty_tapp_inv G (FExp.etapp f T0) T d f T0 (Eq.refl.{1} FExp (FExp.etapp f T0)) {
                | ExTy.mk(B, And2.mk(df, eqT)) =>
                    Eq.subst.{1} FTy (fun (x : FTy) => FHasTy G (FExp.etapp f2 T0) x)
                      (tsubst(B)(Nat.zero)(T0)) T (Eq.symm.{1} FTy T (tsubst(B)(Nat.zero)(T0)) eqT)
                      (FHasTy.fttapp G f2 B T0 (stf.rec G (FTy.tall B) df))
              }
          | Step.s_ttbeta(b, T0) => fun (G : FCtx) (T : FTy) (d : FHasTy G (FExp.etapp (FExp.etlam b) T0) T) =>
              match hasty_tapp_inv G (FExp.etapp (FExp.etlam b) T0) T d (FExp.etlam b) T0 (Eq.refl.{1} FExp (FExp.etapp (FExp.etlam b) T0)) {
                | ExTy.mk(B, And2.mk(df, eqT)) =>
                    match hasty_tlam_inv G (FExp.etlam b) (FTy.tall B) df b (Eq.refl.{1} FExp (FExp.etlam b)) {
                      | ExTy.mk(B2, And2.mk(eqAll, dbody)) =>
                          Eq.subst.{1} FTy (fun (x : FTy) => FHasTy G (esubstTy(b)(Nat.zero)(T0)) x)
                            (tsubst(B2)(Nat.zero)(T0)) T
                            (Eq.trans.{1} FTy (tsubst(B2)(Nat.zero)(T0)) (tsubst(B)(Nat.zero)(T0)) T
                               (tsubst1_cong B2 B Nat.zero T0 (Eq.symm.{1} FTy B B2 (tall_inj B B2 eqAll)))
                               (Eq.symm.{1} FTy T (tsubst(B)(Nat.zero)(T0)) eqT))
                            (tysubst_preserves G b B2 T0 dbody)
                    }
              }
        }
    }
"#;

/// Prelude + types + checker.
pub fn lang_session() -> Result<Session, String> {
    let mut s = Session::new();
    s.run(SF_PRELUDE)?;
    s.run(SF_LANG)?;
    Ok(s)
}

/// Additionally loads the evaluator, so polymorphic programs can be run.
pub fn runnable_session() -> Result<Session, String> {
    let mut s = lang_session()?;
    s.run(SF_DYNAMICS)?;
    Ok(s)
}

/// Loads the typing relation + soundness theorem on top of the checker.
pub fn safety_session() -> Result<Session, String> {
    let mut s = lang_session()?;
    s.run(SF_SAFETY)?;
    Ok(s)
}

/// Loads progress (needs the evaluator's `isValue` + the typing relation).
pub fn progress_session() -> Result<Session, String> {
    let mut s = lang_session()?;
    s.run(SF_DYNAMICS)?;
    s.run(SF_SAFETY)?;
    s.run(SF_PROGRESS)?;
    Ok(s)
}

/// Loads the Step relation + inversion scaffolding (toward preservation).
pub fn step_session() -> Result<Session, String> {
    let mut s = lang_session()?;
    s.run(SF_DYNAMICS)?;
    s.run(SF_SAFETY)?;
    s.run(SF_STEP)?;
    Ok(s)
}

/// Loads the FHasTy inversions (toward preservation's redex cases).
pub fn inv_session() -> Result<Session, String> {
    let mut s = step_session()?;
    s.run(SF_INV)?;
    Ok(s)
}

/// Loads the de Bruijn type-operation lemmas (toward the substitution lemmas) on top of
/// the full inversion stack (so it can reuse `SF_SAFETY`'s congruences + `eqNat_sound`).
pub fn tylemmas_session() -> Result<Session, String> {
    let mut s = inv_session()?;
    s.run(SF_TYLEMMAS)?;
    Ok(s)
}

/// Loads the context-operation + lookup weakening/inversion plumbing.
pub fn ctxops_session() -> Result<Session, String> {
    let mut s = tylemmas_session()?;
    s.run(SF_CTXOPS)?;
    Ok(s)
}

/// Loads the context-level commutation lemmas + FLookup type-shift/subst/inversion.
pub fn ctxcomm_session() -> Result<Session, String> {
    let mut s = ctxops_session()?;
    s.run(SF_CTXCOMM)?;
    Ok(s)
}

/// Loads the term + type weakening theorems.
pub fn weaken_session() -> Result<Session, String> {
    let mut s = ctxcomm_session()?;
    s.run(SF_WEAKEN)?;
    Ok(s)
}

/// Loads the parallel-substitution functions + congruences + applySub_ext.
pub fn tsubsta_session() -> Result<Session, String> {
    let mut s = weaken_session()?;
    s.run(SF_TSUBSTA)?;
    Ok(s)
}

/// Loads the index lemmas + the `esubstTm` bridge.
pub fn tsubstb_session() -> Result<Session, String> {
    let mut s = tsubsta_session()?;
    s.run(SF_TSUBSTB)?;
    s.run(SF_TSUBSTC)?;
    s.run(SF_TSUBSTD)?;
    Ok(s)
}

/// Loads the term substitution lemma + `subst_preserves`/`esubstTm_preserves`.
pub fn tsubst_session() -> Result<Session, String> {
    let mut s = tsubstb_session()?;
    s.run(SF_TSUBSTE)?;
    Ok(s)
}

/// Loads the type substitution lemma + type-β preservation.
pub fn tysubst_session() -> Result<Session, String> {
    let mut s = tsubst_session()?;
    s.run(SF_TYSUBST)?;
    Ok(s)
}

/// Loads **preservation** (needs the Step relation, the inversions, and both substitution
/// lemmas) — full System F type safety together with `progress`.
pub fn preservation_session() -> Result<Session, String> {
    let mut s = tysubst_session()?;
    s.run(SF_PRES)?;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nat(n: u64) -> String {
        let mut s = String::from("Nat.zero");
        for _ in 0..n {
            s = format!("Nat.succ({s})");
        }
        s
    }

    /// The whole checker + evaluator layer elaborates and is kernel-checked.
    #[test]
    fn systemf_lang_checks() {
        runnable_session().expect("System F types + checker + evaluator should check");
    }

    /// The typing relation + **soundness theorem** (`fok_sound`) elaborates and is
    /// kernel-checked: a passing decidable check yields a real System F typing derivation.
    #[test]
    fn systemf_soundness_checks() {
        safety_session().expect("System F typing relation + soundness should check");
    }

    /// **Progress** (`FHasTy nil e T → isValue e ∨ canStep e`) elaborates and is kernel-checked.
    #[test]
    fn systemf_progress_checks() {
        progress_session().expect("System F progress should check");
    }

    /// The Step relation + inversion/no-confusion scaffolding (toward preservation) checks.
    #[test]
    fn systemf_step_checks() {
        step_session().expect("System F Step relation + scaffolding should check");
    }

    /// The FHasTy inversions (toward preservation) elaborate and are kernel-checked.
    #[test]
    fn systemf_inversions_check() {
        inv_session().expect("System F typing inversions should check");
    }

    /// The de Bruijn type-operation lemmas elaborate and are kernel-checked.
    #[test]
    fn systemf_tylemmas_check() {
        tylemmas_session().expect("System F de Bruijn type lemmas should check");
    }

    /// The context-operation + lookup weakening/inversion plumbing elaborates and checks.
    #[test]
    fn systemf_ctxops_check() {
        ctxops_session().expect("System F context-op + lookup lemmas should check");
    }

    /// The context-level commutation + FLookup shift/subst/inversion lemmas check.
    #[test]
    fn systemf_ctxcomm_check() {
        ctxcomm_session().expect("System F context commutation lemmas should check");
    }

    /// The term + type weakening theorems elaborate and are kernel-checked.
    #[test]
    fn systemf_weaken_check() {
        weaken_session().expect("System F weakening theorems should check");
    }

    /// The parallel-substitution functions + the `esubstTm` bridge elaborate and check.
    #[test]
    fn systemf_tsubsta_check() {
        tsubstb_session().expect("System F parallel substitution + bridge should check");
    }

    /// The term substitution lemma + `subst_preserves`/`esubstTm_preserves` check.
    #[test]
    fn systemf_tsubst_check() {
        tsubst_session().expect("System F term substitution lemma should check");
    }

    /// The type substitution lemma + type-β preservation elaborate and check.
    #[test]
    fn systemf_tysubst_check() {
        tysubst_session().expect("System F type substitution lemma should check");
    }

    /// **PRESERVATION** elaborates and is kernel-checked: System F reduction preserves typing.
    #[test]
    fn systemf_preservation_check() {
        preservation_session().expect("System F preservation should check");
    }

    /// **Preservation has teeth.** For the concrete type-β redex `(Λ. λ(x:tvar0). x) [nat]`,
    /// the kernel runs `preservation` on the actual `Step.s_ttbeta` derivation to produce a
    /// checked typing for the contractum `λ(x:nat). x` — at the *same* synthesized type.
    #[test]
    fn preservation_certifies_polymorphic_step() {
        let mut s = preservation_session().unwrap();
        s.run("def polyIdBody : FExp := FExp.elam(FTy.tvar(Nat.zero), FExp.evar(Nat.zero))").unwrap();
        s.run("def redex : FExp := FExp.etapp(FExp.etlam(polyIdBody), FTy.tnat)").unwrap();
        s.run("def redex_ty : FTy := fsynth(redex)(FCtx.nil)").unwrap();
        s.run("def redex_typed : FHasTy FCtx.nil redex redex_ty := fok_sound(redex)(FCtx.nil)(Eq.refl.{1} Bool Bool.true)").unwrap();
        s.run(
            "def stepped_typed : FHasTy FCtx.nil (esubstTy(polyIdBody)(Nat.zero)(FTy.tnat)) redex_ty := \
               preservation(redex)(esubstTy(polyIdBody)(Nat.zero)(FTy.tnat))(Step.s_ttbeta polyIdBody FTy.tnat)(FCtx.nil)(redex_ty)(redex_typed)",
        )
        .expect("preservation should certify the contractum at the same type");
        assert!(s.k.env().contains("stepped_typed"));
    }

    /// **Soundness has teeth.** For the polymorphic identity, the `refl` certificate exists,
    /// so `fok_sound` produces a kernel-checked derivation `FHasTy nil polyId (∀.0→0)`.
    #[test]
    fn soundness_certifies_polymorphic_identity() {
        let mut s = safety_session().unwrap();
        s.run("def polyId : FExp := FExp.etlam(FExp.elam(FTy.tvar(Nat.zero), FExp.evar(Nat.zero)))").unwrap();
        s.run(
            "def polyId_typed : FHasTy FCtx.nil polyId (fsynth(polyId)(FCtx.nil)) := \
               fok_sound(polyId)(FCtx.nil)(Eq.refl.{1} Bool Bool.true)",
        )
        .expect("a well-typed polymorphic term has a checked derivation");
        assert!(s.k.env().contains("polyId_typed"));
    }

    /// **Polymorphism type-checks and runs.** The polymorphic identity
    /// `Λ. λ(x:tvar0). x : ∀. tvar0 → tvar0`, instantiated at `nat` and applied to `5`,
    /// synthesizes `nat` and runs to `5` — type application substitutes `nat` into the
    /// λ's annotation, then β-reduces.
    #[test]
    fn polymorphic_identity_runs() {
        let mut s = runnable_session().unwrap();
        s.run("def polyId : FExp := FExp.etlam(FExp.elam(FTy.tvar(Nat.zero), FExp.evar(Nat.zero)))").unwrap();
        s.run("def polyId_ty : FTy := fsynth(polyId)(FCtx.nil)").unwrap();
        s.run("def polyId_ok : Bool := fok(polyId)(FCtx.nil)").unwrap();
        // (polyId [nat]) 5
        s.run(&format!(
            "def app : FExp := FExp.eapp(FExp.etapp(polyId, FTy.tnat), FExp.enat({}))", nat(5)
        )).unwrap();
        s.run("def app_ty : FTy := fsynth(app)(FCtx.nil)").unwrap();
        s.run("def app_ok : Bool := fok(app)(FCtx.nil)").unwrap();
        s.run(&format!("def app_val : FExp := run({})(app)", nat(10))).unwrap();
        assert_eq!(s.run_entry("polyId_ok").unwrap(), "Bool.true");
        assert_eq!(s.run_entry("polyId_ty").unwrap(), "FTy.tall (FTy.tarrow (FTy.tvar 0) (FTy.tvar 0))");
        assert_eq!(s.run_entry("app_ok").unwrap(), "Bool.true", "instantiated application is well typed");
        assert_eq!(s.run_entry("app_ty").unwrap(), "FTy.tnat", "polyId [nat] 5 : nat");
        assert_eq!(s.run_entry("app_val").unwrap(), "FExp.enat 5", "polyId [nat] 5 = 5");
    }
}
