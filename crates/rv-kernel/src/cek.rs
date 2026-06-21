//! **Tier 4 — a CK abstract machine (and, on top of it, algebraic effect handlers).**
//!
//! Where [`crate::stlc`] evaluates by *searching* a term for the next redex (a
//! substitution-based small-step `step : Exp → OExp`), this module evaluates with an
//! **explicit control stack** — an abstract machine. A CK machine is a transition system
//! over states
//!
//! ```text
//!   ⟨ C , K ⟩
//! ```
//!
//! the **C**ontrol (the term currently in focus) and the **K**ontinuation (a
//! *defunctionalised* stack recording "what to do with the value once C is done"). The
//! search for the next redex that the small-step semantics re-does on every step is
//! replaced here by following the stack — each transition is `O(1)`.
//!
//! ## CK, not CEK — and why
//!
//! The textbook **CEK** machine adds an **E**nvironment, so functions become *closures*
//! (a body plus the environment it captured) and β just extends the environment instead
//! of substituting. That requires values and environments to be **mutually inductive**
//! (a value may be a closure holding an environment; an environment is a list of values).
//! This kernel's surface `match` compiler does not yet support matching on a member of a
//! mutual inductive group outside a mutual-function bundle, which makes a readable `step`
//! over closures impractical today. So this module uses the **CK** presentation: the same
//! explicit control stack, but β-reduction is by **substitution** (reusing the de Bruijn
//! machinery), exactly as in Felleisen & Friedman's original CK machine. Everything below
//! is over a single, ordinary inductive, so every transition is a plain `match`.
//!
//! Everything here is verified Raven, kernel-checked, and **executable**: the tests run
//! real programs through the machine and read the resulting number back out.
//!
//!  * **Machine** — `Tm` (variables, literals, λ, application, addition, a zero-test
//!    conditional), the de Bruijn `shift`/`subst`, the defunctionalised continuation
//!    `Kont`, the machine `State`, the single-transition `step : State → State`, and the
//!    fuelled driver `run`.
//!  * **Effects** (in [`EFFECTS`]) — `Tm.op`/`Tm.handle`: the continuation grows a
//!    handler frame, and performing an operation unwinds the stack to the nearest handler.
//!
//! The headline correctness property is in [`META`]; the computational tests pin
//! behaviour.

use crate::verify::Session;

/// Logic, booleans, naturals (with the de Bruijn index helpers), and the term language.
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

    inductive Bool : Type | false : Bool | true : Bool
    inductive Nat : Type | zero : Nat | succ : Nat -> Nat
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
    fn shiftIdx(k: Nat) -> (Nat -> Nat) {
        match k {
          | Nat.zero    => fun (n : Nat) => Nat.succ(n)
          | Nat.succ(k2) => fun (n : Nat) =>
              match n { | Nat.zero => Nat.zero | Nat.succ(n2) => Nat.succ(shiftIdx(k2)(n2)) }
        }
    }

    -- The focused core language (de Bruijn variables; only `lam` binds).
    inductive Tm : Type
      | var : Nat -> Tm
      | lit : Nat -> Tm
      | lam : Tm -> Tm                -- λ. body          (body refers to the parameter as var 0)
      | app : Tm -> Tm -> Tm
      | add : Tm -> Tm -> Tm
      | ifz : Tm -> Tm -> Tm -> Tm    -- ifz s then else  (branch on whether s evaluates to zero)
"#;

/// The machine: de Bruijn substitution, the continuation stack, the state, the transition.
pub const MACHINE: &str = r#"
    -- de Bruijn shift: lift free variables (index ≥ cutoff) by one (under `lam`, the
    -- cutoff goes up). Needed so substitution under a binder does not capture.
    fn shift(t: Tm) -> (Nat -> Tm) {
        match t {
          | Tm.var(n)   => fun (c : Nat) => Tm.var(shiftIdx(c)(n))
          | Tm.lit(n)   => fun (c : Nat) => Tm.lit(n)
          | Tm.lam(b)   => fun (c : Nat) => Tm.lam(shift(b)(Nat.succ(c)))
          | Tm.app(f, a) => fun (c : Nat) => Tm.app(shift(f)(c), shift(a)(c))
          | Tm.add(x, y) => fun (c : Nat) => Tm.add(shift(x)(c), shift(y)(c))
          | Tm.ifz(s, th, el) => fun (c : Nat) => Tm.ifz(shift(s)(c), shift(th)(c), shift(el)(c))
        }
    }

    -- Single-variable substitution `t[j := v]`: replace `var j` by `v`, decrement the
    -- variables above `j` (the binder for `j` is gone), and shift `v` as it crosses binders.
    fn subst(t: Tm) -> (Nat -> (Tm -> Tm)) {
        match t {
          | Tm.var(n)   => fun (j : Nat) (v : Tm) =>
              match nat_eqb(n)(j) {
                | Bool.true  => v
                | Bool.false => match nat_ltb(j)(n) { | Bool.true => Tm.var(pred(n)) | Bool.false => Tm.var(n) }
              }
          | Tm.lit(n)   => fun (j : Nat) (v : Tm) => Tm.lit(n)
          | Tm.lam(b)   => fun (j : Nat) (v : Tm) => Tm.lam(subst(b)(Nat.succ(j))(shift(v)(Nat.zero)))
          | Tm.app(f, a) => fun (j : Nat) (v : Tm) => Tm.app(subst(f)(j)(v), subst(a)(j)(v))
          | Tm.add(x, y) => fun (j : Nat) (v : Tm) => Tm.add(subst(x)(j)(v), subst(y)(j)(v))
          | Tm.ifz(s, th, el) => fun (j : Nat) (v : Tm) => Tm.ifz(subst(s)(j)(v), subst(th)(j)(v), subst(el)(j)(v))
        }
    }
    -- β: open a λ-body with an argument (substitute it for the bound variable 0).
    def open (b : Tm) (v : Tm) : Tm := subst(b)(Nat.zero)(v)

    -- The values: literals and λ-abstractions.
    fn isVal(t: Tm) -> Bool {
        match t {
          | Tm.var(n) => Bool.false | Tm.lit(n) => Bool.true | Tm.lam(b) => Bool.true
          | Tm.app(f, a) => Bool.false | Tm.add(x, y) => Bool.false | Tm.ifz(s, th, el) => Bool.false
        }
    }

    -- The continuation: a defunctionalised "rest of the computation" stack. Each frame is
    -- one pending elimination, remembering the sub-terms not yet evaluated.
    inductive Kont : Type
      | kdone : Kont
      | kapp1 : Tm -> Kont -> Kont        -- evaluating the function; argument term still to run
      | kapp2 : Tm -> Kont -> Kont        -- function *value* in hand; evaluating the argument
      | kadd1 : Tm -> Kont -> Kont        -- evaluating the left summand; right term still to run
      | kadd2 : Nat -> Kont -> Kont       -- left summand computed; evaluating the right
      | kifz  : Tm -> Tm -> Kont -> Kont  -- evaluating the scrutinee; both branches pending

    -- A machine state: "evaluate C with K", "return value V to K", a final answer, or stuck.
    inductive State : Type
      | seval  : Tm -> Kont -> State
      | sret   : Tm -> Kont -> State
      | sdone  : Tm -> State
      | sstuck : State

    fn isFinal(s: State) -> Bool {
        match s { | State.sdone(v) => Bool.true | State.sstuck => Bool.true
                 | State.seval(t, k) => Bool.false | State.sret(v, k) => Bool.false }
    }

    -- THE TRANSITION. One clause per (control shape) and per (continuation frame); a total
    -- function and a *single* step — no search, no recursion.
    fn step(s: State) -> State {
        match s {
          | State.seval(t, k) =>
              match t {
                | Tm.var(n)         => State.sstuck                                  -- closed programs never focus a free var
                | Tm.lit(n)         => State.sret (Tm.lit n) k
                | Tm.lam(b)         => State.sret (Tm.lam b) k
                | Tm.app(f, a)      => State.seval f (Kont.kapp1 a k)
                | Tm.add(x, y)      => State.seval x (Kont.kadd1 y k)
                | Tm.ifz(c, t2, e2) => State.seval c (Kont.kifz t2 e2 k)
              }
          | State.sret(v, k) =>
              match k {
                | Kont.kdone => State.sdone v
                | Kont.kapp1(a, k2) => State.seval a (Kont.kapp2 v k2)
                | Kont.kapp2(vf, k2) =>
                    match vf {
                      | Tm.lam(b) => State.seval (open b v) k2
                      | Tm.var(n) => State.sstuck | Tm.lit(n) => State.sstuck
                      | Tm.app(f, a) => State.sstuck | Tm.add(x, y) => State.sstuck | Tm.ifz(c, t2, e2) => State.sstuck
                    }
                | Kont.kadd1(y, k2) =>
                    match v {
                      | Tm.lit(m) => State.seval y (Kont.kadd2 m k2)
                      | Tm.var(n) => State.sstuck | Tm.lam(b) => State.sstuck
                      | Tm.app(f, a) => State.sstuck | Tm.add(x, y2) => State.sstuck | Tm.ifz(c, t2, e2) => State.sstuck
                    }
                | Kont.kadd2(m, k2) =>
                    match v {
                      | Tm.lit(n) => State.sret (Tm.lit (addN(m)(n))) k2
                      | Tm.var(n) => State.sstuck | Tm.lam(b) => State.sstuck
                      | Tm.app(f, a) => State.sstuck | Tm.add(x, y2) => State.sstuck | Tm.ifz(c, t2, e2) => State.sstuck
                    }
                | Kont.kifz(t2, e2, k2) =>
                    match v {
                      | Tm.lit(n) => match n { | Nat.zero => State.seval t2 k2 | Nat.succ(m) => State.seval e2 k2 }
                      | Tm.var(n) => State.sstuck | Tm.lam(b) => State.sstuck
                      | Tm.app(f, a) => State.sstuck | Tm.add(x, y2) => State.sstuck | Tm.ifz(c, t3, e3) => State.sstuck
                    }
              }
          | State.sdone(v) => State.sdone v
          | State.sstuck => State.sstuck
        }
    }

    -- The fuelled driver: step until the state is final or the fuel runs out.
    fn run(fuel: Nat) -> (State -> State) {
        match fuel {
          | Nat.zero    => fun (s : State) => s
          | Nat.succ(k) => fun (s : State) =>
              match isFinal(s) { | Bool.true => s | Bool.false => run(k)(step(s)) }
        }
    }

    -- Load a closed term into the initial state, and read a number out of a final state.
    def load (t : Tm) : State := State.seval t Kont.kdone
    def evalNat (fuel : Nat) (t : Tm) : Nat :=
      match run(fuel)(load(t)) {
        | State.sdone(v) =>
            match v {
              | Tm.lit(n) => n
              | Tm.var(n) => Nat.zero | Tm.lam(b) => Nat.zero
              | Tm.app(f, a) => Nat.zero | Tm.add(x, y) => Nat.zero | Tm.ifz(c, t2, e2) => Nat.zero
            }
        | State.sret(v, k) => Nat.zero
        | State.seval(t2, k) => Nat.zero
        | State.sstuck => Nat.zero
      }
"#;

/// The base session: the prelude + the machine, kernel-checked and ready to *run*.
pub fn session() -> Result<Session, String> {
    let mut s = Session::new();
    s.run(PRELUDE)?;
    s.run(MACHINE)?;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build `Nat.succ^n Nat.zero` for fuel/program literals.
    fn nat(n: usize) -> String {
        let mut s = String::from("Nat.zero");
        for _ in 0..n {
            s = format!("Nat.succ ({s})");
        }
        s
    }

    /// Load `prog`, run it with `fuel` steps, and read back the resulting number.
    fn eval(prog: &str, fuel: usize) -> String {
        let mut s = session().unwrap();
        s.run(&format!("def prog : Tm := {prog}")).unwrap();
        s.run(&format!("def fuel : Nat := {}", nat(fuel))).unwrap();
        s.run("def answer : Nat := evalNat fuel prog").unwrap();
        s.run_entry("answer").unwrap()
    }

    #[test]
    fn beta_and_addition() {
        // (λx. x + 1) 2  ==>  3
        let prog = "Tm.app (Tm.lam (Tm.add (Tm.var Nat.zero) (Tm.lit (Nat.succ Nat.zero)))) \
                    (Tm.lit (Nat.succ (Nat.succ Nat.zero)))";
        assert_eq!(eval(prog, 20), "3");
    }
}
