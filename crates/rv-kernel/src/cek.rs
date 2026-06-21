//! **Tier 4 — a CEK abstract machine (and, on top of it, algebraic effect handlers).**
//!
//! Where [`crate::stlc`] evaluates by *searching* a term for the next redex (a
//! substitution-based small-step `step : Exp → OExp`), this module evaluates with an
//! **explicit control stack** and an **environment** — an abstract machine. A CEK machine
//! is a transition system over states
//!
//! ```text
//!   ⟨ C , E , K ⟩
//! ```
//!
//! the **C**ontrol (the term in focus), the **E**nvironment (the values of the de Bruijn
//! variables in scope), and the **K**ontinuation (a *defunctionalised* stack recording
//! "what to do with the value once C is done"). Functions are **closures** — a body paired
//! with the environment it captured — so there is **no substitution at all**: applying
//! `(λ. b)` to `v` just extends the environment with `v` and continues with `b`. Each
//! transition is `O(1)`: no redex search, no term traversal.
//!
//! This is the genuine CEK machine. An earlier version of this module was a *CK* machine
//! (substitution instead of an environment) because the surface `match` compiler could not
//! eliminate a member of a mutual inductive group — and closures force `Val`/`Env` to be
//! mutual (a value may be a closure holding an environment; an environment is a list of
//! values). That limitation is now lifted (`elab2::compile_match_mutual`), so the machine
//! carries a real environment.
//!
//! Everything here is verified Raven, kernel-checked, and **executable**: the tests run
//! real programs through the machine and read the resulting number back out.
//!
//!  * **Machine** — `Tm` (variables, literals, λ, application, addition, a zero-test
//!    conditional), the mutually-inductive closures `Val`/`Env`, the defunctionalised
//!    continuation `Kont`, the machine `State`, the single transition `step : State →
//!    State`, and the fuelled driver `run`.
//!  * **Effects** — `Tm.op`/`Tm.handle`: `handle` evaluates its handler to a closure and
//!    pushes a handler frame; performing an `op` **unwinds** the stack to the nearest
//!    handler and applies it to the payload, discarding the delimited continuation in
//!    between (the exception/abort fragment of algebraic effects — no first-class
//!    resumption, which would additionally need `Kont` reified as a `Val`).
//!  * **Metatheory** ([`META`]) — the driver's fixed-point theorems.

use crate::verify::Session;

/// Logic, booleans, naturals (with addition), and the focused term language `Tm`.
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
    fn addN(m: Nat) -> (Nat -> Nat) {
        match m { | Nat.zero => fun (n : Nat) => n | Nat.succ(k) => fun (n : Nat) => Nat.succ(addN(k)(n)) }
    }

    -- The focused core language (de Bruijn variables; only `lam` binds). The last two
    -- constructors are the **algebraic effects** layer: `op` performs an operation with a
    -- payload, and `handle body h` runs `body` under the handler function `h`.
    inductive Tm : Type
      | var : Nat -> Tm
      | lit : Nat -> Tm
      | lam : Tm -> Tm                -- λ. body          (body refers to the parameter as var 0)
      | app : Tm -> Tm -> Tm
      | add : Tm -> Tm -> Tm
      | ifz : Tm -> Tm -> Tm -> Tm    -- ifz s then else  (branch on whether s evaluates to zero)
      | op  : Tm -> Tm                -- perform an operation carrying the payload term
      | handle : Tm -> Tm -> Tm       -- handle body with handler `h : payload -> result`
"#;

/// The machine: closures + environments, the continuation stack, the state, the transition.
pub const MACHINE: &str = r#"
    -- Closures and environments are mutually inductive: a value may be a closure capturing
    -- an environment, and an environment is a list of values. (Matching on a member of a
    -- mutual group is what `elab2::compile_match_mutual` makes possible.)
    mutual {
      inductive Val : Type
        | vnat  : Nat -> Val
        | vclos : Env -> Tm -> Val      -- ⟨ captured env , λ-body ⟩
      inductive Env : Type
        | enil  : Env
        | econs : Val -> Env -> Env
    }

    -- Environment lookup by de Bruijn index. Out-of-scope indices return a dummy `vnat 0`;
    -- on closed, well-scoped programs (everything the machine is run on) that never fires.
    -- Recurses on the *index* (a plain `Nat`), so it is an ordinary solo recursion.
    fn lookupEnv(n: Nat) -> (Env -> Val) {
        match n {
          | Nat.zero => fun (e : Env) =>
              match e { | Env.enil => Val.vnat Nat.zero | Env.econs(v, rest) => v }
          | Nat.succ(m) => fun (e : Env) =>
              match e { | Env.enil => Val.vnat Nat.zero | Env.econs(v, rest) => lookupEnv(m)(rest) }
        }
    }

    -- The continuation: a defunctionalised "rest of the computation" stack. Each frame
    -- remembers the environment for the sub-terms not yet run. The last three frames are
    -- the effects layer: `kop` (payload being evaluated), `khEval` (a handler being
    -- evaluated, with its body pending), and `khandle` (an installed handler value).
    inductive Kont : Type
      | kdone : Kont
      | kapp1 : Env -> Tm -> Kont -> Kont        -- evaluating the function; arg term + env pending
      | kapp2 : Val -> Kont -> Kont              -- function value in hand; evaluating the argument
      | kadd1 : Env -> Tm -> Kont -> Kont        -- evaluating the left summand; right term + env pending
      | kadd2 : Nat -> Kont -> Kont              -- left summand computed; evaluating the right
      | kifz  : Env -> Tm -> Tm -> Kont -> Kont  -- evaluating the scrutinee; both branches + env pending
      | kop   : Kont -> Kont                     -- payload of a performed operation is being evaluated
      | khEval : Tm -> Env -> Kont -> Kont       -- handler being evaluated; its body + env pending
      | khandle : Val -> Kont -> Kont            -- an installed handler value around the running body

    -- A machine state: "evaluate C under E with K", "return value V to K", a final answer,
    -- or stuck (a type error the checker rules out).
    inductive State : Type
      | seval  : Tm -> Env -> Kont -> State
      | sret   : Val -> Kont -> State
      | sdone  : Val -> State
      | sstuck : State

    fn isFinal(s: State) -> Bool {
        match s { | State.sdone(v) => Bool.true | State.sstuck => Bool.true
                 | State.seval(t, e, k) => Bool.false | State.sret(v, k) => Bool.false }
    }

    -- UNWIND: an operation has been performed with payload `v`; walk the continuation to the
    -- nearest installed handler, discarding the frames in between, and apply that handler
    -- (a closure) to the payload. No handler ⇒ unhandled effect ⇒ stuck. Recurses on `Kont`.
    fn unwind(k: Kont) -> (Val -> State) {
        match k {
          | Kont.kdone => fun (v : Val) => State.sstuck
          | Kont.khandle(vh, k2) => fun (v : Val) =>
              match vh {
                | Val.vclos(cenv, hbody) => State.seval hbody (Env.econs v cenv) k2
                | Val.vnat(n) => State.sstuck
              }
          | Kont.kop(k2)            => fun (v : Val) => unwind(k2)(v)
          | Kont.khEval(b, e, k2)   => fun (v : Val) => unwind(k2)(v)
          | Kont.kapp1(e, a, k2)    => fun (v : Val) => unwind(k2)(v)
          | Kont.kapp2(vf, k2)      => fun (v : Val) => unwind(k2)(v)
          | Kont.kadd1(e, y, k2)    => fun (v : Val) => unwind(k2)(v)
          | Kont.kadd2(m, k2)       => fun (v : Val) => unwind(k2)(v)
          | Kont.kifz(e, t2, e2, k2) => fun (v : Val) => unwind(k2)(v)
        }
    }

    -- THE TRANSITION. One clause per (control shape) and per (continuation frame); a total
    -- function and a *single* step — no search, no substitution.
    fn step(s: State) -> State {
        match s {
          | State.seval(t, env, k) =>
              match t {
                | Tm.var(n)         => State.sret (lookupEnv(n)(env)) k
                | Tm.lit(n)         => State.sret (Val.vnat n) k
                | Tm.lam(b)         => State.sret (Val.vclos env b) k
                | Tm.app(f, a)      => State.seval f env (Kont.kapp1 env a k)
                | Tm.add(x, y)      => State.seval x env (Kont.kadd1 env y k)
                | Tm.ifz(c, t2, e2) => State.seval c env (Kont.kifz env t2 e2 k)
                | Tm.op(a)          => State.seval a env (Kont.kop k)
                | Tm.handle(b, h)   => State.seval h env (Kont.khEval b env k)
              }
          | State.sret(v, k) =>
              match k {
                | Kont.kdone => State.sdone v
                | Kont.kapp1(env, a, k2) => State.seval a env (Kont.kapp2 v k2)
                | Kont.kapp2(vf, k2) =>
                    match vf {
                      | Val.vclos(cenv, body) => State.seval body (Env.econs v cenv) k2
                      | Val.vnat(n) => State.sstuck
                    }
                | Kont.kadd1(env, y, k2) =>
                    match v {
                      | Val.vnat(m) => State.seval y env (Kont.kadd2 m k2)
                      | Val.vclos(cenv, body) => State.sstuck
                    }
                | Kont.kadd2(m, k2) =>
                    match v {
                      | Val.vnat(n) => State.sret (Val.vnat (addN(m)(n))) k2
                      | Val.vclos(cenv, body) => State.sstuck
                    }
                | Kont.kifz(env, t2, e2, k2) =>
                    match v {
                      | Val.vnat(n) => match n { | Nat.zero => State.seval t2 env k2 | Nat.succ(m) => State.seval e2 env k2 }
                      | Val.vclos(cenv, body) => State.sstuck
                    }
                | Kont.kop(k2) => unwind(k2)(v)                      -- payload evaluated: perform the effect
                | Kont.khEval(body, env2, k2) => State.seval body env2 (Kont.khandle v k2)  -- handler ready; run body
                | Kont.khandle(vh, k2) => State.sret v k2            -- body finished normally: discard the handler
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

    -- Load a closed term into the initial state (empty environment), and read a number out
    -- of a final state.
    def load (t : Tm) : State := State.seval t Env.enil Kont.kdone
    def evalNat (fuel : Nat) (t : Tm) : Nat :=
      match run(fuel)(load(t)) {
        | State.sdone(v) => match v { | Val.vnat(n) => n | Val.vclos(env, b) => Nat.zero }
        | State.sret(v, k) => Nat.zero
        | State.seval(t2, e, k) => Nat.zero
        | State.sstuck => Nat.zero
      }
"#;

/// **The machine-checked metatheory of the driver.** `step` is a *total function*, so
/// determinism is free; the content here is that the driver halts correctly:
///
///  * `step_final` — a **final** state (`sdone`/`sstuck`) is a fixed point of `step`.
///  * `run_final_fix` — starting from a final state, `run` returns it unchanged for **any**
///    fuel: once the machine answers, more steps never change the answer.
pub const META: &str = r#"
    -- Bool no-confusion: `false ≠ true`.
    def isFalseProp (b : Bool) : Prop := Bool.rec.{1} (fun (_ : Bool) => Prop) True False b
    def ff_ne_tt (h : Eq.{1} Bool Bool.false Bool.true) : False :=
      Eq.rec.{1, 0} Bool Bool.false
        (fun (b : Bool) (_ : Eq.{1} Bool Bool.false b) => isFalseProp b)
        True.intro Bool.true h

    -- A final state is a fixed point of `step`. For `seval`/`sret`, `isFinal s` computes to
    -- `false`, so the hypothesis is absurd and the goal follows by `False.rec`.
    fn step_final(s: State)
      -> (Eq.{1} Bool (isFinal s) Bool.true -> Eq.{1} State (step s) s) {
        match s {
          | State.sdone(v) => fun (h : Eq.{1} Bool (isFinal (State.sdone v)) Bool.true) =>
              Eq.refl.{1} State (State.sdone v)
          | State.sstuck => fun (h : Eq.{1} Bool (isFinal State.sstuck) Bool.true) =>
              Eq.refl.{1} State State.sstuck
          | State.seval(t, e, k) => fun (h : Eq.{1} Bool (isFinal (State.seval t e k)) Bool.true) =>
              False.rec.{0}
                (fun (_ : False) => Eq.{1} State (step (State.seval t e k)) (State.seval t e k))
                (ff_ne_tt h)
          | State.sret(v, k) => fun (h : Eq.{1} Bool (isFinal (State.sret v k)) Bool.true) =>
              False.rec.{0}
                (fun (_ : False) => Eq.{1} State (step (State.sret v k)) (State.sret v k))
                (ff_ne_tt h)
        }
    }

    -- Running a final state for any amount of fuel leaves it unchanged. `run (succ k) s`
    -- unfolds to `match isFinal s { true => s | false => run k (step s) }`; rewriting
    -- `isFinal s` to `true` (the hypothesis) collapses it to `s`.
    fn run_final_fix(n: Nat)
      -> ((s : State) -> Eq.{1} Bool (isFinal s) Bool.true -> Eq.{1} State (run n s) s) {
        match n {
          | Nat.zero => fun (s : State) (h : Eq.{1} Bool (isFinal s) Bool.true) =>
              Eq.refl.{1} State s
          | Nat.succ(k) => fun (s : State) (h : Eq.{1} Bool (isFinal s) Bool.true) =>
              Eq.subst.{1} Bool
                (fun (b : Bool) =>
                   Eq.{1} State (match b { | Bool.true => s | Bool.false => run(k)(step(s)) }) s)
                Bool.true (isFinal s) (Eq.symm.{1} Bool (isFinal s) Bool.true h)
                (Eq.refl.{1} State s)
        }
    }
"#;

/// The base session: the prelude + the machine, kernel-checked and ready to *run*.
pub fn session() -> Result<Session, String> {
    let mut s = Session::new();
    s.run(PRELUDE)?;
    s.run(MACHINE)?;
    Ok(s)
}

/// The machine session plus the [`META`] driver metatheory (the fixed-point theorems).
pub fn meta_session() -> Result<Session, String> {
    let mut s = session()?;
    s.run(META)?;
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
        // (λx. x + 1) 2  ==>  3  (β extends the environment; no substitution)
        let prog = "Tm.app (Tm.lam (Tm.add (Tm.var Nat.zero) (Tm.lit (Nat.succ Nat.zero)))) \
                    (Tm.lit (Nat.succ (Nat.succ Nat.zero)))";
        assert_eq!(eval(prog, 20), "3");
    }

    #[test]
    fn closure_captures_its_environment() {
        // (λx. (λy. x) 9) 5  ==>  5   — the inner closure must capture x from the outer env.
        let inner = format!(
            "Tm.app (Tm.lam (Tm.var (Nat.succ Nat.zero))) (Tm.lit ({}))",
            nat(9)
        );
        let prog = format!("Tm.app (Tm.lam ({inner})) (Tm.lit ({}))", nat(5));
        assert_eq!(eval(&prog, 30), "5");
    }

    #[test]
    fn driver_metatheory_kernel_checks() {
        // The fixed-point theorems (step_final, run_final_fix) are verified by the kernel.
        let s = meta_session().expect("driver metatheory should kernel-check");
        assert!(s.k.env().contains("step_final"));
        assert!(s.k.env().contains("run_final_fix"));
    }
}
