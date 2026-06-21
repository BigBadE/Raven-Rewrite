//! **Tier 4 — a CEK abstract machine with resumable algebraic effect handlers.**
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
//! with the environment it captured — so there is **no substitution at all**. Each
//! transition is `O(1)`.
//!
//! ## Effects: handlers with first-class resumptions
//!
//! `handle body h` runs `body` under the handler `h : payload → resume → result`. When
//! `body` performs `op v`, the machine walks the continuation to the nearest handler and
//! calls `h` with the payload `v` **and a resumption** — the continuation captured at the
//! `op`, reified as a value `Val.vkont`. The handler may **resume** (apply the resumption
//! to a value, continuing the suspended computation — `λp. λk. k p` makes `op` behave like
//! a value-returning call) or **abort** (ignore the resumption, replacing the whole handled
//! expression — `λp. λk. p`). Resuming re-installs the handler, i.e. **deep** handlers.
//! This is full algebraic effects, not just exceptions.
//!
//! Reifying the resumption forces `Val`, `Env` and `Kont` into one **mutual** inductive
//! group (a value may be a continuation; a continuation frame may hold a value). Matching on
//! members of such a group — and the handler-search written as a *mutual function bundle*
//! over the group — is exactly what `elab2::compile_match_mutual` and the bundle compiler
//! make possible.
//!
//! Everything is verified Raven, kernel-checked, and **executable**: the tests run real
//! programs through the machine and read the resulting number back out.
//!
//!  * **Machine** — `Tm`, the mutually-inductive `Val`/`Env`/`Kont`, the `State`, the
//!    single transition `step`, and the fuelled driver `run`.
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
    -- payload, and `handle body h` runs `body` under the handler `h : payload -> resume -> r`.
    inductive Tm : Type
      | var : Nat -> Tm
      | lit : Nat -> Tm
      | lam : Tm -> Tm                -- λ. body          (body refers to the parameter as var 0)
      | app : Tm -> Tm -> Tm
      | add : Tm -> Tm -> Tm
      | ifz : Tm -> Tm -> Tm -> Tm    -- ifz s then else  (branch on whether s evaluates to zero)
      | op  : Tm -> Tm                -- perform an operation carrying the payload term
      | handle : Tm -> Tm -> Tm       -- handle body with handler `h : payload -> resume -> r`
"#;

/// The machine: closures + environments + reified continuations, the state, the transition.
pub const MACHINE: &str = r#"
    -- Values, environments, and continuations are ONE mutual inductive group: a value may
    -- be a closure (capturing an environment) or a reified continuation `vkont` (a
    -- resumption); an environment is a list of values; a continuation frame may hold values
    -- and other continuations.
    mutual {
      inductive Val : Type
        | vnat  : Nat -> Val
        | vclos : Env -> Tm -> Val      -- ⟨ captured env , λ-body ⟩
        | vkont : Kont -> Val           -- a reified resumption (first-class continuation)
      inductive Env : Type
        | enil  : Env
        | econs : Val -> Env -> Env
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
        | kresume : Val -> Kont -> Kont            -- apply the returned function to this value, then continue
    }

    -- Environment lookup by de Bruijn index. Recurses on the *index* (a plain `Nat`), so it
    -- is an ordinary solo recursion even though `Env` is a mutual member.
    fn lookupEnv(n: Nat) -> (Env -> Val) {
        match n {
          | Nat.zero => fun (e : Env) =>
              match e { | Env.enil => Val.vnat Nat.zero | Env.econs(v, rest) => v }
          | Nat.succ(m) => fun (e : Env) =>
              match e { | Env.enil => Val.vnat Nat.zero | Env.econs(v, rest) => lookupEnv(m)(rest) }
        }
    }

    -- A machine state: "evaluate C under E with K", "return value V to K", a final answer,
    -- or stuck (a type error the checker rules out).
    inductive State : Type
      | seval  : Tm -> Env -> Kont -> State
      | sret   : Val -> Kont -> State
      | sdone  : Val -> State
      | sstuck : State

    -- HANDLER SEARCH. `walkKont` walks a continuation down to the nearest installed handler
    -- and fires it: it runs the handler body with the payload bound and the *original*
    -- continuation (passed as `ko`) reified as the resumption `vkont ko`; the handler then
    -- runs with the continuation that was below the handler. No handler ⇒ stuck.
    --
    -- It must recurse structurally over `Kont` (a mutual member), so it is written as a
    -- mutual-function bundle over the whole group; `walkVal`/`walkEnv` are the (unused)
    -- sibling members the bundle requires. Each returns `Kont -> Val -> State`, i.e. it is
    -- applied to the original continuation `ko` and the payload `pv`.
    fn walkVal(x: Val) -> (Kont -> (Val -> State)) {
        match x {
          | Val.vnat(n)      => fun (ko : Kont) => fun (pv : Val) => State.sstuck
          | Val.vclos(e, b)  => fun (ko : Kont) => fun (pv : Val) => State.sstuck
          | Val.vkont(kk)    => fun (ko : Kont) => fun (pv : Val) => State.sstuck
        }
    }
    fn walkEnv(x: Env) -> (Kont -> (Val -> State)) {
        match x {
          | Env.enil         => fun (ko : Kont) => fun (pv : Val) => State.sstuck
          | Env.econs(v, r)  => fun (ko : Kont) => fun (pv : Val) => State.sstuck
        }
    }
    fn walkKont(k: Kont) -> (Kont -> (Val -> State)) {
        match k {
          | Kont.kdone => fun (ko : Kont) => fun (pv : Val) => State.sstuck
          | Kont.khandle(vh, k2) => fun (ko : Kont) => fun (pv : Val) =>
              match vh {
                | Val.vclos(hcenv, hb) => State.seval hb (Env.econs pv hcenv) (Kont.kresume (Val.vkont ko) k2)
                | Val.vnat(n) => State.sstuck
                | Val.vkont(kk) => State.sstuck
              }
          | Kont.kapp1(e, a, k2)     => fun (ko : Kont) => fun (pv : Val) => walkKont(k2)(ko)(pv)
          | Kont.kapp2(vf, k2)       => fun (ko : Kont) => fun (pv : Val) => walkKont(k2)(ko)(pv)
          | Kont.kadd1(e, y, k2)     => fun (ko : Kont) => fun (pv : Val) => walkKont(k2)(ko)(pv)
          | Kont.kadd2(m, k2)        => fun (ko : Kont) => fun (pv : Val) => walkKont(k2)(ko)(pv)
          | Kont.kifz(e, t2, e2, k2) => fun (ko : Kont) => fun (pv : Val) => walkKont(k2)(ko)(pv)
          | Kont.kop(k2)             => fun (ko : Kont) => fun (pv : Val) => walkKont(k2)(ko)(pv)
          | Kont.khEval(b, e, k2)    => fun (ko : Kont) => fun (pv : Val) => walkKont(k2)(ko)(pv)
          | Kont.kresume(rv, k2)     => fun (ko : Kont) => fun (pv : Val) => walkKont(k2)(ko)(pv)
        }
    }

    fn isFinal(s: State) -> Bool {
        match s { | State.sdone(v) => Bool.true | State.sstuck => Bool.true
                 | State.seval(t, e, k) => Bool.false | State.sret(v, k) => Bool.false }
    }

    -- THE TRANSITION. One clause per (control shape) and per (continuation frame); a total
    -- function and a *single* step — no search (the search lives in `walkKont`, invoked once
    -- per performed operation), no substitution.
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
                      | Val.vkont(kr) => State.sret v kr            -- applying a resumption: jump to it
                      | Val.vnat(n) => State.sstuck
                    }
                | Kont.kadd1(env, y, k2) =>
                    match v {
                      | Val.vnat(m) => State.seval y env (Kont.kadd2 m k2)
                      | Val.vclos(cenv, body) => State.sstuck
                      | Val.vkont(kk) => State.sstuck
                    }
                | Kont.kadd2(m, k2) =>
                    match v {
                      | Val.vnat(n) => State.sret (Val.vnat (addN(m)(n))) k2
                      | Val.vclos(cenv, body) => State.sstuck
                      | Val.vkont(kk) => State.sstuck
                    }
                | Kont.kifz(env, t2, e2, k2) =>
                    match v {
                      | Val.vnat(n) => match n { | Nat.zero => State.seval t2 env k2 | Nat.succ(m) => State.seval e2 env k2 }
                      | Val.vclos(cenv, body) => State.sstuck
                      | Val.vkont(kk) => State.sstuck
                    }
                | Kont.kop(k2) => walkKont(k2)(k2)(v)                -- payload evaluated: find handler, resume = k2
                | Kont.khEval(body, env2, k2) => State.seval body env2 (Kont.khandle v k2)  -- handler ready; run body
                | Kont.khandle(vh, k2) => State.sret v k2            -- body finished normally: discard the handler
                | Kont.kresume(rv, k2) =>
                    match v {
                      | Val.vclos(cenv, body) => State.seval body (Env.econs rv cenv) k2  -- apply (λresume. …) to the resumption
                      | Val.vkont(kr) => State.sret rv kr
                      | Val.vnat(n) => State.sstuck
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

    -- Load a closed term into the initial state (empty environment), and read a number out
    -- of a final state.
    def load (t : Tm) : State := State.seval t Env.enil Kont.kdone
    def evalNat (fuel : Nat) (t : Tm) : Nat :=
      match run(fuel)(load(t)) {
        | State.sdone(v) => match v { | Val.vnat(n) => n | Val.vclos(env, b) => Nat.zero | Val.vkont(k) => Nat.zero }
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

    -- Running a final state for any amount of fuel leaves it unchanged.
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

    -- ===== Driver adequacy: fuel composes, and answers are stable under more fuel. =====
    -- These make "the machine's result" well-defined: once `run` reaches a final state, no
    -- amount of extra fuel changes it. (The full machine-vs-small-step *simulation* — that
    -- the machine computes the answer an independent semantics assigns — is a larger
    -- development and is NOT proved here.)
    def congrArg.{u, v} (A : Sort u) (B : Sort v) (f : A -> B) (a : A) (b : A) (h : Eq.{u} A a b)
      : Eq.{v} B (f a) (f b) :=
      Eq.subst.{u} A (fun (x : A) => Eq.{v} B (f a) (f x)) a b h (Eq.refl.{v} B (f a))

    inductive Or2 (A : Prop) (B : Prop) : Prop | inl : A -> Or2 A B | inr : B -> Or2 A B
    def bcases (b : Bool) : Or2 (Eq.{1} Bool b Bool.true) (Eq.{1} Bool b Bool.false) :=
      Bool.rec.{0} (fun (x : Bool) => Or2 (Eq.{1} Bool x Bool.true) (Eq.{1} Bool x Bool.false))
        (Or2.inr (Eq.{1} Bool Bool.false Bool.true) (Eq.{1} Bool Bool.false Bool.false) (Eq.refl.{1} Bool Bool.false))
        (Or2.inl (Eq.{1} Bool Bool.true Bool.true) (Eq.{1} Bool Bool.true Bool.false) (Eq.refl.{1} Bool Bool.true))
        b

    -- One unfolding of `run` on a non-final state: `run (succ x) s = run x (step s)`.
    def run_succ_step (x : Nat) (s : State) (hf : Eq.{1} Bool (isFinal s) Bool.false)
      : Eq.{1} State (run (Nat.succ x) s) (run x (step s)) :=
      Eq.subst.{1} Bool
        (fun (b : Bool) =>
           Eq.{1} State (match b { | Bool.true => s | Bool.false => run(x)(step(s)) }) (run x (step s)))
        Bool.false (isFinal s) (Eq.symm.{1} Bool (isFinal s) Bool.false hf)
        (Eq.refl.{1} State (run x (step s)))

    -- FUEL COMPOSITION: run (n + m) s = run m (run n s). By induction on n, splitting on
    -- whether `s` is already final (then both sides collapse via `run_final_fix`) or not
    -- (then one `step` is shared and the tail follows by the IH).
    fn run_compose(n: Nat)
      -> ((m : Nat) -> (s : State) -> Eq.{1} State (run (addN(n)(m)) s) (run m (run n s))) {
        match n {
          | Nat.zero => fun (m : Nat) (s : State) => Eq.refl.{1} State (run m s)
          | Nat.succ(n2) => fun (m : Nat) (s : State) =>
              match bcases(isFinal s) {
                | Or2.inl(htrue) =>
                    Eq.trans.{1} State (run (addN(Nat.succ(n2))(m)) s) s (run m (run (Nat.succ n2) s))
                      (run_final_fix (addN(Nat.succ(n2))(m)) s htrue)
                      (Eq.symm.{1} State (run m (run (Nat.succ n2) s)) s
                        (Eq.trans.{1} State (run m (run (Nat.succ n2) s)) (run m s) s
                          (congrArg.{1, 1} State State (fun (x : State) => run m x)
                             (run (Nat.succ n2) s) s (run_final_fix (Nat.succ n2) s htrue))
                          (run_final_fix m s htrue)))
                | Or2.inr(hfalse) =>
                    Eq.trans.{1} State (run (addN(Nat.succ(n2))(m)) s) (run (addN(n2)(m)) (step s)) (run m (run (Nat.succ n2) s))
                      (run_succ_step (addN(n2)(m)) s hfalse)
                      (Eq.trans.{1} State (run (addN(n2)(m)) (step s)) (run m (run n2 (step s))) (run m (run (Nat.succ n2) s))
                        (run_compose(n2)(m)(step s))
                        (congrArg.{1, 1} State State (fun (x : State) => run m x)
                           (run n2 (step s)) (run (Nat.succ n2) s)
                           (Eq.symm.{1} State (run (Nat.succ n2) s) (run n2 (step s)) (run_succ_step n2 s hfalse))))
              }
        }
    }

    -- ANSWER STABILITY: if `run n s` is final, running `n + m` fuel gives the same answer.
    def run_stable (n : Nat) (m : Nat) (s : State) (h : Eq.{1} Bool (isFinal (run n s)) Bool.true)
      : Eq.{1} State (run (addN(n)(m)) s) (run n s) :=
      Eq.trans.{1} State (run (addN(n)(m)) s) (run m (run n s)) (run n s)
        (run_compose(n)(m)(s))
        (run_final_fix m (run n s) h)
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

/// **Machine type-safety for the pure fragment.** A simple type system for `Tm`
/// (`var`/`lit`/`lam`/`app`/`add`/`ifz` — `op`/`handle` are deliberately left *untypable*,
/// so a well-typed program never performs an effect), lifted to the machine's runtime
/// objects: value typing `HasTyV` and environment typing `HasTyE` (mutual), continuation
/// typing `HasTyK k A B` ("feeding an `A` into `k` yields a final answer of type `B`"), and
/// state typing `HasTyS`. The payoff theorem is **preservation** (`step` preserves the
/// answer type) — and because the stuck state `sstuck` has *no* typing rule, preservation
/// alone says **a well-typed state never gets stuck**.
pub const SAFETY: &str = r#"
    -- Object types and typing contexts (de Bruijn).
    inductive Ty : Type | tnat : Ty | tarr : Ty -> Ty -> Ty
    inductive Ctx : Type | cnil : Ctx | ccons : Ty -> Ctx -> Ctx

    -- de Bruijn lookup in the context.
    inductive Lookup : Ctx -> Nat -> Ty -> Prop
      | here  : (G : Ctx) -> (A : Ty) -> Lookup (Ctx.ccons A G) Nat.zero A
      | there : (G : Ctx) -> (A : Ty) -> (B : Ty) -> (n : Nat)
                  -> Lookup G n A -> Lookup (Ctx.ccons B G) (Nat.succ n) A

    -- The typing relation for terms (the pure fragment; no rule for op/handle).
    inductive HasTy : Ctx -> Tm -> Ty -> Prop
      | tvar : (G : Ctx) -> (n : Nat) -> (A : Ty) -> Lookup G n A -> HasTy G (Tm.var n) A
      | tlit : (G : Ctx) -> (n : Nat) -> HasTy G (Tm.lit n) Ty.tnat
      | tlam : (G : Ctx) -> (A : Ty) -> (B : Ty) -> (b : Tm)
                 -> HasTy (Ctx.ccons A G) b B -> HasTy G (Tm.lam b) (Ty.tarr A B)
      | tapp : (G : Ctx) -> (f : Tm) -> (a : Tm) -> (A : Ty) -> (B : Ty)
                 -> HasTy G f (Ty.tarr A B) -> HasTy G a A -> HasTy G (Tm.app f a) B
      | tadd : (G : Ctx) -> (x : Tm) -> (y : Tm)
                 -> HasTy G x Ty.tnat -> HasTy G y Ty.tnat -> HasTy G (Tm.add x y) Ty.tnat
      | tifz : (G : Ctx) -> (c : Tm) -> (t : Tm) -> (e : Tm) -> (A : Ty)
                 -> HasTy G c Ty.tnat -> HasTy G t A -> HasTy G e A -> HasTy G (Tm.ifz c t e) A

    -- Value typing and environment typing. Indexed *mutual* inductives are unsupported, and
    -- the pointwise (∀-under-binder) formulation is a W-type (also unsupported). So both
    -- relations live in ONE non-mutual indexed inductive `HasTyVE` over the sums `VE`
    -- (Val|Env) and `TC` (Ty|Ctx): a value typing and an environment typing are the two
    -- injections. The recursive occurrences are finitary and strictly positive. No rule for
    -- `vkont` — a reified continuation is never well-typed in the pure fragment.
    inductive VE : Type | injv : Val -> VE | inje : Env -> VE
    inductive TC : Type | injt : Ty -> TC | injc : Ctx -> TC
    inductive HasTyVE : VE -> TC -> Prop
      | vtnat  : (n : Nat) -> HasTyVE (VE.injv (Val.vnat n)) (TC.injt Ty.tnat)
      | vtclos : (env : Env) -> (G : Ctx) -> (b : Tm) -> (A : Ty) -> (B : Ty)
                   -> HasTyVE (VE.inje env) (TC.injc G) -> HasTy (Ctx.ccons A G) b B
                   -> HasTyVE (VE.injv (Val.vclos env b)) (TC.injt (Ty.tarr A B))
      | etnil  : HasTyVE (VE.inje Env.enil) (TC.injc Ctx.cnil)
      | etcons : (v : Val) -> (A : Ty) -> (rest : Env) -> (G : Ctx)
                   -> HasTyVE (VE.injv v) (TC.injt A) -> HasTyVE (VE.inje rest) (TC.injc G)
                   -> HasTyVE (VE.inje (Env.econs v rest)) (TC.injc (Ctx.ccons A G))
    def HasTyV (v : Val) (A : Ty) : Prop := HasTyVE (VE.injv v) (TC.injt A)
    def HasTyE (env : Env) (G : Ctx) : Prop := HasTyVE (VE.inje env) (TC.injc G)

    -- Continuation typing: `HasTyK k A B` means "given a value of type A, the continuation
    -- k runs to a final answer of type B". One rule per (typable) frame; the effect frames
    -- kop/khEval/khandle/kresume have no rule.
    inductive HasTyK : Kont -> Ty -> Ty -> Prop
      | ktdone : (A : Ty) -> HasTyK Kont.kdone A A
      | ktapp1 : (env : Env) -> (G : Ctx) -> (a : Tm) -> (C : Ty) -> (D : Ty) -> (B : Ty) -> (k2 : Kont)
                   -> HasTyE env G -> HasTy G a C -> HasTyK k2 D B
                   -> HasTyK (Kont.kapp1 env a k2) (Ty.tarr C D) B
      | ktapp2 : (vf : Val) -> (C : Ty) -> (D : Ty) -> (B : Ty) -> (k2 : Kont)
                   -> HasTyV vf (Ty.tarr C D) -> HasTyK k2 D B
                   -> HasTyK (Kont.kapp2 vf k2) C B
      | ktadd1 : (env : Env) -> (G : Ctx) -> (y : Tm) -> (B : Ty) -> (k2 : Kont)
                   -> HasTyE env G -> HasTy G y Ty.tnat -> HasTyK k2 Ty.tnat B
                   -> HasTyK (Kont.kadd1 env y k2) Ty.tnat B
      | ktadd2 : (m : Nat) -> (B : Ty) -> (k2 : Kont)
                   -> HasTyK k2 Ty.tnat B -> HasTyK (Kont.kadd2 m k2) Ty.tnat B
      | ktifz  : (env : Env) -> (G : Ctx) -> (t : Tm) -> (e : Tm) -> (A : Ty) -> (B : Ty) -> (k2 : Kont)
                   -> HasTyE env G -> HasTy G t A -> HasTy G e A -> HasTyK k2 A B
                   -> HasTyK (Kont.kifz env t e k2) Ty.tnat B

    -- State typing: a state runs to a final answer of type B. No rule for `sstuck`.
    inductive HasTyS : State -> Ty -> Prop
      | stseval : (t : Tm) -> (env : Env) -> (G : Ctx) -> (k : Kont) -> (A : Ty) -> (B : Ty)
                    -> HasTyE env G -> HasTy G t A -> HasTyK k A B -> HasTyS (State.seval t env k) B
      | stsret  : (v : Val) -> (k : Kont) -> (A : Ty) -> (B : Ty)
                    -> HasTyV v A -> HasTyK k A B -> HasTyS (State.sret v k) B
      | stsdone : (v : Val) -> (B : Ty) -> HasTyV v B -> HasTyS (State.sdone v) B
"#;

/// **Inversion infrastructure** for value typing. Because `HasTyV`/`HasTyE` share the
/// `HasTyVE` inductive through the `VE`/`TC` injections, a plain `match` on a value-typing
/// proof cannot refine the underlying value (its index is `injv v`, not `v`). So the
/// canonical-forms lemmas use the standard inversion-via-equalities trick — generalise the
/// indices, then recover the value with `injv`-injectivity and rule out the impossible
/// constructors with no-confusion. The results are packaged in `NatInv`/`ClosInv`, whose
/// indices are the value *directly*, so the preservation proof can `match` them cleanly.
pub const SAFETY_INV: &str = r#"
    def congrArg.{u, v} (A : Sort u) (B : Sort v) (f : A -> B) (a : A) (b : A) (h : Eq.{u} A a b)
      : Eq.{v} B (f a) (f b) := Eq.subst.{u} A (fun (x : A) => Eq.{v} B (f a) (f x)) a b h (Eq.refl.{v} B (f a))

    -- No-confusion: the VE / TC injections and the Ty constructors are distinct.
    def veIsV (w : VE) : Prop := match w { | VE.injv(x) => True | VE.inje(y) => False }
    def ve_nc (e : Env) (v : Val) (h : Eq.{1} VE (VE.inje e) (VE.injv v)) : False :=
      Eq.subst.{1} VE veIsV (VE.injv v) (VE.inje e) (Eq.symm.{1} VE (VE.inje e) (VE.injv v) h) True.intro
    def tyIsNat (t : Ty) : Prop := match t { | Ty.tnat => True | Ty.tarr(a, b) => False }
    def ty_nc (a : Ty) (b : Ty) (h : Eq.{1} Ty (Ty.tarr a b) Ty.tnat) : False :=
      Eq.subst.{1} Ty tyIsNat Ty.tnat (Ty.tarr a b) (Eq.symm.{1} Ty (Ty.tarr a b) Ty.tnat h) True.intro

    -- Injectivity of the injections and of `tarr`, via projection + congrArg.
    def unInjv (w : VE) (d : Val) : Val := match w { | VE.injv(x) => x | VE.inje(y) => d }
    def injv_inj (a : Val) (b : Val) (h : Eq.{1} VE (VE.injv a) (VE.injv b)) : Eq.{1} Val a b :=
      congrArg.{1, 1} VE Val (fun (w : VE) => unInjv w a) (VE.injv a) (VE.injv b) h
    def unInjt (w : TC) (d : Ty) : Ty := match w { | TC.injt(x) => x | TC.injc(y) => d }
    def injt_inj (a : Ty) (b : Ty) (h : Eq.{1} TC (TC.injt a) (TC.injt b)) : Eq.{1} Ty a b :=
      congrArg.{1, 1} TC Ty (fun (w : TC) => unInjt w a) (TC.injt a) (TC.injt b) h
    def tarrDom (t : Ty) (d : Ty) : Ty := match t { | Ty.tnat => d | Ty.tarr(a, b) => a }
    def tarrCod (t : Ty) (d : Ty) : Ty := match t { | Ty.tnat => d | Ty.tarr(a, b) => b }
    def tarr_inj_dom (a : Ty) (b : Ty) (c : Ty) (d : Ty) (h : Eq.{1} Ty (Ty.tarr a b) (Ty.tarr c d)) : Eq.{1} Ty a c :=
      congrArg.{1, 1} Ty Ty (fun (t : Ty) => tarrDom t a) (Ty.tarr a b) (Ty.tarr c d) h
    def tarr_inj_cod (a : Ty) (b : Ty) (c : Ty) (d : Ty) (h : Eq.{1} Ty (Ty.tarr a b) (Ty.tarr c d)) : Eq.{1} Ty b d :=
      congrArg.{1, 1} Ty Ty (fun (t : Ty) => tarrCod t b) (Ty.tarr a b) (Ty.tarr c d) h

    -- Canonical-form packages (indexed by the value directly).
    inductive NatInv : Val -> Prop | mkN : (n : Nat) -> NatInv (Val.vnat n)
    inductive ClosInv : Val -> Ty -> Ty -> Prop
      | mkC : (cenv : Env) -> (G : Ctx) -> (body : Tm) -> (C : Ty) -> (D : Ty)
                -> HasTyE cenv G -> HasTy (Ctx.ccons C G) body D -> ClosInv (Val.vclos cenv body) C D

    -- A well-typed value of type `tnat` is a `vnat`.
    def hvNat (ve : VE) (tc : TC) (h : HasTyVE ve tc)
      : (v : Val) -> Eq.{1} VE ve (VE.injv v) -> Eq.{1} TC tc (TC.injt Ty.tnat) -> NatInv v :=
      match h {
        | HasTyVE.vtnat(n) => fun (v : Val) (ev : Eq.{1} VE (VE.injv (Val.vnat n)) (VE.injv v)) (et : Eq.{1} TC (TC.injt Ty.tnat) (TC.injt Ty.tnat)) =>
            Eq.subst.{1} Val NatInv (Val.vnat n) v (injv_inj (Val.vnat n) v ev) (NatInv.mkN n)
        | HasTyVE.vtclos(env, G, b, A, B, he, hb) => fun (v : Val) (ev : Eq.{1} VE (VE.injv (Val.vclos env b)) (VE.injv v)) (et : Eq.{1} TC (TC.injt (Ty.tarr A B)) (TC.injt Ty.tnat)) =>
            False.rec.{0} (fun (_ : False) => NatInv v) (ty_nc A B (injt_inj (Ty.tarr A B) Ty.tnat et))
        | HasTyVE.etnil => fun (v : Val) (ev : Eq.{1} VE (VE.inje Env.enil) (VE.injv v)) (et : Eq.{1} TC (TC.injc Ctx.cnil) (TC.injt Ty.tnat)) =>
            False.rec.{0} (fun (_ : False) => NatInv v) (ve_nc Env.enil v ev)
        | HasTyVE.etcons(v2, A2, rest, G2, hv2, he2) => fun (v : Val) (ev : Eq.{1} VE (VE.inje (Env.econs v2 rest)) (VE.injv v)) (et : Eq.{1} TC (TC.injc (Ctx.ccons A2 G2)) (TC.injt Ty.tnat)) =>
            False.rec.{0} (fun (_ : False) => NatInv v) (ve_nc (Env.econs v2 rest) v ev)
      }
    def canonNat (v : Val) (h : HasTyV v Ty.tnat) : NatInv v :=
      hvNat (VE.injv v) (TC.injt Ty.tnat) h v (Eq.refl.{1} VE (VE.injv v)) (Eq.refl.{1} TC (TC.injt Ty.tnat))

    -- A well-typed value of type `tarr C D` is a closure with a well-typed env and body.
    def hvArr (ve : VE) (tc : TC) (h : HasTyVE ve tc)
      : (v : Val) -> (C : Ty) -> (D : Ty) -> Eq.{1} VE ve (VE.injv v) -> Eq.{1} TC tc (TC.injt (Ty.tarr C D)) -> ClosInv v C D :=
      match h {
        | HasTyVE.vtnat(n) => fun (v : Val) (C : Ty) (D : Ty) (ev : Eq.{1} VE (VE.injv (Val.vnat n)) (VE.injv v)) (et : Eq.{1} TC (TC.injt Ty.tnat) (TC.injt (Ty.tarr C D))) =>
            False.rec.{0} (fun (_ : False) => ClosInv v C D) (ty_nc C D (Eq.symm.{1} Ty Ty.tnat (Ty.tarr C D) (injt_inj Ty.tnat (Ty.tarr C D) et)))
        | HasTyVE.vtclos(env, G, b, A, B, he, hb) => fun (v : Val) (C : Ty) (D : Ty) (ev : Eq.{1} VE (VE.injv (Val.vclos env b)) (VE.injv v)) (et : Eq.{1} TC (TC.injt (Ty.tarr A B)) (TC.injt (Ty.tarr C D))) =>
            Eq.subst.{1} Val (fun (w : Val) => ClosInv w C D) (Val.vclos env b) v (injv_inj (Val.vclos env b) v ev)
              (Eq.subst.{1} Ty (fun (cc : Ty) => ClosInv (Val.vclos env b) cc D) A C (tarr_inj_dom A B C D (injt_inj (Ty.tarr A B) (Ty.tarr C D) et))
                (Eq.subst.{1} Ty (fun (dd : Ty) => ClosInv (Val.vclos env b) A dd) B D (tarr_inj_cod A B C D (injt_inj (Ty.tarr A B) (Ty.tarr C D) et))
                  (ClosInv.mkC env G b A B he hb)))
        | HasTyVE.etnil => fun (v : Val) (C : Ty) (D : Ty) (ev : Eq.{1} VE (VE.inje Env.enil) (VE.injv v)) (et : Eq.{1} TC (TC.injc Ctx.cnil) (TC.injt (Ty.tarr C D))) =>
            False.rec.{0} (fun (_ : False) => ClosInv v C D) (ve_nc Env.enil v ev)
        | HasTyVE.etcons(v2, A2, rest, G2, hv2, he2) => fun (v : Val) (C : Ty) (D : Ty) (ev : Eq.{1} VE (VE.inje (Env.econs v2 rest)) (VE.injv v)) (et : Eq.{1} TC (TC.injc (Ctx.ccons A2 G2)) (TC.injt (Ty.tarr C D))) =>
            False.rec.{0} (fun (_ : False) => ClosInv v C D) (ve_nc (Env.econs v2 rest) v ev)
      }
    def canonArr (v : Val) (C : Ty) (D : Ty) (h : HasTyV v (Ty.tarr C D)) : ClosInv v C D :=
      hvArr (VE.injv v) (TC.injt (Ty.tarr C D)) h v C D (Eq.refl.{1} VE (VE.injv v)) (Eq.refl.{1} TC (TC.injt (Ty.tarr C D)))
"#;

/// The machine session plus the [`SAFETY`] type system (relations only; the metatheory
/// proofs are layered on top in further sessions).
pub fn safety_session() -> Result<Session, String> {
    let mut s = session()?;
    s.run(SAFETY)?;
    Ok(s)
}

/// **Environment-typing inversion.** `envConsInv` inverts an environment typed at a
/// non-empty context into a typed head + typed tail (the same VE/TC equations technique as
/// the value canonical forms), with the supporting no-confusion / injectivity facts for the
/// `inje`/`injc` injections and the `Ctx` constructors. This is the inversion the
/// environment-lookup lemma (and the `var` case of preservation) is built from.
pub const SAFETY_LOOKUP: &str = r#"
    def unInje (w : VE) (d : Env) : Env := match w { | VE.injv(x) => d | VE.inje(y) => y }
    def inje_inj (a : Env) (b : Env) (h : Eq.{1} VE (VE.inje a) (VE.inje b)) : Eq.{1} Env a b :=
      congrArg.{1, 1} VE Env (fun (w : VE) => unInje w a) (VE.inje a) (VE.inje b) h
    def unInjc (w : TC) (d : Ctx) : Ctx := match w { | TC.injt(x) => d | TC.injc(y) => y }
    def injc_inj (a : Ctx) (b : Ctx) (h : Eq.{1} TC (TC.injc a) (TC.injc b)) : Eq.{1} Ctx a b :=
      congrArg.{1, 1} TC Ctx (fun (w : TC) => unInjc w a) (TC.injc a) (TC.injc b) h
    def ctxIsCons (c : Ctx) : Prop := match c { | Ctx.cnil => False | Ctx.ccons(A, G) => True }
    def ctx_nc (A : Ty) (G : Ctx) (h : Eq.{1} Ctx (Ctx.ccons A G) Ctx.cnil) : False :=
      Eq.subst.{1} Ctx ctxIsCons (Ctx.ccons A G) Ctx.cnil h True.intro
    def cconsHd (c : Ctx) (d : Ty) : Ty := match c { | Ctx.cnil => d | Ctx.ccons(A, G) => A }
    def cconsTl (c : Ctx) (d : Ctx) : Ctx := match c { | Ctx.cnil => d | Ctx.ccons(A, G) => G }
    def ccons_inj_hd (A : Ty) (G : Ctx) (A2 : Ty) (G2 : Ctx) (h : Eq.{1} Ctx (Ctx.ccons A G) (Ctx.ccons A2 G2)) : Eq.{1} Ty A A2 :=
      congrArg.{1, 1} Ctx Ty (fun (c : Ctx) => cconsHd c A) (Ctx.ccons A G) (Ctx.ccons A2 G2) h
    def ccons_inj_tl (A : Ty) (G : Ctx) (A2 : Ty) (G2 : Ctx) (h : Eq.{1} Ctx (Ctx.ccons A G) (Ctx.ccons A2 G2)) : Eq.{1} Ctx G G2 :=
      congrArg.{1, 1} Ctx Ctx (fun (c : Ctx) => cconsTl c G) (Ctx.ccons A G) (Ctx.ccons A2 G2) h

    -- Invert an environment typed at a non-empty context: it is an `econs` of a typed head
    -- and a typed tail.
    inductive EnvConsInv : Env -> Ty -> Ctx -> Prop
      | mkE : (v : Val) -> (A : Ty) -> (rest : Env) -> (G : Ctx)
                -> HasTyV v A -> HasTyE rest G -> EnvConsInv (Env.econs v rest) A G
    def heInv (ve : VE) (tc : TC) (h : HasTyVE ve tc)
      : (env : Env) -> (A : Ty) -> (G : Ctx) -> Eq.{1} VE ve (VE.inje env) -> Eq.{1} TC tc (TC.injc (Ctx.ccons A G)) -> EnvConsInv env A G :=
      match h {
        | HasTyVE.vtnat(n) => fun (env : Env) (A : Ty) (G : Ctx) (ev : Eq.{1} VE (VE.injv (Val.vnat n)) (VE.inje env)) (et : Eq.{1} TC (TC.injt Ty.tnat) (TC.injc (Ctx.ccons A G))) =>
            False.rec.{0} (fun (_ : False) => EnvConsInv env A G) (ve_nc env (Val.vnat n) (Eq.symm.{1} VE (VE.injv (Val.vnat n)) (VE.inje env) ev))
        | HasTyVE.vtclos(env2, G2, b, A2, B2, he, hb) => fun (env : Env) (A : Ty) (G : Ctx) (ev : Eq.{1} VE (VE.injv (Val.vclos env2 b)) (VE.inje env)) (et : Eq.{1} TC (TC.injt (Ty.tarr A2 B2)) (TC.injc (Ctx.ccons A G))) =>
            False.rec.{0} (fun (_ : False) => EnvConsInv env A G) (ve_nc env (Val.vclos env2 b) (Eq.symm.{1} VE (VE.injv (Val.vclos env2 b)) (VE.inje env) ev))
        | HasTyVE.etnil => fun (env : Env) (A : Ty) (G : Ctx) (ev : Eq.{1} VE (VE.inje Env.enil) (VE.inje env)) (et : Eq.{1} TC (TC.injc Ctx.cnil) (TC.injc (Ctx.ccons A G))) =>
            False.rec.{0} (fun (_ : False) => EnvConsInv env A G) (ctx_nc A G (Eq.symm.{1} Ctx Ctx.cnil (Ctx.ccons A G) (injc_inj Ctx.cnil (Ctx.ccons A G) et)))
        | HasTyVE.etcons(v2, A2, rest2, G2, hv2, he2) => fun (env : Env) (A : Ty) (G : Ctx) (ev : Eq.{1} VE (VE.inje (Env.econs v2 rest2)) (VE.inje env)) (et : Eq.{1} TC (TC.injc (Ctx.ccons A2 G2)) (TC.injc (Ctx.ccons A G))) =>
            Eq.subst.{1} Env (fun (e : Env) => EnvConsInv e A G) (Env.econs v2 rest2) env (inje_inj (Env.econs v2 rest2) env ev)
              (Eq.subst.{1} Ty (fun (aa : Ty) => EnvConsInv (Env.econs v2 rest2) aa G) A2 A (ccons_inj_hd A2 G2 A G (injc_inj (Ctx.ccons A2 G2) (Ctx.ccons A G) et))
                (Eq.subst.{1} Ctx (fun (gg : Ctx) => EnvConsInv (Env.econs v2 rest2) A2 gg) G2 G (ccons_inj_tl A2 G2 A G (injc_inj (Ctx.ccons A2 G2) (Ctx.ccons A G) et))
                  (EnvConsInv.mkE v2 A2 rest2 G2 hv2 he2)))
      }
    def envConsInv (env : Env) (A : Ty) (G : Ctx) (h : HasTyE env (Ctx.ccons A G)) : EnvConsInv env A G :=
      heInv (VE.inje env) (TC.injc (Ctx.ccons A G)) h env A G (Eq.refl.{1} VE (VE.inje env)) (Eq.refl.{1} TC (TC.injc (Ctx.ccons A G)))

"#;

/// The safety session plus the [`SAFETY_INV`] inversion infrastructure (canonical forms).
pub fn inv_session() -> Result<Session, String> {
    let mut s = safety_session()?;
    s.run(SAFETY_INV)?;
    Ok(s)
}

/// The inversion session plus the [`SAFETY_LOOKUP`] environment-typing inversion.
pub fn lookup_session() -> Result<Session, String> {
    let mut s = inv_session()?;
    s.run(SAFETY_LOOKUP)?;
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
    fn machine_type_system_kernel_checks() {
        // The type system for the CEK machine (term typing + value/env typing via the VE/TC
        // encoding + continuation + state typing) is well-formed and kernel-checked.
        let s = safety_session().expect("machine type system should kernel-check");
        for n in ["HasTy", "HasTyVE", "HasTyV", "HasTyE", "HasTyK", "HasTyS"] {
            assert!(s.k.env().contains(n), "missing relation: {n}");
        }
    }

    #[test]
    fn canonical_forms_and_inversions_kernel_check() {
        // The value canonical forms (a well-typed `tnat` value is a `vnat`; a `tarr` value is
        // a closure with a well-typed env+body) and the environment-typing inversion are
        // verified — the inversion infrastructure the preservation proof is built from.
        let s = lookup_session().expect("inversion infrastructure should kernel-check");
        for n in ["canonNat", "canonArr", "envConsInv", "injv_inj", "ve_nc"] {
            assert!(s.k.env().contains(n), "missing lemma: {n}");
        }
    }

    #[test]
    fn driver_metatheory_kernel_checks() {
        // The fixed-point theorems (step_final, run_final_fix) are verified by the kernel.
        let s = meta_session().expect("driver metatheory should kernel-check");
        assert!(s.k.env().contains("step_final"));
        assert!(s.k.env().contains("run_final_fix"));
        // Driver adequacy: fuel composes and answers are stable under more fuel.
        assert!(s.k.env().contains("run_compose"));
        assert!(s.k.env().contains("run_stable"));
    }
}
