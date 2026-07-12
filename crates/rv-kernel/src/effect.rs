//! Algebraic effects, the call-by-push-value way: **values** (the kernel) beside
//! **computations** (this module).
//!
//! The kernel is the pure value/logic world. A *computation* may additionally perform
//! effects (`div`, `panic`, `io`, `st`, …), tracked in an **effect row**. The rules
//! that matter:
//!
//! * **sequencing unions** the rows (doing `a` then `b` may do either's effects),
//! * a **handler discharges** a label (and a handler *is* a capability — granting the
//!   right to perform that effect),
//! * **purity = the empty row**, and a pure computation embeds back into the kernel as
//!   a value. This is the spec/exec boundary with no keyword: a function admissible as
//!   *logic* (a `spec`) is exactly one whose computation is pure; an *exec* function
//!   has a non-empty row.
//!
//! Capability sandboxing falls out: a computation can run only under a set of granted
//! handlers that covers its row; handle everything and the row is empty — provably
//! incapable of any effect.
//!
//! Scope: this is the effect-*row* discipline + the value/computation split +
//! handler/capability checking. A full dependent operational semantics for handlers
//! is future work; what's here is the type-level skeleton the surface compiles to.

use rv_kernel_core::term::Term;
use std::collections::BTreeSet;

/// An effect label.
pub type Effect = String;

/// A set of latent effects.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct EffRow(BTreeSet<Effect>);

impl EffRow {
    pub fn empty() -> Self {
        EffRow(BTreeSet::new())
    }
    pub fn single(e: &str) -> Self {
        EffRow([e.to_string()].into_iter().collect())
    }
    pub fn of(labels: &[&str]) -> Self {
        EffRow(labels.iter().map(|s| s.to_string()).collect())
    }
    pub fn union(&self, other: &EffRow) -> EffRow {
        EffRow(self.0.union(&other.0).cloned().collect())
    }
    pub fn remove(&self, e: &str) -> EffRow {
        let mut s = self.0.clone();
        s.remove(e);
        EffRow(s)
    }
    pub fn contains(&self, e: &str) -> bool {
        self.0.contains(e)
    }
    /// Is the row empty — i.e. is the computation pure (admissible as logic)?
    pub fn is_pure(&self) -> bool {
        self.0.is_empty()
    }
    /// Is every effect of `self` covered by the `granted` capabilities?
    pub fn covered_by(&self, granted: &EffRow) -> bool {
        self.0.is_subset(&granted.0)
    }
    pub fn labels(&self) -> impl Iterator<Item = &str> {
        self.0.iter().map(String::as_str)
    }
}

/// A computation. `Return` injects a kernel value (the pure fragment); the other
/// constructors add or discharge effects.
#[derive(Clone, Debug)]
pub enum Comp {
    /// Return a pure value — empty effect row. This is the embedding of the kernel
    /// value world into computations.
    Return(Term),
    /// Perform an operation of the given effect, then continue.
    Perform(Effect, Box<Comp>),
    /// Sequence: run the first, then the second (their rows union).
    Seq(Box<Comp>, Box<Comp>),
    /// Branch on a (boolean) value; the row is the union of the two arms.
    Cond(Term, Box<Comp>, Box<Comp>),
    /// Handle (discharge) an effect — removes that label from the row. A handler is a
    /// capability: it grants the right to that effect and eliminates it.
    Handle(Effect, Box<Comp>),
}

impl Comp {
    pub fn ret(v: Term) -> Comp {
        Comp::Return(v)
    }
    pub fn perform(e: &str, k: Comp) -> Comp {
        Comp::Perform(e.to_string(), Box::new(k))
    }
    pub fn seq(a: Comp, b: Comp) -> Comp {
        Comp::Seq(Box::new(a), Box::new(b))
    }
    pub fn cond(c: Term, a: Comp, b: Comp) -> Comp {
        Comp::Cond(c, Box::new(a), Box::new(b))
    }
    pub fn handle(e: &str, c: Comp) -> Comp {
        Comp::Handle(e.to_string(), Box::new(c))
    }

    /// The latent effect row of this computation.
    pub fn effect(&self) -> EffRow {
        match self {
            Comp::Return(_) => EffRow::empty(),
            Comp::Perform(e, k) => EffRow::single(e).union(&k.effect()),
            Comp::Seq(a, b) => a.effect().union(&b.effect()),
            Comp::Cond(_, a, b) => a.effect().union(&b.effect()),
            Comp::Handle(e, c) => c.effect().remove(e),
        }
    }

    /// Pure ⇔ empty row ⇔ admissible as logic / a `spec`.
    pub fn is_pure(&self) -> bool {
        self.effect().is_pure()
    }

    /// Runnable under a granted capability set?
    pub fn runnable_under(&self, granted: &EffRow) -> bool {
        self.effect().covered_by(granted)
    }

    /// Reflect a **pure** computation back into the kernel value world. `None` if the
    /// computation has any *un-discharged* effect — that is precisely the gate stopping
    /// effectful code from being used as logic. When the whole computation is pure,
    /// descend to the value it returns.
    pub fn as_value(&self) -> Option<Term> {
        if !self.is_pure() {
            return None;
        }
        self.trailing_return()
    }

    /// The value ultimately returned, peeling handlers/ops/sequencing. Only meaningful
    /// once [`Comp::is_pure`] holds.
    fn trailing_return(&self) -> Option<Term> {
        match self {
            Comp::Return(v) => Some(v.clone()),
            Comp::Handle(_, c) | Comp::Perform(_, c) => c.trailing_return(),
            Comp::Seq(_, b) => b.trailing_return(),
            Comp::Cond(..) => None, // would need evaluation; out of scope for the skeleton
        }
    }

    /// Sandbox: discharge every effect in `caps`, yielding a computation whose row is
    /// guaranteed disjoint from `caps`. Handling *all* of a computation's effects makes
    /// it provably pure.
    pub fn sandbox(self, caps: &EffRow) -> Comp {
        let mut c = self;
        for e in caps.labels() {
            c = Comp::handle(e, c);
        }
        c
    }
}

// ---------------------------------------------------------------------------
// Operational semantics: deep handlers with resumptions.
// ---------------------------------------------------------------------------

/// A computation in continuation-passing form, ready to be *run* by a handler. An
/// operation `Perform(op, arg, k)` performs `op` with argument `arg` and continues as
/// `k`, which is a computation under one extra binder — the operation's **result**,
/// referenced inside `k` as de Bruijn `Var(0)`.
#[derive(Clone, Debug)]
pub enum Prog {
    Return(Term),
    Perform(String, Term, Box<Prog>),
}

impl Prog {
    pub fn ret(v: Term) -> Prog {
        Prog::Return(v)
    }
    /// `perform op(arg); <continuation referencing the result as Var(0)>`.
    pub fn perform(op: &str, arg: Term, cont: Prog) -> Prog {
        Prog::Perform(op.to_string(), arg, Box::new(cont))
    }

    /// Plug a value in for this program's outermost result binder (used to resume a
    /// continuation once an operation has produced its result).
    pub fn instantiate(&self, r: &Term) -> Prog {
        self.subst(0, r)
    }
    fn subst(&self, depth: usize, r: &Term) -> Prog {
        match self {
            Prog::Return(v) => Prog::Return(v.subst_at(depth, r)),
            Prog::Perform(op, arg, k) => {
                Prog::Perform(op.clone(), arg.subst_at(depth, r), Box::new(k.subst(depth + 1, r)))
            }
        }
    }
}

/// A handler: a return clause and, for each handled operation, a clause receiving the
/// argument and a **resumption** (the rest of the computation, ready to continue with
/// the operation's result). These are *deep* handlers — the resumption re-installs the
/// handler, so it covers the whole continuation.
pub trait Handler {
    fn handles(&self, op: &str) -> bool;
    fn ret(&self, v: Term) -> Result<Term, String> {
        Ok(v)
    }
    fn handle_op(
        &self,
        op: &str,
        arg: Term,
        resume: &mut dyn FnMut(Term) -> Result<Term, String>,
    ) -> Result<Term, String>;
}

/// Run `p` under handler `h`, returning the final value. An operation `h` doesn't
/// handle is an error (in a full system it would propagate to an outer handler).
pub fn run(p: &Prog, h: &dyn Handler) -> Result<Term, String> {
    match p {
        Prog::Return(v) => h.ret(v.clone()),
        Prog::Perform(op, arg, k) => {
            if h.handles(op) {
                // Deep resumption: continue `k` with the op's result, under `h` again.
                let mut resume = |r: Term| run(&k.instantiate(&r), h);
                h.handle_op(op, arg.clone(), &mut resume)
            } else {
                Err(format!("unhandled effect '{op}'"))
            }
        }
    }
}

/// The canonical **state** handler, interpreting `get`/`put` by threading a state
/// value. Returns `(result, final_state)`. State needs the result to depend on the
/// threaded value, so it is its own interpreter rather than a [`Handler`] clause.
pub fn run_state(p: &Prog, state: Term) -> Result<(Term, Term), String> {
    match p {
        Prog::Return(v) => Ok((v.clone(), state)),
        Prog::Perform(op, arg, k) => match op.as_str() {
            // `get` yields the current state as its result.
            "get" => run_state(&k.instantiate(&state), state),
            // `put new` sets the state, yields unit.
            "put" => run_state(&k.instantiate(&unit_value()), arg.clone()),
            other => Err(format!("state handler: unhandled effect '{other}'")),
        },
    }
}

fn unit_value() -> Term {
    Term::cnst(rv_kernel_core::term::name("unit"), vec![])
}

/// A handler that supplies a fixed value for every `ask` (the reader effect).
pub struct Reader {
    pub value: Term,
}
impl Handler for Reader {
    fn handles(&self, op: &str) -> bool {
        op == "ask"
    }
    fn handle_op(
        &self,
        _op: &str,
        _arg: Term,
        resume: &mut dyn FnMut(Term) -> Result<Term, String>,
    ) -> Result<Term, String> {
        resume(self.value.clone()) // resume the continuation with the environment value
    }
}

/// A handler for `throw`: short-circuits, ignoring the resumption (the exception
/// effect). The thrown value becomes the result.
pub struct Exception;
impl Handler for Exception {
    fn handles(&self, op: &str) -> bool {
        op == "throw"
    }
    fn handle_op(
        &self,
        _op: &str,
        arg: Term,
        _resume: &mut dyn FnMut(Term) -> Result<Term, String>,
    ) -> Result<Term, String> {
        Ok(arg) // discard the continuation — control does not return
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_kernel_core::term::name;

    fn unit() -> Term {
        Term::cnst(name("unit"), vec![])
    }
    fn c(s: &str) -> Term {
        Term::cnst(name(s), vec![])
    }

    #[test]
    fn rows_accumulate_and_sequence() {
        // perform io; perform st; return
        let c = Comp::perform("io", Comp::perform("st", Comp::ret(unit())));
        assert_eq!(c.effect(), EffRow::of(&["io", "st"]));
        // sequencing unions rows
        let a = Comp::perform("io", Comp::ret(unit()));
        let b = Comp::perform("panic", Comp::ret(unit()));
        assert_eq!(Comp::seq(a, b).effect(), EffRow::of(&["io", "panic"]));
    }

    #[test]
    fn handler_discharges_an_effect() {
        let c = Comp::perform("io", Comp::perform("st", Comp::ret(unit())));
        let handled = Comp::handle("io", c);
        assert_eq!(handled.effect(), EffRow::of(&["st"]));
        assert!(!handled.is_pure());
    }

    #[test]
    fn handling_everything_is_pure_and_reflects() {
        let c = Comp::perform("io", Comp::perform("st", Comp::ret(unit())));
        let sandboxed = c.sandbox(&EffRow::of(&["io", "st"]));
        assert!(sandboxed.is_pure(), "all effects discharged ⇒ pure");
        // A pure computation crosses back into the kernel value world.
        assert_eq!(sandboxed.as_value(), Some(unit()));
    }

    #[test]
    fn purity_gate_blocks_effectful_code_from_logic() {
        // A "spec function" body: pure ⇒ admissible (reflects to a value).
        let spec = Comp::ret(unit());
        assert!(spec.is_pure());
        assert_eq!(spec.as_value(), Some(unit()));

        // An "exec function" body: performs io ⇒ NOT admissible as logic.
        let exec = Comp::perform("io", Comp::ret(unit()));
        assert!(!exec.is_pure());
        assert_eq!(exec.as_value(), None, "effectful code cannot be used as logic");
    }

    #[test]
    fn capability_sandboxing() {
        let comp = Comp::perform("io", Comp::ret(unit()));
        // Runnable only when `io` is granted.
        assert!(comp.runnable_under(&EffRow::of(&["io", "st"])));
        assert!(!comp.runnable_under(&EffRow::of(&["st"])), "missing the io capability");
        // No ambient capability ⇒ a pure computation runs anywhere.
        assert!(Comp::ret(unit()).runnable_under(&EffRow::empty()));
    }

    // ----- operational semantics: deep handlers -----

    /// State handler threads state: `put a; x = get; return x`  ⇒  result `a`, state `a`.
    #[test]
    fn state_handler_threads_state() {
        // put a ; (get bound as Var0) ; return Var0
        let prog = Prog::perform(
            "put",
            c("a"),
            Prog::perform("get", unit(), Prog::ret(Term::Var(0))),
        );
        let (result, final_state) = run_state(&prog, c("s0")).unwrap();
        assert_eq!(result, c("a"));
        assert_eq!(final_state, c("a"));
    }

    /// Reader handler resumes with the supplied environment value.
    #[test]
    fn reader_handler_supplies_value() {
        // x = ask ; return x
        let prog = Prog::perform("ask", unit(), Prog::ret(Term::Var(0)));
        let out = run(&prog, &Reader { value: c("env") }).unwrap();
        assert_eq!(out, c("env"));
    }

    /// Exception handler short-circuits: `throw e; <unreachable>`  ⇒  `e`.
    #[test]
    fn exception_handler_short_circuits() {
        let prog = Prog::perform("throw", c("boom"), Prog::ret(c("never")));
        assert_eq!(run(&prog, &Exception).unwrap(), c("boom"));
        // With no throw, the return value passes through.
        let ok = Prog::ret(c("fine"));
        assert_eq!(run(&ok, &Exception).unwrap(), c("fine"));
    }

    /// An unhandled effect is reported, not silently ignored.
    #[test]
    fn unhandled_effect_errors() {
        let prog = Prog::perform("io", unit(), Prog::ret(unit()));
        assert!(run(&prog, &Reader { value: unit() }).is_err());
    }
}
