//! End-to-end tests for the Tier-4 CK abstract machine: real programs are loaded,
//! run through the explicit control stack, and the resulting number is read back.
use rv_kernel::cek;

/// Build `Nat.succ^n Nat.zero`.
fn nat(n: usize) -> String {
    let mut s = String::from("Nat.zero");
    for _ in 0..n {
        s = format!("Nat.succ ({s})");
    }
    s
}

/// Load `prog`, run it with `fuel` steps on the machine, read back the resulting number.
fn eval(prog: &str, fuel: usize) -> String {
    let mut s = cek::session().unwrap();
    s.run(&format!("def prog : Tm := {prog}")).unwrap();
    s.run(&format!("def fuel : Nat := {}", nat(fuel))).unwrap();
    s.run("def answer : Nat := evalNat fuel prog").unwrap();
    s.run_entry("answer").unwrap()
}

#[test]
fn beta_then_add() {
    // (λx. x + 1) 2  ==>  3
    let prog = "Tm.app (Tm.lam (Tm.add (Tm.var Nat.zero) (Tm.lit (Nat.succ Nat.zero)))) \
                (Tm.lit (Nat.succ (Nat.succ Nat.zero)))";
    assert_eq!(eval(prog, 30), "3");
}

#[test]
fn higher_order_double_application() {
    // (λf. f (f 0)) (λx. x + 1)  ==>  2
    let succ = "Tm.lam (Tm.add (Tm.var Nat.zero) (Tm.lit (Nat.succ Nat.zero)))";
    let twice = "Tm.lam (Tm.app (Tm.var Nat.zero) (Tm.app (Tm.var Nat.zero) (Tm.lit Nat.zero)))";
    let prog = format!("Tm.app ({twice}) ({succ})");
    assert_eq!(eval(&prog, 40), "2");
}

#[test]
fn nested_lambdas_capture_correctly() {
    // (λx. (λy. x + y) 10) 5  ==>  15   (tests that the de Bruijn substitution is right)
    let inner = format!(
        "Tm.app (Tm.lam (Tm.add (Tm.var (Nat.succ Nat.zero)) (Tm.var Nat.zero))) (Tm.lit ({}))",
        nat(10)
    );
    let prog = format!("Tm.app (Tm.lam ({inner})) (Tm.lit ({}))", nat(5));
    assert_eq!(eval(&prog, 40), "15");
}

#[test]
fn conditional_takes_then_branch_on_zero() {
    // ifz 0 then 7 else 9  ==>  7
    let prog = format!(
        "Tm.ifz (Tm.lit Nat.zero) (Tm.lit ({})) (Tm.lit ({}))",
        nat(7),
        nat(9)
    );
    assert_eq!(eval(&prog, 20), "7");
}

#[test]
fn conditional_takes_else_branch_on_nonzero() {
    // ifz 3 then 7 else 9  ==>  9
    let prog = format!(
        "Tm.ifz (Tm.lit ({})) (Tm.lit ({})) (Tm.lit ({}))",
        nat(3),
        nat(7),
        nat(9)
    );
    assert_eq!(eval(&prog, 20), "9");
}

// ----- algebraic effects + handlers -----

// (Object-level numbers are kept small: each is a unary `Nat.succ` chain, and the kernel
// evaluator recurses structurally over its full depth.)

// Handlers take two arguments: `λ payload. λ resume. body` (de Bruijn: payload = var1,
// resume = var0). `abort_*` ignore the resumption (the handler's value replaces the whole
// handled expression); `resume_*` apply it (the `op` returns and the computation continues).

/// `λp. λk. p`  — abort, yielding the payload.
fn abort_payload() -> String {
    "Tm.lam (Tm.lam (Tm.var (Nat.succ Nat.zero)))".into()
}
/// `λp. λk. p + c`  — abort, yielding payload + c.
fn abort_plus(c: usize) -> String {
    format!(
        "Tm.lam (Tm.lam (Tm.add (Tm.var (Nat.succ Nat.zero)) (Tm.lit ({}))))",
        nat(c)
    )
}
/// `λp. λk. k p`  — resume, feeding the payload back so `op` returns it.
fn resume_payload() -> String {
    "Tm.lam (Tm.lam (Tm.app (Tm.var Nat.zero) (Tm.var (Nat.succ Nat.zero))))".into()
}
/// `λp. λk. k (p + c)`  — resume, so `op` returns payload + c.
fn resume_plus(c: usize) -> String {
    format!(
        "Tm.lam (Tm.lam (Tm.app (Tm.var Nat.zero) (Tm.add (Tm.var (Nat.succ Nat.zero)) (Tm.lit ({})))))",
        nat(c)
    )
}

#[test]
fn handler_receives_the_operation_payload() {
    // handle (op 7) (λp. λk. p + 2)  ==>  9   (abort: handler's value is the result)
    let prog = format!("Tm.handle (Tm.op (Tm.lit ({}))) ({})", nat(7), abort_plus(2));
    assert_eq!(eval(&prog, 40), "9");
}

#[test]
fn aborting_discards_the_delimited_continuation() {
    // handle ((op 5) + 9) (λp. λk. p)  ==>  5
    // Ignoring the resumption throws away the `+ 9` between the op and the handler.
    let prog = format!(
        "Tm.handle (Tm.add (Tm.op (Tm.lit ({}))) (Tm.lit ({}))) ({})",
        nat(5),
        nat(9),
        abort_payload()
    );
    assert_eq!(eval(&prog, 40), "5");
}

#[test]
fn resuming_continues_the_computation() {
    // handle ((op 5) + 9) (λp. λk. k p)  ==>  14
    // Resuming feeds the payload back so `op 5` returns 5, and `5 + 9` runs to completion.
    // (Contrast `aborting_discards_…` above: same program, abort gives 5, resume gives 14.)
    let prog = format!(
        "Tm.handle (Tm.add (Tm.op (Tm.lit ({}))) (Tm.lit ({}))) ({})",
        nat(5),
        nat(9),
        resume_payload()
    );
    assert_eq!(eval(&prog, 60), "14");
}

#[test]
fn the_handler_transforms_the_resumed_value() {
    // handle ((op 5) + 9) (λp. λk. k (p + 100))  ==>  114   — op returns 105, then + 9.
    let prog = format!(
        "Tm.handle (Tm.add (Tm.op (Tm.lit ({}))) (Tm.lit ({}))) ({})",
        nat(5),
        nat(9),
        resume_plus(100)
    );
    assert_eq!(eval(&prog, 60), "114");
}

#[test]
fn nearest_handler_wins() {
    // handle (handle (op 1) (λp.λk. p + 3)) (λp.λk. p + 5)  ==>  4   (inner handler catches)
    let prog = format!(
        "Tm.handle (Tm.handle (Tm.op (Tm.lit ({}))) ({})) ({})",
        nat(1),
        abort_plus(3),
        abort_plus(5)
    );
    assert_eq!(eval(&prog, 40), "4");
}

#[test]
fn handler_is_transparent_when_no_op_is_performed() {
    // handle 6 (λp. λk. p + 1)  ==>  6   (body completes normally; the handler is popped)
    let prog = format!("Tm.handle (Tm.lit ({})) ({})", nat(6), abort_plus(1));
    assert_eq!(eval(&prog, 20), "6");
}

#[test]
fn unhandled_operation_gets_stuck() {
    // op 3 with no enclosing handler  ==>  stuck (the reader yields the 0 default)
    let prog = format!("Tm.op (Tm.lit ({}))", nat(3));
    assert_eq!(eval(&prog, 20), "0");
}

#[test]
fn insufficient_fuel_does_not_finish() {
    // One step is not enough to evaluate `(λx.x) 0`; the reader yields the zero default.
    let prog = "Tm.app (Tm.lam (Tm.var Nat.zero)) (Tm.lit (Nat.succ Nat.zero))";
    // With ample fuel it is 1; with a single step it has not reached `sdone` yet.
    assert_eq!(eval(prog, 30), "1");
    assert_eq!(eval(prog, 1), "0");
}
