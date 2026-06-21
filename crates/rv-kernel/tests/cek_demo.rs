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

#[test]
fn handler_receives_the_operation_payload() {
    // handle (op 7) (λp. p + 2)  ==>  9
    let h = format!("Tm.lam (Tm.add (Tm.var Nat.zero) (Tm.lit ({})))", nat(2));
    let prog = format!("Tm.handle (Tm.op (Tm.lit ({}))) ({h})", nat(7));
    assert_eq!(eval(&prog, 40), "9");
}

#[test]
fn performing_an_op_discards_the_delimited_continuation() {
    // handle ((op 5) + 9) (λp. p)  ==>  5
    // The `+ 9` is part of the continuation between the op and the handler; performing the
    // op throws it away (exception/abort-style handling), so the handler sees just 5.
    let h = "Tm.lam (Tm.var Nat.zero)";
    let prog = format!(
        "Tm.handle (Tm.add (Tm.op (Tm.lit ({}))) (Tm.lit ({}))) ({h})",
        nat(5),
        nat(9)
    );
    assert_eq!(eval(&prog, 40), "5");
}

#[test]
fn nearest_handler_wins() {
    // handle (handle (op 1) (λp. p + 3)) (λp. p + 5)  ==>  4   (the inner handler catches)
    let inner_h = format!("Tm.lam (Tm.add (Tm.var Nat.zero) (Tm.lit ({})))", nat(3));
    let outer_h = format!("Tm.lam (Tm.add (Tm.var Nat.zero) (Tm.lit ({})))", nat(5));
    let prog = format!(
        "Tm.handle (Tm.handle (Tm.op (Tm.lit ({}))) ({inner_h})) ({outer_h})",
        nat(1)
    );
    assert_eq!(eval(&prog, 40), "4");
}

#[test]
fn handler_is_transparent_when_no_op_is_performed() {
    // handle 6 (λp. p + 1)  ==>  6   (body completes normally; the handler is popped)
    let prog = format!(
        "Tm.handle (Tm.lit ({})) (Tm.lam (Tm.add (Tm.var Nat.zero) (Tm.lit (Nat.succ Nat.zero))))",
        nat(6)
    );
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
