//! `match` on a member of a **mutual** inductive group, compiled via the group's
//! multi-motive recursor (real motive+arms for the matched member, trivial `R → R`
//! motive + identity minors for the siblings). Previously rejected outright.
use rv_kernel::verify::Session;

fn val_env() -> Session {
    let mut s = Session::new();
    s.run("inductive Bool : Type | false : Bool | true : Bool").unwrap();
    s.run("inductive Nat : Type | zero : Nat | succ : Nat -> Nat").unwrap();
    s.run("inductive Tm : Type | lit : Nat -> Tm | bod : Tm -> Tm").unwrap();
    s.run(
        "mutual { inductive Val : Type | vnat : Nat -> Val | vclos : Env -> Tm -> Val  \
                  inductive Env : Type | enil : Env | econs : Val -> Env -> Env }",
    )
    .unwrap();
    s
}

#[test]
fn non_recursive_match_on_a_mutual_member_computes() {
    let mut s = val_env();
    // A bare case-analysis on Val (a mutual member): pull out the Nat, default 0 on closures.
    s.run("def valNat (v : Val) : Nat := match v { | Val.vnat(n) => n | Val.vclos(e, b) => Nat.zero }")
        .unwrap();
    s.run("def a : Nat := valNat (Val.vnat (Nat.succ (Nat.succ Nat.zero)))").unwrap();
    s.run("def b : Nat := valNat (Val.vclos Env.enil (Tm.lit Nat.zero))").unwrap();
    assert_eq!(s.run_entry("a").unwrap(), "2");
    assert_eq!(s.run_entry("b").unwrap(), "0");
}

#[test]
fn match_on_a_member_with_a_sibling_field() {
    let mut s = val_env();
    // `vclos` carries an `Env` (the *other* member) — the arm binds it and ignores it; the
    // recursor still demands (and the compiler still supplies) that field's IH slot.
    s.run("def isClos (v : Val) : Nat := match v { | Val.vnat(n) => Nat.zero | Val.vclos(e, b) => Nat.succ Nat.zero }")
        .unwrap();
    s.run("def c : Nat := isClos (Val.vclos Env.enil (Tm.lit Nat.zero))").unwrap();
    assert_eq!(s.run_entry("c").unwrap(), "1");
}

#[test]
fn lookup_into_a_mutual_environment() {
    let mut s = val_env();
    // Recurse on the Nat index, destructuring the mutual `Env` with inner matches.
    s.run(
        "fn lookupEnv(n: Nat) -> (Env -> Val) { \
           match n { \
             | Nat.zero => fun (e : Env) => match e { | Env.enil => Val.vnat Nat.zero | Env.econs(v, rest) => v } \
             | Nat.succ(m) => fun (e : Env) => match e { | Env.enil => Val.vnat Nat.zero | Env.econs(v, rest) => lookupEnv(m)(rest) } } }",
    )
    .unwrap();
    s.run("def e2 : Env := Env.econs (Val.vnat (Nat.succ Nat.zero)) (Env.econs (Val.vnat (Nat.succ (Nat.succ Nat.zero))) Env.enil)")
        .unwrap();
    s.run("def head : Nat := match lookupEnv Nat.zero e2 { | Val.vnat(n) => n | Val.vclos(e, b) => Nat.zero }").unwrap();
    s.run("def secnd : Nat := match lookupEnv (Nat.succ Nat.zero) e2 { | Val.vnat(n) => n | Val.vclos(e, b) => Nat.zero }").unwrap();
    assert_eq!(s.run_entry("head").unwrap(), "1");
    assert_eq!(s.run_entry("secnd").unwrap(), "2");
}

#[test]
fn match_on_tree_of_a_tree_forest_group() {
    // The classic mutual pair: a Tree holds a Forest, a Forest is a list of Trees.
    let mut s = Session::new();
    s.run("inductive Nat : Type | zero : Nat | succ : Nat -> Nat").unwrap();
    s.run(
        "mutual { inductive Tree : Type | node : Nat -> Forest -> Tree  \
                  inductive Forest : Type | fnil : Forest | fcons : Tree -> Forest -> Forest }",
    )
    .unwrap();
    // A non-recursive match reading the label off a Tree node (Forest field bound + ignored).
    s.run("def label (t : Tree) : Nat := match t { | Tree.node(n, f) => n }").unwrap();
    s.run("def t0 : Tree := Tree.node (Nat.succ (Nat.succ (Nat.succ Nat.zero))) Forest.fnil").unwrap();
    s.run("def l0 : Nat := label t0").unwrap();
    assert_eq!(s.run_entry("l0").unwrap(), "3");
}
