//! Small, generic term-manipulation helpers shared by trusted core code
//! ([`crate::coinductive`]) and the untrusted recursor synthesizer
//! (`rv_kernel::generate`). These are pure structural utilities over [`Term`] —
//! peeling/folding Π-telescopes and a free-occurrence check — not synthesis logic,
//! so they live in the core crate and both sides depend on this one copy.

use crate::term::Term;

/// The de Bruijn index, at context depth `depth`, of the binder introduced at
/// absolute level `level` (0 = outermost).
pub fn mk_var(depth: usize, level: usize) -> Term {
    Term::Var(depth - 1 - level)
}

/// Peel exactly `n` leading `Π`s, returning their domains (each in the context of the
/// previous ones) and the remaining body. `None` if there are fewer than `n`.
pub fn peel_pis(mut t: Term, n: usize) -> Option<(Vec<Term>, Term)> {
    let mut doms = Vec::with_capacity(n);
    for _ in 0..n {
        match t {
            Term::Pi(_, d, b) => {
                doms.push((*d).clone());
                t = (*b).clone();
            }
            _ => return None,
        }
    }
    Some((doms, t))
}

/// Peel all leading `Π`s.
pub fn peel_all_pis(mut t: Term) -> (Vec<Term>, Term) {
    let mut doms = Vec::new();
    while let Term::Pi(_, d, b) = t {
        doms.push((*d).clone());
        t = (*b).clone();
    }
    (doms, t)
}

/// Does the constant `n` occur anywhere in `t`?
pub fn occurs(n: &str, t: &Term) -> bool {
    match t {
        Term::Const(m, _) => &**m == n,
        Term::App(f, a) => occurs(n, f) || occurs(n, a),
        Term::Lam(d, b) | Term::Pi(_, d, b) => occurs(n, d) || occurs(n, b),
        Term::Let(_, x, y, z) => occurs(n, x) || occurs(n, y) || occurs(n, z),
        Term::PLam(b) => occurs(n, b),
        Term::PApp(p, r) => occurs(n, p) || occurs(n, r),
        Term::PathP(fam, a0, a1) => occurs(n, fam) || occurs(n, a0) || occurs(n, a1),
        Term::Sort(_) | Term::Var(_) | Term::Meta(_) | Term::I | Term::IZero | Term::IOne => false,
    }
}

/// Fold a telescope of domains (each in the context of the previous ones) and a body
/// (in the full context) into nested `Π`s.
pub fn fold_pis(doms: &[Term], body: Term) -> Term {
    let mut t = body;
    for d in doms.iter().rev() {
        t = Term::pi(d.clone(), t);
    }
    t
}
