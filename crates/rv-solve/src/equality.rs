//! The equality / congruence fragment over **opaque** (uninterpreted) terms.
//!
//! Some comparison atoms cannot be handled by the linear engine because their
//! operands are not linear integer expressions — e.g. `q / r`, `q % r`, or any
//! term the arithmetic layer rejects. When such a term appears under `==` / `!=`
//! we still want the *equality theory* to apply: `==` is reflexive, symmetric and
//! transitive, and `a == b ∧ a != b` is a contradiction.
//!
//! We decide the **conjunctive** equality fragment with a union–find (congruence
//! closure restricted to constants — we deliberately do *not* model function
//! symbols, so `f(a) == f(b)` is out of scope and stays opaque):
//!
//! 1. Union the two sides of every asserted equality `l == r`.
//! 2. After all unions, a disjunct is UNSAT iff some asserted disequality `l != r`
//!    has `find(l) == find(r)` — the two terms are forced equal yet asserted
//!    unequal.
//!
//! ## Soundness
//!
//! We only ever return `true` ("this conjunction is UNSAT") when an asserted
//! disequality directly contradicts the equality closure. Every union step is a
//! valid consequence of an asserted equality, and `find(l) == find(r)` means
//! `l = r` is entailed by the asserted equalities alone; asserting `l != r` on top
//! is then genuinely contradictory. We never use this layer to *prove* a goal
//! beyond detecting such a contradiction, so it cannot discharge an invalid
//! obligation. (Reflexivity `l != l` with `l` syntactically identical is also
//! caught, since `find(l) == find(l)` trivially.)
//!
//! Terms are compared by **syntactic identity** (`Term`'s derived `Eq`), which is
//! the same notion the rest of the opaque machinery uses. Two syntactically
//! different terms that happen to denote the same value are treated as distinct —
//! that only makes us *weaker* (we may fail to prove something), never unsound.

use rv_core::Term;

/// A union–find over opaque terms, keyed by syntactic identity.
///
/// `Term` is not `Hash` (it lives in the kernel and we cannot extend it), so we
/// intern by linear scan over the `terms` vector — disjuncts in this slice carry only
/// a handful of atoms, so this is negligible. Each distinct `Term` we see is assigned
/// a dense index; `parent` is the standard disjoint-set forest with path compression
/// and union-by-size.
#[derive(Default)]
pub struct EqClosure {
    terms: Vec<Term>,
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl EqClosure {
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up `t`'s set index if it has been interned.
    fn lookup(&self, t: &Term) -> Option<usize> {
        self.terms.iter().position(|x| x == t)
    }

    /// Intern `t`, returning its set index (creating a fresh singleton set if new).
    /// The arguments of an `App` are interned too, so the congruence closure
    /// ([`close`]) can compare their classes.
    fn id(&mut self, t: &Term) -> usize {
        if let Some(i) = self.lookup(t) {
            return i;
        }
        let i = self.parent.len();
        self.parent.push(i);
        self.size.push(1);
        self.terms.push(t.clone());
        if let Term::App(_, args) = t {
            for a in args.clone() {
                self.id(&a);
            }
        }
        i
    }

    /// Find with path compression.
    fn find(&mut self, mut i: usize) -> usize {
        while self.parent[i] != i {
            self.parent[i] = self.parent[self.parent[i]];
            i = self.parent[i];
        }
        i
    }

    /// Assert `a == b`: union their classes.
    pub fn assert_eq(&mut self, a: &Term, b: &Term) {
        let (ia, ib) = (self.id(a), self.id(b));
        self.union(ia, ib);
    }

    /// Intern `t` (and, for an `App`, its arguments) without asserting anything, so
    /// it participates in the congruence closure. Call this for terms that appear
    /// only in disequalities — otherwise they'd never be interned and congruence
    /// could not relate them.
    pub fn see(&mut self, t: &Term) {
        self.id(t);
    }

    /// Union the classes of two interned indices (union by size).
    fn union(&mut self, ia: usize, ib: usize) {
        let (ra, rb) = (self.find(ia), self.find(ib));
        if ra == rb {
            return;
        }
        let (small, large) = if self.size[ra] < self.size[rb] { (ra, rb) } else { (rb, ra) };
        self.parent[small] = large;
        self.size[large] += self.size[small];
    }

    /// Saturate the **congruence closure** over uninterpreted applications: while
    /// any two interned `App(f, a..)` and `App(f, b..)` (same symbol, same arity)
    /// have all argument pairs already in the same class, union the two
    /// applications. Repeats to a fixpoint. Call this once after all `assert_eq`s
    /// and before checking disequalities.
    ///
    /// Soundness: congruence (`a = b ⟹ f(a) = f(b)`) is valid for any function, so
    /// every union performed here is a genuine consequence of the asserted
    /// equalities — it can only force *more* terms equal, never falsely separate
    /// them, so a later disequality contradiction it enables is real.
    pub fn close(&mut self) {
        loop {
            let apps: Vec<usize> = (0..self.terms.len())
                .filter(|&i| matches!(self.terms[i], Term::App(..)))
                .collect();
            let mut changed = false;
            for x in 0..apps.len() {
                for y in (x + 1)..apps.len() {
                    let (i, j) = (apps[x], apps[y]);
                    if self.find(i) != self.find(j) && self.congruent(i, j) {
                        self.union(i, j);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// Whether two interned `App` terms are congruent: same function symbol and
    /// arity, with every argument pair currently in the same class.
    fn congruent(&mut self, i: usize, j: usize) -> bool {
        let (ti, tj) = (self.terms[i].clone(), self.terms[j].clone());
        let (Term::App(f, a), Term::App(g, b)) = (&ti, &tj) else {
            return false;
        };
        if f != g || a.len() != b.len() {
            return false;
        }
        a.iter().zip(b.iter()).all(|(x, y)| {
            let (ix, iy) = (self.id(x), self.id(y));
            self.find(ix) == self.find(iy)
        })
    }

    /// Are `a` and `b` currently forced equal by the asserted equalities?
    ///
    /// Returns `false` if either term was never seen (it cannot be forced equal to
    /// anything it never co-occurred with).
    pub fn equal(&mut self, a: &Term, b: &Term) -> bool {
        let (ia, ib) = match (self.lookup(a), self.lookup(b)) {
            (Some(ia), Some(ib)) => (ia, ib),
            _ => return false,
        };
        self.find(ia) == self.find(ib)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_core::{Symbols, Term};

    fn v(s: &mut Symbols, name: &str) -> Term {
        Term::Var(s.intern(name))
    }

    #[test]
    fn transitivity_holds() {
        let mut s = Symbols::new();
        let (a, b, c) = (v(&mut s, "a"), v(&mut s, "b"), v(&mut s, "c"));
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        uf.assert_eq(&b, &c);
        assert!(uf.equal(&a, &c));
    }

    #[test]
    fn symmetry_holds() {
        let mut s = Symbols::new();
        let (a, b) = (v(&mut s, "a"), v(&mut s, "b"));
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        assert!(uf.equal(&b, &a));
    }

    #[test]
    fn unrelated_not_equal() {
        let mut s = Symbols::new();
        let (a, b, c) = (v(&mut s, "a"), v(&mut s, "b"), v(&mut s, "c"));
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        assert!(!uf.equal(&a, &c));
    }

    /// Congruence: `a == b ⟹ f(a) == f(b)`.
    #[test]
    fn congruence_over_apps() {
        let mut s = Symbols::new();
        let (a, b) = (v(&mut s, "a"), v(&mut s, "b"));
        let f = s.intern("f");
        let fa = Term::app(f, vec![a.clone()]);
        let fb = Term::app(f, vec![b.clone()]);
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        uf.see(&fa);
        uf.see(&fb);
        uf.close();
        assert!(uf.equal(&fa, &fb));
    }

    /// Congruence does *not* over-fire: distinct, unequal arguments leave the
    /// applications in separate classes.
    #[test]
    fn no_spurious_congruence() {
        let mut s = Symbols::new();
        let (a, b) = (v(&mut s, "a"), v(&mut s, "b"));
        let f = s.intern("f");
        let fa = Term::app(f, vec![a.clone()]);
        let fb = Term::app(f, vec![b.clone()]);
        let mut uf = EqClosure::new();
        // No `a == b` asserted.
        uf.see(&fa);
        uf.see(&fb);
        uf.close();
        assert!(!uf.equal(&fa, &fb));
    }

    /// Nested congruence to a fixpoint: `a == b ⟹ g(f(a)) == g(f(b))`.
    #[test]
    fn nested_congruence() {
        let mut s = Symbols::new();
        let (a, b) = (v(&mut s, "a"), v(&mut s, "b"));
        let (f, g) = (s.intern("f"), s.intern("g"));
        let gfa = Term::app(g, vec![Term::app(f, vec![a.clone()])]);
        let gfb = Term::app(g, vec![Term::app(f, vec![b.clone()])]);
        let mut uf = EqClosure::new();
        uf.assert_eq(&a, &b);
        uf.see(&gfa);
        uf.see(&gfb);
        uf.close();
        assert!(uf.equal(&gfa, &gfb));
    }
}
