//! Propositional normalization: NNF, DNF, and atom extraction.
//!
//! We turn a `Prop` (with the boolean structure that may also live *inside* a
//! `Holds(term)`) into a flat **disjunction of conjunctions of literals**, where a
//! literal is an [`Atom`] tagged with a polarity. The arithmetic engine then only
//! ever sees conjunctions of atoms — it never re-parses propositional structure.

use rv_core::{BinOp, Prop, Term, UnOp};

/// An atomic, indivisible proposition.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Atom {
    /// An integer comparison `lhs ⋈ rhs`. `op` is one of `Eq/Ne/Lt/Le/Gt/Ge`.
    /// Whether it is actually *linear* is decided later by the arithmetic engine;
    /// if not, the whole literal is treated as opaque.
    Cmp { op: BinOp, lhs: Term, rhs: Term },
    /// Anything we do not interpret: a bare boolean term, a quantified prop, a
    /// non-comparison boolean operator we couldn't flatten, etc. Compared only by
    /// syntactic identity (the derived `Eq`).
    Opaque(OpaqueAtom),
}

/// Wrapper distinguishing the two kinds of opaque source so they never alias.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum OpaqueAtom {
    /// An opaque boolean-valued term (e.g. a bare `Var`, or `Holds(x / y == 0)`
    /// where the term is non-linear).
    Term(Term),
    /// An opaque proposition (e.g. a quantifier) that we cannot decompose.
    Prop(Box<Prop>),
}

/// A literal: an atom with a polarity.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Literal {
    pub atom: Atom,
    /// `true` means the atom is negated (`¬atom`).
    pub negated: bool,
}

impl Literal {
    fn pos(atom: Atom) -> Literal {
        Literal { atom, negated: false }
    }
    fn neg(atom: Atom) -> Literal {
        Literal { atom, negated: true }
    }
}

// ===========================================================================
// Negation Normal Form
// ===========================================================================

/// An NNF formula: negations have been pushed to the literals. Kept as its own
/// small tree (rather than reusing `Prop`) so the DNF step is total and obvious.
#[derive(Clone, Debug)]
pub enum Nnf {
    /// Constant true / false (after simplification these are pushed up where possible,
    /// but we keep them as nodes for a uniform recursion).
    Const(bool),
    Lit(Literal),
    And(Box<Nnf>, Box<Nnf>),
    Or(Box<Nnf>, Box<Nnf>),
}

/// Convert a `Prop` to NNF. `negate` requests `¬prop` (this is how negations are
/// driven inward without ever constructing a `Not` node in the result).
///
/// `Implies(a, b)` is rewritten to `¬a ∨ b`. Quantifiers are not decomposed: a
/// `Forall`/`Exists` becomes an opaque literal (sound — uninterpreted).
pub fn to_nnf(p: &Prop, negate: bool) -> Nnf {
    match p {
        Prop::True => Nnf::Const(!negate),
        Prop::False => Nnf::Const(negate),

        // De Morgan: ¬(a ∧ b) = ¬a ∨ ¬b, ¬(a ∨ b) = ¬a ∧ ¬b.
        Prop::And(a, b) => {
            let (la, lb) = (to_nnf(a, negate), to_nnf(b, negate));
            if negate {
                Nnf::Or(Box::new(la), Box::new(lb))
            } else {
                Nnf::And(Box::new(la), Box::new(lb))
            }
        }
        Prop::Or(a, b) => {
            let (la, lb) = (to_nnf(a, negate), to_nnf(b, negate));
            if negate {
                Nnf::And(Box::new(la), Box::new(lb))
            } else {
                Nnf::Or(Box::new(la), Box::new(lb))
            }
        }

        // ¬¬p collapses; otherwise flip the requested polarity.
        Prop::Not(a) => to_nnf(a, !negate),

        // a ⟹ b  ≡  ¬a ∨ b. Negated: ¬(a ⟹ b) ≡ a ∧ ¬b.
        Prop::Implies(a, b) => {
            if negate {
                Nnf::And(Box::new(to_nnf(a, false)), Box::new(to_nnf(b, true)))
            } else {
                Nnf::Or(Box::new(to_nnf(a, true)), Box::new(to_nnf(b, false)))
            }
        }

        // A boolean term: descend into its boolean structure (And/Or/Not/literals),
        // bottoming out at comparisons (which become Cmp atoms) or opaque terms.
        Prop::Holds(t) => term_to_nnf(t, negate),

        // Quantifiers: not decomposed. Treat the whole prop as one opaque atom.
        Prop::Forall(_, _) | Prop::Exists(_, _) => {
            let atom = Atom::Opaque(OpaqueAtom::Prop(Box::new(p.clone())));
            Nnf::Lit(if negate { Literal::neg(atom) } else { Literal::pos(atom) })
        }
    }
}

/// Convert a boolean-valued `Term` to NNF, honoring an outer `negate` request.
///
/// Understood structure: `Bool` literals; `Not`; `And`/`Or`; comparison binops.
/// Anything else (a bare `Var`, an arithmetic term used as a boolean, etc.) becomes
/// an opaque atom.
fn term_to_nnf(t: &Term, negate: bool) -> Nnf {
    match t {
        Term::Bool(b) => Nnf::Const(*b ^ negate),

        Term::Un(UnOp::Not, inner) => term_to_nnf(inner, !negate),

        Term::Bin(BinOp::And, a, b) => {
            let (la, lb) = (term_to_nnf(a, negate), term_to_nnf(b, negate));
            if negate {
                Nnf::Or(Box::new(la), Box::new(lb)) // ¬(a∧b)=¬a∨¬b
            } else {
                Nnf::And(Box::new(la), Box::new(lb))
            }
        }
        Term::Bin(BinOp::Or, a, b) => {
            let (la, lb) = (term_to_nnf(a, negate), term_to_nnf(b, negate));
            if negate {
                Nnf::And(Box::new(la), Box::new(lb)) // ¬(a∨b)=¬a∧¬b
            } else {
                Nnf::Or(Box::new(la), Box::new(lb))
            }
        }

        // Comparisons become Cmp atoms. The polarity is recorded on the literal; the
        // arithmetic engine will turn `¬(a < b)` into the right constraint itself.
        Term::Bin(op, a, b) if is_cmp(*op) => {
            let atom = Atom::Cmp { op: *op, lhs: (**a).clone(), rhs: (**b).clone() };
            Nnf::Lit(if negate { Literal::neg(atom) } else { Literal::pos(atom) })
        }

        // Anything else used as a boolean is opaque (e.g. a bare boolean variable).
        _ => {
            let atom = Atom::Opaque(OpaqueAtom::Term(t.clone()));
            Nnf::Lit(if negate { Literal::neg(atom) } else { Literal::pos(atom) })
        }
    }
}

fn is_cmp(op: BinOp) -> bool {
    matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
}

// ===========================================================================
// Disjunctive Normal Form
// ===========================================================================

/// Enumerate the DNF of an NNF formula as a list of conjunctions (each a `Vec` of
/// literals). Returns `None` if the number of disjuncts would exceed `max` — the
/// caller then reports `Failed` (sound: refusing to decide is never unsound).
///
/// `Const(true)` is the empty conjunction (trivially satisfiable); `Const(false)`
/// contributes no disjuncts. These identities make the recursion total.
pub fn dnf(f: &Nnf, max: usize) -> Option<Vec<Vec<Literal>>> {
    match f {
        // `true` ⇒ one disjunct, the empty (vacuously-true) conjunction.
        Nnf::Const(true) => Some(vec![vec![]]),
        // `false` ⇒ zero disjuncts.
        Nnf::Const(false) => Some(vec![]),

        Nnf::Lit(l) => Some(vec![vec![l.clone()]]),

        // DNF(a ∨ b) = DNF(a) ++ DNF(b).
        Nnf::Or(a, b) => {
            let mut da = dnf(a, max)?;
            let db = dnf(b, max)?;
            da.extend(db);
            if da.len() > max {
                return None;
            }
            Some(da)
        }

        // DNF(a ∧ b) = { ca ∪ cb : ca ∈ DNF(a), cb ∈ DNF(b) } (cross product).
        Nnf::And(a, b) => {
            let da = dnf(a, max)?;
            let db = dnf(b, max)?;
            // Bail early if the product would blow past the cap.
            if da.len().checked_mul(db.len()).is_none_or(|n| n > max) {
                return None;
            }
            let mut out = Vec::with_capacity(da.len() * db.len());
            for ca in &da {
                for cb in &db {
                    let mut merged = ca.clone();
                    merged.extend(cb.clone());
                    out.push(merged);
                }
            }
            Some(out)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rv_core::{Symbols, Ty};

    #[test]
    fn nnf_implies_becomes_or() {
        // a ⟹ b should NNF (un-negated) to ¬a ∨ b: an Or node.
        let mut s = Symbols::new();
        let _ = Ty::Int; // keep import used
        let a = Prop::Holds(Term::Var(s.intern("p")));
        let b = Prop::Holds(Term::Var(s.intern("q")));
        let imp = a.implies(b);
        let n = to_nnf(&imp, false);
        assert!(matches!(n, Nnf::Or(_, _)));
    }

    #[test]
    fn dnf_distributes() {
        // (p ∨ q) ∧ r  ⇒  (p ∧ r) ∨ (q ∧ r): two disjuncts.
        let mut s = Symbols::new();
        let p = Prop::Holds(Term::Var(s.intern("p")));
        let q = Prop::Holds(Term::Var(s.intern("q")));
        let r = Prop::Holds(Term::Var(s.intern("r")));
        let f = (p.or(q)).and(r);
        let n = to_nnf(&f, false);
        let d = dnf(&n, 100).unwrap();
        assert_eq!(d.len(), 2);
        for conj in &d {
            assert_eq!(conj.len(), 2);
        }
    }
}
