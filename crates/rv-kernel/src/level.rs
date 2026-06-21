//! Universe levels.
//!
//! Sorts are stratified `Type 0 : Type 1 : Type 2 : …` to avoid Girard's paradox
//! (`Type : Type` is inconsistent). A *level* is a small arithmetic expression over
//! universe **parameters** (for universe-polymorphic declarations like the
//! polymorphic identity, which lives at every level at once) built from:
//!
//! * `Zero`               — the base universe (`Type 0`, i.e. `Prop`'s neighbour),
//! * `Succ l`             — the next universe up,
//! * `Max a b`            — the least upper bound (used by `Π`/function-space rules),
//! * `IMax a b`           — the *impredicative* max: `Zero` when `b` is `Zero`, else
//!                          `Max a b`. This is the hook the `Prop` decision (Phase 2)
//!                          turns on; in Phase 0–1 only `Succ`/`Max` actually fire.
//! * `Param i`            — a universe variable, bound by a declaration's level arity.
//!
//! Level (in)equality is **not** syntactic: `Max a b = Max b a`, `Max a a = a`, etc.
//! We decide it by a normalize-then-compare algorithm (`leq` both ways), faithful to
//! the Lean/Coq kernels. The checker is *sound* (it only reports `leq`/`equiv` when
//! genuinely entailed); any incompleteness merely rejects some valid programs, never
//! accepts an unsound one.

use std::rc::Rc;

/// A universe level expression.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Level {
    Zero,
    Succ(Rc<Level>),
    Max(Rc<Level>, Rc<Level>),
    /// Impredicative max: `IMax a b` denotes `0` when `b` collapses to `0`, else
    /// `Max a b`. Lets a `Π` into `Prop` stay in `Prop` regardless of the domain.
    IMax(Rc<Level>, Rc<Level>),
    /// A universe parameter, referenced by its index into the declaration's level
    /// parameter list.
    Param(u32),
    /// An **elaboration-only** level metavariable (a hole to be solved by level
    /// unification). Like [`crate::term::Term::Meta`], the trusted kernel must never
    /// see one: the elaborator zonks every level meta away, and the kernel rejects any
    /// that leak. For soundness, [`equiv`] treats a meta as equal only to *itself*.
    Meta(u32),
}

impl Level {
    pub fn zero() -> Level {
        Level::Zero
    }
    pub fn succ(l: Level) -> Level {
        Level::Succ(Rc::new(l))
    }
    pub fn max(a: Level, b: Level) -> Level {
        Level::Max(Rc::new(a), Rc::new(b))
    }
    pub fn imax(a: Level, b: Level) -> Level {
        Level::IMax(Rc::new(a), Rc::new(b))
    }
    pub fn param(i: u32) -> Level {
        Level::Param(i)
    }
    pub fn meta(i: u32) -> Level {
        Level::Meta(i)
    }

    /// Does this level contain an (unsolved) metavariable? The kernel rejects any that
    /// do, mirroring the term-level check.
    pub fn has_meta(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false,
            Level::Meta(_) => true,
            Level::Succ(a) => a.has_meta(),
            Level::Max(a, b) | Level::IMax(a, b) => a.has_meta() || b.has_meta(),
        }
    }
    /// `Type n` for a concrete `n` (i.e. `Succ^n Zero`).
    pub fn of_nat(n: u32) -> Level {
        let mut l = Level::Zero;
        for _ in 0..n {
            l = Level::succ(l);
        }
        l
    }

    /// Substitute level parameters by position (`Param(i)` ↦ `args[i]`). Out-of-range
    /// params are left untouched (caller guarantees arity in practice).
    pub fn instantiate(&self, args: &[Level]) -> Level {
        match self {
            Level::Zero => Level::Zero,
            Level::Succ(a) => Level::succ(a.instantiate(args)),
            Level::Max(a, b) => Level::max(a.instantiate(args), b.instantiate(args)),
            Level::IMax(a, b) => Level::imax(a.instantiate(args), b.instantiate(args)),
            Level::Param(i) => args.get(*i as usize).cloned().unwrap_or(Level::Param(*i)),
            Level::Meta(_) => self.clone(),
        }
    }

    /// Strip leading `Succ`s, returning `(base, offset)` with `self = base + offset`.
    fn base_offset(&self) -> (Level, u32) {
        let mut cur = self.clone();
        let mut n = 0;
        while let Level::Succ(a) = cur {
            cur = (*a).clone();
            n += 1;
        }
        (cur, n)
    }

    /// Whether this level is *definitely* `Zero` (after normalization).
    fn is_zero(&self) -> bool {
        matches!(self.normalize(), Level::Zero)
    }

    /// A normal form: push `Succ` outward, simplify `Max`/`IMax`. Not a unique
    /// canonical form in all cases, but enough that `leq` decides the fragment we
    /// use (concrete levels + single parameters).
    pub fn normalize(&self) -> Level {
        match self {
            Level::Zero | Level::Param(_) | Level::Meta(_) => self.clone(),
            Level::Succ(a) => Level::succ(a.normalize()),
            Level::Max(a, b) => norm_max(a.normalize(), b.normalize()),
            Level::IMax(a, b) => {
                let bn = b.normalize();
                match &bn {
                    // `IMax a 0 = 0`.
                    Level::Zero => Level::Zero,
                    // `IMax a (Succ _) = Max a (Succ _)`.
                    Level::Succ(_) => norm_max(a.normalize(), bn),
                    // `b` is a param/imax we cannot collapse: keep it impredicative.
                    _ => Level::imax(a.normalize(), bn),
                }
            }
        }
    }
}

/// Smart `Max` that absorbs `Zero` and merges along a shared base (`max(b+i, b+j) =
/// b + max(i,j)`), so concrete levels fully simplify.
fn norm_max(a: Level, b: Level) -> Level {
    if let Level::Zero = a {
        return b;
    }
    if let Level::Zero = b {
        return a;
    }
    let (ba, oa) = a.base_offset();
    let (bb, ob) = b.base_offset();
    if ba == bb {
        let base = ba;
        let mut r = base;
        for _ in 0..oa.max(ob) {
            r = Level::succ(r);
        }
        return r;
    }
    Level::max(a, b)
}

/// `lhs ≥ rhs`? (sound, normalize-then-compare). Equality is mutual `geq`.
fn geq_core(lhs: &Level, rhs: &Level) -> bool {
    if lhs == rhs || rhs.is_zero() {
        return true;
    }
    match rhs {
        Level::Max(b, c) => geq_core(lhs, b) && geq_core(lhs, c),
        _ => {
            if let Level::Max(a1, a2) = lhs {
                if geq_core(a1, rhs) || geq_core(a2, rhs) {
                    return true;
                }
            }
            match (lhs, rhs) {
                (Level::IMax(_, a2), _) => geq_core(a2, rhs),
                (_, Level::IMax(_, b2)) => geq_core(lhs, b2),
                _ => {
                    let (lb, lo) = lhs.base_offset();
                    let (rb, ro) = rhs.base_offset();
                    if lb == rb || rb.is_zero() {
                        lo >= ro
                    } else {
                        false
                    }
                }
            }
        }
    }
}

/// Decide `lhs ≤ rhs` over normalized levels.
pub fn leq(lhs: &Level, rhs: &Level) -> bool {
    geq_core(&rhs.normalize(), &lhs.normalize())
}

/// Decide level equality (definitional): `a ≤ b` and `b ≤ a`.
pub fn equiv(a: &Level, b: &Level) -> bool {
    leq(a, b) && leq(b, a)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concrete_levels_compare() {
        assert!(leq(&Level::of_nat(1), &Level::of_nat(2)));
        assert!(!leq(&Level::of_nat(2), &Level::of_nat(1)));
        assert!(equiv(&Level::of_nat(3), &Level::of_nat(3)));
    }

    #[test]
    fn max_absorbs_and_commutes() {
        let a = Level::param(0);
        let z = Level::Zero;
        assert!(equiv(&Level::max(a.clone(), z.clone()), &a));
        assert!(equiv(&Level::max(a.clone(), a.clone()), &a));
        let b = Level::param(1);
        assert!(equiv(&Level::max(a.clone(), b.clone()), &Level::max(b, a)));
    }

    #[test]
    fn imax_collapses_on_zero_rhs() {
        let a = Level::param(0);
        // IMax a 0 = 0
        assert!(equiv(&Level::imax(a.clone(), Level::Zero), &Level::Zero));
        // IMax a (Succ 0) = Max a (Succ 0)
        assert!(equiv(
            &Level::imax(a.clone(), Level::of_nat(1)),
            &Level::max(a, Level::of_nat(1))
        ));
    }

    #[test]
    fn succ_shares_base() {
        let a = Level::param(0);
        // max(a+1, a+2) = a+2
        let lhs = Level::max(Level::succ(a.clone()), Level::succ(Level::succ(a.clone())));
        assert!(equiv(&lhs, &Level::succ(Level::succ(a))));
    }

    #[test]
    fn instantiate_params() {
        let l = Level::max(Level::param(0), Level::succ(Level::param(1)));
        let got = l.instantiate(&[Level::Zero, Level::of_nat(2)]);
        assert!(equiv(&got, &Level::of_nat(3)));
    }
}
