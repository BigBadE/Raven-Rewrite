//! # `rv-borrow` — the ownership / borrow *substrate*
//!
//! This crate is a **self-contained library** of ownership-theory building blocks.
//! It is the substrate a future borrow-checking wave will sit on; it is *not yet*
//! wired into the IR. It exports two families of structures, both phrased against
//! the traits in [`rv_logic`]:
//!
//! 1. **Resource algebras** — partial commutative monoids with a validity
//!    predicate ([`rv_logic::ResourceAlgebra`]). These model *who owns how much*
//!    of a resource. We provide [`FracPerm`], the classic **fractional
//!    permissions** algebra: a permission is a rational in `(0, 1]`; `1` is full
//!    (unique / `&mut` / owned) and any fraction `< 1` is a shared `&`. Two halves
//!    compose back to the whole.
//!
//! 2. **Usage semirings** — QTT-style grades ([`rv_logic::Grades`]). These model
//!    *how many times* a variable may be used. We provide [`UsageSemiring`] over
//!    the carrier [`Mult`] (`Zero` / `One` / `Many`), from which linear, affine,
//!    and unrestricted disciplines are recovered by restricting the *allowed* set
//!    of grades.
//!
//! Plus a small generic [`check_pcm_laws`] harness used by the tests (and usable
//! by downstream crates) to confirm any `ResourceAlgebra` is a lawful partial
//! commutative monoid, and a documentation-oriented [`BorrowKind`] enum mapping
//! Rust-style borrows onto permissions and grades.
//!
//! ## Design notes
//!
//! * **No panics.** Every operation is total at the Rust level: partiality of the
//!   monoid is expressed as `Option`, and invalid permissions are expressed via
//!   `valid`, never via `panic!`. Rationals are kept normalized with `i64` and the
//!   only arithmetic that could overflow (numerator cross-multiplication) is done
//!   with checked ops that fall back to "invalid" rather than wrapping.
//! * **Foundation limitation (reported, not worked around):**
//!   [`rv_logic::ResourceAlgebra::R`] is bounded only by `Clone`, and `Grades::G`
//!   by `Clone + PartialEq`. So `compose`/`add` cannot, at the trait level, rely on
//!   `Eq`/`Hash`/`Ord` of the carrier. Our carriers happen to derive all of those,
//!   but the generic [`check_pcm_laws`] therefore takes an explicit equality
//!   closure rather than assuming `PartialEq` on `R`.

#![forbid(unsafe_code)]

// ===========================================================================
// 1. Rational helper: a normalized positive rational, stored as i64/i64.
// ===========================================================================

/// A non-negative rational number stored as `num / den`, always kept in lowest
/// terms with `den > 0`. Used as the carrier of fractional permissions.
///
/// We keep this deliberately small and self-contained (no external deps). All
/// constructors normalize, so two equal rationals always have identical fields,
/// which makes `PartialEq`/`Eq` structural equality the *mathematical* equality.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Rational {
    num: i64,
    den: i64,
}

impl Rational {
    /// Build `num / den`, normalized. Returns `None` if `den == 0`, if `num < 0`,
    /// or if normalization would overflow. (Permissions are never negative.)
    pub fn new(num: i64, den: i64) -> Option<Rational> {
        if den == 0 || num < 0 || den < 0 {
            return None;
        }
        let g = gcd(num, den);
        // g is never 0 here unless num == 0; guard anyway to avoid div-by-zero.
        let g = if g == 0 { 1 } else { g };
        Some(Rational { num: num / g, den: den / g })
    }

    /// The integer/whole rational `n / 1`.
    pub fn whole(n: i64) -> Option<Rational> {
        Rational::new(n, 1)
    }

    /// Numerator (in lowest terms).
    pub fn num(&self) -> i64 {
        self.num
    }

    /// Denominator (in lowest terms, always `> 0`).
    pub fn den(&self) -> i64 {
        self.den
    }

    /// Is this exactly zero?
    pub fn is_zero(&self) -> bool {
        self.num == 0
    }

    /// Checked addition. Returns `None` on overflow rather than wrapping/panicking.
    pub fn checked_add(&self, other: &Rational) -> Option<Rational> {
        // a/b + c/d = (a*d + c*b) / (b*d)
        let ad = self.num.checked_mul(other.den)?;
        let cb = other.num.checked_mul(self.den)?;
        let num = ad.checked_add(cb)?;
        let den = self.den.checked_mul(other.den)?;
        Rational::new(num, den)
    }

    /// Half of this rational (`num / (2*den)`), normalized. `None` on overflow.
    pub fn halved(&self) -> Option<Rational> {
        let den = self.den.checked_mul(2)?;
        Rational::new(self.num, den)
    }

    /// Compare to another rational without overflow-prone shared denominators
    /// where avoidable. Returns `Ordering`. Both denominators are positive, so
    /// cross-multiplication preserves sign; on overflow we fall back to `f64`
    /// (sufficient for the small permission rationals we deal with).
    pub fn cmp_to(&self, other: &Rational) -> core::cmp::Ordering {
        match (self.num.checked_mul(other.den), other.num.checked_mul(self.den)) {
            (Some(l), Some(r)) => l.cmp(&r),
            _ => {
                let l = self.num as f64 / self.den as f64;
                let r = other.num as f64 / other.den as f64;
                l.partial_cmp(&r).unwrap_or(core::cmp::Ordering::Equal)
            }
        }
    }

    /// Is `self <= other`?
    pub fn le(&self, other: &Rational) -> bool {
        self.cmp_to(other) != core::cmp::Ordering::Greater
    }
}

/// Euclid's GCD on non-negative inputs (we only ever pass non-negatives).
fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// ===========================================================================
// 2. Fractional permissions resource algebra.
// ===========================================================================

/// A *permission*: the carrier `R` of the [`FracPerm`] resource algebra.
///
/// * [`Perm::Empty`] is the **unit** of the monoid — the "no permission" element.
///   Composing it with anything is the identity. It is *not* a usable permission
///   (a real permission must be `> 0`), but it is always valid so it can act as a
///   neutral element.
/// * [`Perm::Frac`] holds a strictly-positive rational. A real, usable permission.
///
/// Modeling the unit as a dedicated `Empty` variant (rather than the rational `0`)
/// keeps "is this a real permission?" and "is this the identity?" cleanly separate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Perm {
    /// The empty permission — the monoid unit. Holds nothing.
    Empty,
    /// A positive fractional permission. Invariant (enforced by constructors):
    /// the inner rational is `> 0`.
    Frac(Rational),
}

impl Perm {
    /// Construct a real permission from `num / den`. Returns `None` if the value
    /// is not strictly positive or is malformed (so callers can't smuggle a `0`
    /// or negative into a `Frac`). Use [`Perm::Empty`] for the unit explicitly.
    pub fn frac(num: i64, den: i64) -> Option<Perm> {
        let r = Rational::new(num, den)?;
        if r.is_zero() {
            None
        } else {
            Some(Perm::Frac(r))
        }
    }

    /// The full permission `1` — unique ownership (`&mut` / owned).
    pub fn full() -> Perm {
        // 1/1 is always constructible.
        Perm::Frac(Rational::new(1, 1).expect("1/1 is valid"))
    }

    /// The fraction `1/2` — the canonical result of splitting full ownership once.
    pub fn half_perm() -> Perm {
        Perm::Frac(Rational::new(1, 2).expect("1/2 is valid"))
    }

    /// Is this the full permission (`== 1`)? Full = `&mut` / owned / unique.
    pub fn is_full(&self) -> bool {
        match self {
            Perm::Empty => false,
            Perm::Frac(r) => *r == Rational::new(1, 1).expect("1/1 is valid"),
        }
    }

    /// Is this a real (non-empty, strictly positive) permission?
    pub fn is_real(&self) -> bool {
        matches!(self, Perm::Frac(_))
    }

    /// The rational value, or `None` for [`Perm::Empty`].
    pub fn rational(&self) -> Option<Rational> {
        match self {
            Perm::Empty => None,
            Perm::Frac(r) => Some(*r),
        }
    }

    /// Split this permission in half. `Empty` halves to `Empty`; a `Frac` halves
    /// its rational. Two of the results [`compose`](FracPerm::compose) back to the
    /// original. Returns `None` only on (extremely unlikely) overflow.
    ///
    /// This is the fundamental "share a `&`" operation: `half(p) ⊕ half(p) = p`.
    pub fn half(&self) -> Option<Perm> {
        match self {
            Perm::Empty => Some(Perm::Empty),
            Perm::Frac(r) => Some(Perm::Frac(r.halved()?)),
        }
    }
}

/// **Fractional permissions** — a partial commutative monoid with validity.
///
/// Intuition: a permission to a location is a rational in `(0, 1]`. Full
/// ownership is `1` and grants mutation (`&mut`); it can be repeatedly *split*
/// into fractions that each grant only shared, read-only access (`&`). Splitting
/// and recombining is exactly addition of fractions:
///
/// ```text
///   half ⊕ half        = full          (valid; recombining a shared borrow)
///   full ⊕ anything>0  = >1            (INVALID; can't over-own)
///   2/3  ⊕ 2/3         = 4/3           (INVALID; over 1)
/// ```
///
/// * `unit()` is [`Perm::Empty`] — the neutral "no permission".
/// * `compose(a, b)` **adds** the permissions. It is total as an `Option`
///   (returns `Some` whenever the arithmetic is representable) — note that
///   composing can yield an *invalid* (sum `> 1`) permission; validity is a
///   *separate* judgement, per the PCM-with-validity design.
/// * `valid(a)` holds when `a` is `Empty`, or a fraction in `(0, 1]`.
///
/// Keeping `compose` and `valid` separate matches the resource-algebra design:
/// the monoid structure is total-ish (partial only via representability), and
/// "too much ownership" is caught by the validity predicate, not by making
/// `compose` fail.
pub struct FracPerm;

impl rv_logic::ResourceAlgebra for FracPerm {
    type R = Perm;

    fn unit() -> Self::R {
        Perm::Empty
    }

    fn compose(a: &Self::R, b: &Self::R) -> Option<Self::R> {
        match (a, b) {
            // Empty is the identity.
            (Perm::Empty, x) | (x, Perm::Empty) => Some(*x),
            // Add the two rationals. Sum of two positives is positive, so the
            // result is a genuine `Frac` (never collapses to Empty). `None` only
            // on arithmetic overflow.
            (Perm::Frac(x), Perm::Frac(y)) => Some(Perm::Frac(x.checked_add(y)?)),
        }
    }

    fn valid(a: &Self::R) -> bool {
        match a {
            // The unit is always valid (it is the neutral element, not a claim
            // of ownership).
            Perm::Empty => true,
            // A real permission is valid iff it lies in (0, 1]. Positivity is an
            // invariant of `Frac`, so we only need the upper bound `<= 1`.
            Perm::Frac(r) => r.le(&Rational::new(1, 1).expect("1/1 is valid")),
        }
    }
}

// ===========================================================================
// 3. Generic PCM (partial commutative monoid) law-checking harness.
// ===========================================================================

/// Outcome of running the PCM law checks — which law (if any) failed, for nicer
/// test diagnostics. `Ok` means every checked instance of every law held.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PcmCheck {
    /// All laws held on the supplied samples.
    Ok,
    /// `compose(a, unit) != a` or `compose(unit, a) != a` for some sample.
    IdentityFailed,
    /// `compose(a, b) != compose(b, a)` for some pair (where both defined).
    CommutativityFailed,
    /// `(a⊕b)⊕c != a⊕(b⊕c)` for some triple (where both sides defined).
    AssociativityFailed,
}

/// Check the **partial commutative monoid** laws of an arbitrary
/// [`rv_logic::ResourceAlgebra`] on a finite set of `samples`:
///
/// * **Identity:** `a ⊕ unit = a` and `unit ⊕ a = a`.
/// * **Commutativity:** whenever both `a ⊕ b` and `b ⊕ a` are defined, they're
///   equal. (Partiality: if one side is `None`, the other must be `None` too.)
/// * **Associativity:** whenever both `(a ⊕ b) ⊕ c` and `a ⊕ (b ⊕ c)` are
///   defined, they're equal.
///
/// Because the trait only guarantees `R: Clone` (no `PartialEq`), the caller
/// supplies an explicit equality predicate `eq`. This keeps the harness usable
/// for any resource algebra regardless of what its carrier derives.
///
/// Returns at the *first* violated law (handy for pinpointing bugs in tests).
pub fn check_pcm_laws<A, Eq>(samples: &[A::R], eq: Eq) -> PcmCheck
where
    A: rv_logic::ResourceAlgebra,
    Eq: Fn(&A::R, &A::R) -> bool,
{
    let unit = A::unit();

    // Identity.
    for a in samples {
        match (A::compose(a, &unit), A::compose(&unit, a)) {
            (Some(r1), Some(r2)) if eq(&r1, a) && eq(&r2, a) => {}
            _ => return PcmCheck::IdentityFailed,
        }
    }

    // Commutativity.
    for a in samples {
        for b in samples {
            match (A::compose(a, b), A::compose(b, a)) {
                (Some(ab), Some(ba)) => {
                    if !eq(&ab, &ba) {
                        return PcmCheck::CommutativityFailed;
                    }
                }
                (None, None) => {}
                // Defined one way but not the other breaks commutativity.
                _ => return PcmCheck::CommutativityFailed,
            }
        }
    }

    // Associativity (only compare when *both* groupings are defined).
    for a in samples {
        for b in samples {
            for c in samples {
                let left = A::compose(a, b).and_then(|ab| A::compose(&ab, c));
                let right = A::compose(b, c).and_then(|bc| A::compose(a, &bc));
                if let (Some(l), Some(r)) = (left, right) {
                    if !eq(&l, &r) {
                        return PcmCheck::AssociativityFailed;
                    }
                }
            }
        }
    }

    PcmCheck::Ok
}

// ===========================================================================
// 4. Usage semiring: the `Mult` carrier and the `UsageSemiring` Grades impl.
// ===========================================================================

/// Multiplicity grade — the carrier `G` of the [`UsageSemiring`].
///
/// This is the QTT "0/1/ω" usage lattice:
/// * [`Mult::Zero`] — used **zero** times (erased / not used).
/// * [`Mult::One`]  — used **exactly once**.
/// * [`Mult::Many`] — used **arbitrarily many** times (`ω`).
///
/// A *single* semiring over this carrier models several disciplines by which
/// grades are *permitted* on a variable:
/// * **linear**       — must end at exactly `One`  (see [`linear_ok`]).
/// * **affine**       — at most once: `Zero` or `One` (see [`affine_ok`]).
/// * **unrestricted** — any grade, including `Many`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mult {
    /// Zero uses.
    Zero,
    /// Exactly one use.
    One,
    /// Many (ω) uses.
    Many,
}

/// **Usage semiring** over [`Mult`]. Implements [`rv_logic::Grades`].
///
/// The semiring operations have their usual QTT reading:
///
/// **Addition** `⊕` — combine the usages of two *occurrences* (e.g. two branches
/// that both reference a variable, or sequential uses being summed):
///
/// | `+`  | Zero | One  | Many |
/// |------|------|------|------|
/// | Zero | Zero | One  | Many |
/// | One  | One  | Many | Many |
/// | Many | Many | Many | Many |
///
/// (`add` saturates: once you use something twice, you're in `Many`.)
///
/// **Multiplication** `⊗` — scale a usage by a multiplicity (e.g. using a
/// variable `n` times inside something itself used with grade `m`):
///
/// | `*`  | Zero | One  | Many |
/// |------|------|------|------|
/// | Zero | Zero | Zero | Zero |
/// | One  | Zero | One  | Many |
/// | Many | Zero | Many | Many |
///
/// `zero = Zero` (additive identity, multiplicative annihilator),
/// `one = One` (multiplicative identity).
///
/// `leq` is the usage order `Zero ≤ One ≤ Many`, used to ask "does the actual
/// usage fit within an allowed bound?".
pub struct UsageSemiring;

impl UsageSemiring {
    /// Numeric rank for the total order `Zero(0) < One(1) < Many(2)`.
    fn rank(g: &Mult) -> u8 {
        match g {
            Mult::Zero => 0,
            Mult::One => 1,
            Mult::Many => 2,
        }
    }
}

impl rv_logic::Grades for UsageSemiring {
    type G = Mult;

    fn zero() -> Self::G {
        Mult::Zero
    }

    fn one() -> Self::G {
        Mult::One
    }

    fn add(a: &Self::G, b: &Self::G) -> Self::G {
        use Mult::*;
        match (a, b) {
            // Zero is the additive identity.
            (Zero, x) | (x, Zero) => *x,
            // Many absorbs.
            (Many, _) | (_, Many) => Many,
            // One + One saturates to Many.
            (One, One) => Many,
        }
    }

    fn mul(a: &Self::G, b: &Self::G) -> Self::G {
        use Mult::*;
        match (a, b) {
            // Zero annihilates.
            (Zero, _) | (_, Zero) => Zero,
            // One is the multiplicative identity.
            (One, x) | (x, One) => *x,
            // Many * Many = Many.
            (Many, Many) => Many,
        }
    }

    fn leq(a: &Self::G, b: &Self::G) -> bool {
        Self::rank(a) <= Self::rank(b)
    }
}

/// Affine discipline predicate: a grade is affine-OK if a value is used **at most
/// once** — i.e. `g ≤ One` (`Zero` or `One`, never `Many`).
pub fn affine_ok(g: &Mult) -> bool {
    <UsageSemiring as rv_logic::Grades>::leq(g, &Mult::One)
}

/// Linear discipline predicate: a grade is linear-OK if a value is used **exactly
/// once** — i.e. `g == One`.
pub fn linear_ok(g: &Mult) -> bool {
    *g == Mult::One
}

// ===========================================================================
// 5. (Optional) BorrowKind — Rust-style borrows mapped onto perms & grades.
// ===========================================================================

/// A Rust-style borrow/move classification, for use by a future borrow checker.
///
/// This ties the two substrates together at the *documentation* level: it says
/// how each surface notion of borrowing projects onto a fractional permission
/// and onto a usage grade.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BorrowKind {
    /// `&T` — a shared, read-only borrow. Splittable; a *fraction* of the
    /// permission, and it does not consume the value (usage `Zero` from the
    /// owner's perspective: the borrow is returned).
    Shared,
    /// `&mut T` — a unique, mutable borrow. Requires the *full* permission while
    /// live, but (like `Shared`) is returned, so it does not consume the value.
    Mut,
    /// `move` — ownership transfer. Takes the full permission *and* consumes the
    /// value: usage `One`.
    Move,
}

impl BorrowKind {
    /// The fractional permission this borrow needs to be *held* while live.
    ///
    /// * `Shared` → a fraction (we return the canonical `1/2`; any positive
    ///   fraction `< 1` would do — the point is "not full").
    /// * `Mut` / `Move` → the full permission `1`.
    pub fn required_perm(&self) -> Perm {
        match self {
            BorrowKind::Shared => Perm::half_perm(),
            BorrowKind::Mut | BorrowKind::Move => Perm::full(),
        }
    }

    /// The usage grade this borrow imposes on the borrowed value.
    ///
    /// * `Shared` / `Mut` → `Zero`: the borrow is returned, so from the owner's
    ///   accounting the value is not consumed.
    /// * `Move` → `One`: the value is consumed exactly once.
    pub fn usage_grade(&self) -> Mult {
        match self {
            BorrowKind::Shared | BorrowKind::Mut => Mult::Zero,
            BorrowKind::Move => Mult::One,
        }
    }

    /// Does this borrow require *unique* access (the full permission)?
    pub fn is_unique(&self) -> bool {
        matches!(self, BorrowKind::Mut | BorrowKind::Move)
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rv_logic::{Grades, ResourceAlgebra};

    // ---- Rational basics ---------------------------------------------------

    #[test]
    fn rational_normalizes() {
        assert_eq!(Rational::new(2, 4), Rational::new(1, 2));
        assert_eq!(Rational::new(3, 3), Rational::new(1, 1));
        assert_eq!(Rational::new(0, 5), Rational::new(0, 1));
    }

    #[test]
    fn rational_rejects_bad_input() {
        assert_eq!(Rational::new(1, 0), None); // div by zero
        assert_eq!(Rational::new(-1, 2), None); // negative
        assert_eq!(Rational::new(1, -2), None); // negative den
    }

    #[test]
    fn rational_add_and_compare() {
        let h = Rational::new(1, 2).unwrap();
        let full = h.checked_add(&h).unwrap();
        assert_eq!(full, Rational::new(1, 1).unwrap());
        assert!(h.le(&full));
        assert!(!full.le(&h));
        // 2/3 + 2/3 = 4/3 > 1
        let twothirds = Rational::new(2, 3).unwrap();
        let sum = twothirds.checked_add(&twothirds).unwrap();
        assert_eq!(sum, Rational::new(4, 3).unwrap());
        assert!(!sum.le(&Rational::new(1, 1).unwrap()));
    }

    // ---- Fractional permission composition & validity ----------------------

    #[test]
    fn unit_is_empty_and_valid() {
        assert_eq!(FracPerm::unit(), Perm::Empty);
        assert!(FracPerm::valid(&Perm::Empty));
    }

    #[test]
    fn half_plus_half_is_full_and_valid() {
        let half = Perm::half_perm();
        let composed = FracPerm::compose(&half, &half).unwrap();
        assert_eq!(composed, Perm::full());
        assert!(composed.is_full());
        assert!(FracPerm::valid(&composed));
    }

    #[test]
    fn full_plus_anything_is_invalid() {
        let full = Perm::full();
        let some = Perm::frac(1, 100).unwrap();
        let sum = FracPerm::compose(&full, &some).unwrap();
        // Composition succeeds (it's representable) but the result is invalid.
        assert!(!FracPerm::valid(&sum));
        // full + full = 2, also invalid.
        let two = FracPerm::compose(&full, &full).unwrap();
        assert!(!FracPerm::valid(&two));
    }

    #[test]
    fn two_thirds_plus_two_thirds_invalid() {
        let p = Perm::frac(2, 3).unwrap();
        let sum = FracPerm::compose(&p, &p).unwrap();
        assert_eq!(sum, Perm::frac(4, 3).unwrap());
        assert!(!FracPerm::valid(&sum));
    }

    #[test]
    fn composing_with_unit_is_identity() {
        let p = Perm::frac(1, 3).unwrap();
        assert_eq!(FracPerm::compose(&p, &Perm::Empty).unwrap(), p);
        assert_eq!(FracPerm::compose(&Perm::Empty, &p).unwrap(), p);
        assert_eq!(
            FracPerm::compose(&Perm::Empty, &Perm::Empty).unwrap(),
            Perm::Empty
        );
    }

    #[test]
    fn perm_helpers() {
        assert!(Perm::full().is_full());
        assert!(!Perm::half_perm().is_full());
        assert!(Perm::half_perm().is_real());
        assert!(!Perm::Empty.is_real());
        // frac rejects zero / negative.
        assert_eq!(Perm::frac(0, 1), None);
        assert_eq!(Perm::frac(-1, 2), None);
        // half of full is the half permission.
        assert_eq!(Perm::full().half().unwrap(), Perm::half_perm());
        // half then compose back recovers the whole.
        let p = Perm::frac(3, 5).unwrap();
        let h = p.half().unwrap();
        assert_eq!(FracPerm::compose(&h, &h).unwrap(), p);
        // half of empty is empty.
        assert_eq!(Perm::Empty.half().unwrap(), Perm::Empty);
    }

    #[test]
    fn valid_boundary_is_one_inclusive() {
        assert!(FracPerm::valid(&Perm::full())); // exactly 1 is valid
        assert!(FracPerm::valid(&Perm::frac(99, 100).unwrap()));
        assert!(!FracPerm::valid(&Perm::frac(101, 100).unwrap()));
    }

    // ---- Generic PCM laws on FracPerm --------------------------------------

    #[test]
    fn fracperm_satisfies_pcm_laws() {
        let samples = vec![
            Perm::Empty,
            Perm::frac(1, 2).unwrap(),
            Perm::frac(1, 3).unwrap(),
            Perm::frac(2, 3).unwrap(),
            Perm::full(),
            Perm::frac(1, 6).unwrap(),
        ];
        // FracPerm carrier derives PartialEq, so plain `==` is our equality.
        let result = check_pcm_laws::<FracPerm, _>(&samples, |a, b| a == b);
        assert_eq!(result, PcmCheck::Ok);
    }

    #[test]
    fn pcm_harness_detects_a_non_law() {
        // A deliberately broken algebra whose `compose` is non-commutative:
        // it returns the *first* argument, ignoring the second (except unit).
        struct Broken;
        impl ResourceAlgebra for Broken {
            type R = u8;
            fn unit() -> u8 {
                0
            }
            fn compose(a: &u8, b: &u8) -> Option<u8> {
                if *a == 0 {
                    Some(*b)
                } else {
                    Some(*a) // ignores b: not commutative
                }
            }
            fn valid(_: &u8) -> bool {
                true
            }
        }
        let samples = vec![1u8, 2u8, 3u8];
        let result = check_pcm_laws::<Broken, _>(&samples, |a, b| a == b);
        assert_eq!(result, PcmCheck::CommutativityFailed);
    }

    // ---- Usage semiring laws ----------------------------------------------

    const GRADES: [Mult; 3] = [Mult::Zero, Mult::One, Mult::Many];

    #[test]
    fn add_table() {
        use Mult::*;
        assert_eq!(UsageSemiring::add(&Zero, &Zero), Zero);
        assert_eq!(UsageSemiring::add(&Zero, &One), One);
        assert_eq!(UsageSemiring::add(&One, &One), Many);
        assert_eq!(UsageSemiring::add(&One, &Many), Many);
        assert_eq!(UsageSemiring::add(&Many, &Many), Many);
    }

    #[test]
    fn mul_table() {
        use Mult::*;
        assert_eq!(UsageSemiring::mul(&Zero, &Many), Zero);
        assert_eq!(UsageSemiring::mul(&One, &Many), Many);
        assert_eq!(UsageSemiring::mul(&Many, &One), Many);
        assert_eq!(UsageSemiring::mul(&Many, &Many), Many);
        assert_eq!(UsageSemiring::mul(&One, &One), One);
    }

    #[test]
    fn additive_identity_and_commutativity() {
        for a in GRADES {
            // zero is identity
            assert_eq!(UsageSemiring::add(&a, &UsageSemiring::zero()), a);
            assert_eq!(UsageSemiring::add(&UsageSemiring::zero(), &a), a);
            for b in GRADES {
                // commutativity of add
                assert_eq!(UsageSemiring::add(&a, &b), UsageSemiring::add(&b, &a));
            }
        }
    }

    #[test]
    fn multiplicative_identity_and_annihilator() {
        for a in GRADES {
            // one is identity
            assert_eq!(UsageSemiring::mul(&a, &UsageSemiring::one()), a);
            assert_eq!(UsageSemiring::mul(&UsageSemiring::one(), &a), a);
            // zero annihilates
            assert_eq!(UsageSemiring::mul(&a, &UsageSemiring::zero()), Mult::Zero);
            assert_eq!(UsageSemiring::mul(&UsageSemiring::zero(), &a), Mult::Zero);
        }
    }

    #[test]
    fn add_and_mul_are_associative() {
        for a in GRADES {
            for b in GRADES {
                for c in GRADES {
                    // (a+b)+c == a+(b+c)
                    let l = UsageSemiring::add(&UsageSemiring::add(&a, &b), &c);
                    let r = UsageSemiring::add(&a, &UsageSemiring::add(&b, &c));
                    assert_eq!(l, r);
                    // (a*b)*c == a*(b*c)
                    let l = UsageSemiring::mul(&UsageSemiring::mul(&a, &b), &c);
                    let r = UsageSemiring::mul(&a, &UsageSemiring::mul(&b, &c));
                    assert_eq!(l, r);
                }
            }
        }
    }

    #[test]
    fn mul_is_commutative() {
        for a in GRADES {
            for b in GRADES {
                assert_eq!(UsageSemiring::mul(&a, &b), UsageSemiring::mul(&b, &a));
            }
        }
    }

    #[test]
    fn distributivity_holds() {
        // a*(b+c) == a*b + a*c  and  (a+b)*c == a*c + b*c
        for a in GRADES {
            for b in GRADES {
                for c in GRADES {
                    let lhs = UsageSemiring::mul(&a, &UsageSemiring::add(&b, &c));
                    let rhs = UsageSemiring::add(
                        &UsageSemiring::mul(&a, &b),
                        &UsageSemiring::mul(&a, &c),
                    );
                    assert_eq!(lhs, rhs, "left-distrib failed for {a:?},{b:?},{c:?}");

                    let lhs2 = UsageSemiring::mul(&UsageSemiring::add(&a, &b), &c);
                    let rhs2 = UsageSemiring::add(
                        &UsageSemiring::mul(&a, &c),
                        &UsageSemiring::mul(&b, &c),
                    );
                    assert_eq!(lhs2, rhs2, "right-distrib failed for {a:?},{b:?},{c:?}");
                }
            }
        }
    }

    #[test]
    fn leq_is_the_usage_order() {
        use Mult::*;
        assert!(UsageSemiring::leq(&Zero, &One));
        assert!(UsageSemiring::leq(&One, &Many));
        assert!(UsageSemiring::leq(&Zero, &Many));
        assert!(UsageSemiring::leq(&One, &One));
        assert!(!UsageSemiring::leq(&Many, &One));
        assert!(!UsageSemiring::leq(&One, &Zero));
    }

    // ---- affine / linear predicates ---------------------------------------

    #[test]
    fn affine_and_linear_predicates() {
        // affine = at most once
        assert!(affine_ok(&Mult::Zero));
        assert!(affine_ok(&Mult::One));
        assert!(!affine_ok(&Mult::Many));
        // linear = exactly once
        assert!(!linear_ok(&Mult::Zero));
        assert!(linear_ok(&Mult::One));
        assert!(!linear_ok(&Mult::Many));
    }

    // ---- BorrowKind mapping ------------------------------------------------

    #[test]
    fn borrowkind_maps_to_perms_and_grades() {
        // Shared: fractional, not full, not consuming.
        assert!(!BorrowKind::Shared.required_perm().is_full());
        assert_eq!(BorrowKind::Shared.usage_grade(), Mult::Zero);
        assert!(!BorrowKind::Shared.is_unique());

        // Mut: full permission, not consuming.
        assert!(BorrowKind::Mut.required_perm().is_full());
        assert_eq!(BorrowKind::Mut.usage_grade(), Mult::Zero);
        assert!(BorrowKind::Mut.is_unique());

        // Move: full permission, consumes once.
        assert!(BorrowKind::Move.required_perm().is_full());
        assert_eq!(BorrowKind::Move.usage_grade(), Mult::One);
        assert!(BorrowKind::Move.is_unique());

        // The Shared permission is valid and re-composes: two shared halves =
        // full unique access (recovering &mut by collecting all the &).
        let shared = BorrowKind::Shared.required_perm();
        assert!(FracPerm::valid(&shared));
        let recombined = FracPerm::compose(&shared, &shared).unwrap();
        assert!(recombined.is_full());
    }
}
