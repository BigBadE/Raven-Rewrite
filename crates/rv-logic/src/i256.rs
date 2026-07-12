//! A standalone, exhaustively-unit-tested 256-bit signed integer.
//!
//! This exists to widen [`crate::lia::Rat`]'s internal numerator/denominator
//! arithmetic past `i128`, so that Farkas certificate checking — the
//! **trusted** re-verification step — no longer spuriously overflows at the
//! `i128::MIN`/`MAX` extremes (which arise from legitimate `u128`/`i128`
//! obligations) while still being sound: every operation here is checked
//! (never wrapping), and any value that would exceed `I256`'s own range
//! returns `None` rather than a wrong answer.
//!
//! # Representation
//!
//! Sign-magnitude: a `bool` sign (`true` = negative; magnitude `0` is always
//! non-negative) plus a 256-bit magnitude stored as four `u64` limbs,
//! little-endian (`limbs[0]` is least significant). Sign-magnitude (rather
//! than two's complement) keeps `neg`/`abs`/comparison trivial to reason
//! about and avoids a min-value asymmetry: unlike `i128::MIN`, `I256`'s
//! magnitude range is symmetric, so negation never overflows.
//!
//! # Trust
//!
//! This type is part of the trust base transitively: [`crate::lia::Rat`]
//! (used by the independently-checkable [`crate::lia::LiaCertificate::check`])
//! is built on it. Every arithmetic operation is unit-tested here directly,
//! independent of `Rat`, so a bug can be caught at this layer.

use std::cmp::Ordering;

/// A 256-bit magnitude: four `u64` limbs, little-endian.
type Limbs = [u64; 4];

/// An exact 256-bit signed integer, sign-magnitude representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct I256 {
    /// `true` iff negative. Magnitude `0` always has `neg == false`
    /// (canonical zero), so equality is plain limb + sign comparison.
    neg: bool,
    mag: Limbs,
}

const ZERO_LIMBS: Limbs = [0, 0, 0, 0];

impl I256 {
    /// The additive identity.
    pub const ZERO: I256 = I256 { neg: false, mag: ZERO_LIMBS };

    /// Construct from an `i128`. Total (every `i128` value fits).
    pub fn from_i128(n: i128) -> I256 {
        if n == 0 {
            return I256::ZERO;
        }
        let neg = n < 0;
        // `n.unsigned_abs()` handles `i128::MIN` correctly (no overflow: the
        // result is a `u128`, which does hold `2^127`).
        let mag128 = n.unsigned_abs();
        I256 { neg, mag: limbs_from_u128(mag128) }
    }

    /// Construct from a `u128`. Total (every `u128` value fits).
    pub fn from_u128(n: u128) -> I256 {
        if n == 0 {
            return I256::ZERO;
        }
        I256 { neg: false, mag: limbs_from_u128(n) }
    }

    /// Is this value zero?
    pub fn is_zero(&self) -> bool {
        self.mag == ZERO_LIMBS
    }
    /// Is this value strictly negative?
    pub fn is_negative(&self) -> bool {
        self.neg && !self.is_zero()
    }
    /// Is this value strictly positive?
    pub fn is_positive(&self) -> bool {
        !self.neg && !self.is_zero()
    }

    /// Exact negation. Total: sign-magnitude has no asymmetric minimum, so
    /// negating any `I256` (including the most extreme representable
    /// magnitude) never overflows.
    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> I256 {
        if self.is_zero() {
            self
        } else {
            I256 { neg: !self.neg, mag: self.mag }
        }
    }

    /// Absolute value. Total, for the same reason as [`I256::neg`].
    pub fn abs(self) -> I256 {
        I256 { neg: false, mag: self.mag }
    }

    /// Checked addition. `None` if the magnitude would exceed 256 bits.
    pub fn checked_add(self, other: I256) -> Option<I256> {
        if self.neg == other.neg {
            let (mag, carry) = add_limbs(self.mag, other.mag);
            if carry {
                return None;
            }
            Some(I256::from_sign_mag(self.neg, mag))
        } else {
            // Different signs: subtract the smaller magnitude from the larger,
            // keep the sign of the larger.
            match cmp_limbs(self.mag, other.mag) {
                Ordering::Equal => Some(I256::ZERO),
                Ordering::Greater => {
                    let mag = sub_limbs(self.mag, other.mag);
                    Some(I256::from_sign_mag(self.neg, mag))
                }
                Ordering::Less => {
                    let mag = sub_limbs(other.mag, self.mag);
                    Some(I256::from_sign_mag(other.neg, mag))
                }
            }
        }
    }

    /// Checked subtraction.
    pub fn checked_sub(self, other: I256) -> Option<I256> {
        self.checked_add(other.neg())
    }

    /// Checked multiplication. `None` on overflow past 256 bits.
    pub fn checked_mul(self, other: I256) -> Option<I256> {
        let mag = mul_limbs(self.mag, other.mag)?;
        let neg = self.neg != other.neg;
        Some(I256::from_sign_mag(neg, mag))
    }

    /// Checked division, truncating toward zero (like `i128`'s `/`).
    /// `None` on division by zero.
    pub fn checked_div(self, other: I256) -> Option<I256> {
        if other.is_zero() {
            return None;
        }
        let (q, _r) = div_rem_limbs(self.mag, other.mag);
        let neg = self.neg != other.neg;
        Some(I256::from_sign_mag(neg, q))
    }

    /// Comparison.
    #[allow(clippy::should_implement_trait)]
    pub fn cmp(&self, other: &I256) -> Ordering {
        match (self.is_negative(), other.is_negative()) {
            (false, false) => cmp_limbs(self.mag, other.mag),
            (true, true) => cmp_limbs(other.mag, self.mag),
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
        }
    }

    /// Greatest common divisor of the absolute values. `gcd(0, n) == n`,
    /// `gcd(0, 0) == 0`. Always fits (gcd never exceeds the smaller operand's
    /// magnitude), so this is total.
    pub fn gcd(a: I256, b: I256) -> I256 {
        let mut x = a.mag;
        let mut y = b.mag;
        while y != ZERO_LIMBS {
            let (_, r) = div_rem_limbs(x, y);
            x = y;
            y = r;
        }
        I256 { neg: false, mag: x }
    }

    /// Try to narrow to an `i128`. `None` if the value doesn't fit.
    pub fn to_i128(&self) -> Option<i128> {
        // i128::MIN magnitude is 2^127; i128::MAX magnitude is 2^127 - 1.
        let mag = limbs_to_u128_checked(self.mag)?;
        if self.neg {
            if mag <= (i128::MAX as u128) + 1 {
                // mag == 2^127 is exactly i128::MIN's magnitude.
                if mag == (i128::MAX as u128) + 1 {
                    Some(i128::MIN)
                } else {
                    Some(-(mag as i128))
                }
            } else {
                None
            }
        } else if mag <= i128::MAX as u128 {
            Some(mag as i128)
        } else {
            None
        }
    }

    fn from_sign_mag(neg: bool, mag: Limbs) -> I256 {
        if mag == ZERO_LIMBS {
            I256::ZERO
        } else {
            I256 { neg, mag }
        }
    }
}

fn limbs_from_u128(n: u128) -> Limbs {
    [(n & 0xFFFF_FFFF_FFFF_FFFF) as u64, (n >> 64) as u64, 0, 0]
}

fn limbs_to_u128_checked(l: Limbs) -> Option<u128> {
    if l[2] != 0 || l[3] != 0 {
        return None;
    }
    Some((l[0] as u128) | ((l[1] as u128) << 64))
}

fn cmp_limbs(a: Limbs, b: Limbs) -> Ordering {
    for i in (0..4).rev() {
        match a[i].cmp(&b[i]) {
            Ordering::Equal => continue,
            other => return other,
        }
    }
    Ordering::Equal
}

/// `a + b`, returning `(sum, overflow)`.
fn add_limbs(a: Limbs, b: Limbs) -> (Limbs, bool) {
    let mut out = ZERO_LIMBS;
    let mut carry: u128 = 0;
    for i in 0..4 {
        let s = a[i] as u128 + b[i] as u128 + carry;
        out[i] = s as u64;
        carry = s >> 64;
    }
    (out, carry != 0)
}

/// `a - b`, assuming `a >= b` (caller's responsibility).
fn sub_limbs(a: Limbs, b: Limbs) -> Limbs {
    let mut out = ZERO_LIMBS;
    let mut borrow: i128 = 0;
    for i in 0..4 {
        let d = a[i] as i128 - b[i] as i128 - borrow;
        if d < 0 {
            out[i] = (d + (1i128 << 64)) as u64;
            borrow = 1;
        } else {
            out[i] = d as u64;
            borrow = 0;
        }
    }
    out
}

/// `a * b`, returning `None` if the true product exceeds 256 bits.
fn mul_limbs(a: Limbs, b: Limbs) -> Option<Limbs> {
    // Schoolbook multiplication into an 8-limb accumulator, then check the
    // top 4 limbs are all zero (else overflow).
    let mut acc: [u128; 8] = [0; 8];
    for (i, &ai) in a.iter().enumerate() {
        if ai == 0 {
            continue;
        }
        let mut carry: u128 = 0;
        for (j, &bj) in b.iter().enumerate() {
            let idx = i + j;
            let prod = (ai as u128) * (bj as u128) + acc[idx] + carry;
            acc[idx] = prod & 0xFFFF_FFFF_FFFF_FFFF;
            carry = prod >> 64;
        }
        // Propagate remaining carry through higher limbs.
        let mut k = i + 4;
        while carry != 0 {
            let s = acc[k] + carry;
            acc[k] = s & 0xFFFF_FFFF_FFFF_FFFF;
            carry = s >> 64;
            k += 1;
        }
    }
    if acc[4] != 0 || acc[5] != 0 || acc[6] != 0 || acc[7] != 0 {
        return None;
    }
    Some([acc[0] as u64, acc[1] as u64, acc[2] as u64, acc[3] as u64])
}

/// Long division: `(quotient, remainder)` such that `a == quotient*b + remainder`,
/// `0 <= remainder < b` (magnitude arithmetic; caller applies signs).
/// Precondition: `b != 0` (caller checks).
fn div_rem_limbs(a: Limbs, b: Limbs) -> (Limbs, Limbs) {
    if cmp_limbs(a, b) == Ordering::Less {
        return (ZERO_LIMBS, a);
    }
    // Simple bit-by-bit long division (256 iterations) — not the fastest,
    // but simple to verify correct, which matters more here than speed.
    let mut quotient = ZERO_LIMBS;
    let mut remainder = ZERO_LIMBS;
    for bit in (0..256).rev() {
        remainder = shl1(remainder);
        if get_bit(a, bit) {
            remainder[0] |= 1;
        }
        if cmp_limbs(remainder, b) != Ordering::Less {
            remainder = sub_limbs(remainder, b);
            set_bit(&mut quotient, bit);
        }
    }
    (quotient, remainder)
}

fn get_bit(l: Limbs, bit: usize) -> bool {
    let limb = bit / 64;
    let off = bit % 64;
    (l[limb] >> off) & 1 == 1
}

fn set_bit(l: &mut Limbs, bit: usize) {
    let limb = bit / 64;
    let off = bit % 64;
    l[limb] |= 1 << off;
}

fn shl1(l: Limbs) -> Limbs {
    let mut out = ZERO_LIMBS;
    let mut carry = 0u64;
    for i in 0..4 {
        out[i] = (l[i] << 1) | carry;
        carry = l[i] >> 63;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn i(n: i128) -> I256 {
        I256::from_i128(n)
    }

    // --- construction / round-trip ------------------------------------

    #[test]
    fn from_i128_round_trips() {
        for n in [0i128, 1, -1, 42, -42, i128::MAX, i128::MIN, i128::MAX - 1, i128::MIN + 1] {
            assert_eq!(I256::from_i128(n).to_i128(), Some(n), "n={n}");
        }
    }

    #[test]
    fn from_u128_round_trips() {
        for n in [0u128, 1, 42, u128::MAX, u128::MAX - 1, i128::MAX as u128, (i128::MAX as u128) + 1]
        {
            let x = I256::from_u128(n);
            assert!(!x.is_negative());
            // Cross-check via subtraction identity against i128 when it fits.
            if n <= i128::MAX as u128 {
                assert_eq!(x.to_i128(), Some(n as i128));
            } else {
                assert_eq!(x.to_i128(), None); // doesn't fit in i128, correctly reported
            }
        }
    }

    #[test]
    fn zero_is_canonical() {
        assert_eq!(I256::ZERO, I256::from_i128(0));
        assert_eq!(I256::from_i128(5).checked_add(I256::from_i128(-5)).unwrap(), I256::ZERO);
        assert!(!I256::ZERO.is_negative());
        assert!(!I256::ZERO.is_positive());
        assert!(I256::ZERO.is_zero());
    }

    // --- addition -------------------------------------------------------

    #[test]
    fn add_basic() {
        assert_eq!(i(2).checked_add(i(3)), Some(i(5)));
        assert_eq!(i(-2).checked_add(i(-3)), Some(i(-5)));
        assert_eq!(i(5).checked_add(i(-3)), Some(i(2)));
        assert_eq!(i(-5).checked_add(i(3)), Some(i(-2)));
        assert_eq!(i(3).checked_add(i(-3)), Some(i(0)));
    }

    #[test]
    fn add_commutative_and_associative_sampled() {
        let vals = [-1000i128, -7, -1, 0, 1, 7, 1000, i128::MAX / 2, i128::MIN / 2];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(i(a).checked_add(i(b)), i(b).checked_add(i(a)), "comm a={a} b={b}");
                for &c in &vals {
                    let lhs = i(a).checked_add(i(b)).unwrap().checked_add(i(c));
                    let rhs = i(a).checked_add(i(b).checked_add(i(c)).unwrap());
                    assert_eq!(lhs, rhs, "assoc a={a} b={b} c={c}");
                }
            }
        }
    }

    #[test]
    fn add_i128_extreme_no_overflow_in_i256() {
        // i128::MAX + i128::MAX overflows i128 but must succeed in I256 (it's
        // well within the 256-bit range) and round-trip back out is None
        // (doesn't fit i128) but the I256 arithmetic itself must not fail.
        let sum = i(i128::MAX).checked_add(i(i128::MAX));
        assert!(sum.is_some());
        assert_eq!(sum.unwrap().to_i128(), None);
    }

    #[test]
    fn add_i128_min_plus_min_no_i256_overflow() {
        let sum = i(i128::MIN).checked_add(i(i128::MIN));
        assert!(sum.is_some());
        assert_eq!(sum.unwrap().to_i128(), None);
    }

    // --- negation / abs ---------------------------------------------------

    #[test]
    fn neg_i128_min_does_not_overflow() {
        // The whole point: unlike i128::MIN.checked_neg() (which is None),
        // I256 negation of the i128::MIN-magnitude value succeeds exactly,
        // because I256's range is symmetric.
        let x = i(i128::MIN);
        let negated = x.neg();
        assert!(!negated.is_negative());
        assert_eq!(negated.checked_add(x), Some(I256::ZERO));
    }

    #[test]
    fn double_neg_is_identity() {
        for n in [0i128, 1, -1, 42, -42, i128::MAX, i128::MIN] {
            assert_eq!(i(n).neg().neg(), i(n));
        }
    }

    #[test]
    fn abs_never_negative() {
        for n in [0i128, 1, -1, 42, -42, i128::MAX, i128::MIN] {
            assert!(!i(n).abs().is_negative());
        }
        assert_eq!(i(-5).abs(), i(5));
        assert_eq!(i(5).abs(), i(5));
    }

    // --- subtraction --------------------------------------------------

    #[test]
    fn sub_basic() {
        assert_eq!(i(5).checked_sub(i(3)), Some(i(2)));
        assert_eq!(i(3).checked_sub(i(5)), Some(i(-2)));
        assert_eq!(i(-3).checked_sub(i(-5)), Some(i(2)));
    }

    // --- multiplication -------------------------------------------------

    #[test]
    fn mul_basic() {
        assert_eq!(i(3).checked_mul(i(4)), Some(i(12)));
        assert_eq!(i(-3).checked_mul(i(4)), Some(i(-12)));
        assert_eq!(i(-3).checked_mul(i(-4)), Some(i(12)));
        assert_eq!(i(0).checked_mul(i(12345)), Some(i(0)));
    }

    #[test]
    fn mul_commutative_sampled() {
        let vals = [-1000i128, -7, -1, 0, 1, 7, 1000, i128::MAX, i128::MIN];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(i(a).checked_mul(i(b)), i(b).checked_mul(i(a)), "a={a} b={b}");
            }
        }
    }

    #[test]
    fn mul_i128_extremes_do_not_overflow_i256() {
        // MAX * MAX and MIN * MIN both overflow i128 but must fit in 256 bits
        // (each operand needs <=128 bits, so the product needs <=256 bits).
        assert!(i(i128::MAX).checked_mul(i(i128::MAX)).is_some());
        assert!(i(i128::MIN).checked_mul(i(i128::MIN)).is_some());
        assert!(i(i128::MIN).checked_mul(i(i128::MAX)).is_some());
    }

    #[test]
    fn mul_known_answer_large() {
        let a = I256::from_u128(u128::MAX);
        let b = I256::from_i128(2);
        let got = a.checked_mul(b).unwrap();
        // u128::MAX * 2 = 2^129 - 2, which should equal (u128::MAX-1)<<1 style check:
        // verify via repeated addition instead of trusting mul itself.
        let via_add = a.checked_add(a).unwrap();
        assert_eq!(got, via_add);
    }

    #[test]
    fn mul_overflows_true_256_bit_range() {
        // (2^128) * (2^128) = 2^256, which does not fit in 256-bit signed magnitude
        // (max magnitude representable is 2^256 - 1... actually our mag is exactly
        // 256 bits unsigned, so 2^256 itself overflows).
        let big = I256::from_u128(u128::MAX).checked_add(I256::from_i128(1)).unwrap(); // 2^128
        assert_eq!(big.checked_mul(big), None);
    }

    // --- division ---------------------------------------------------------

    #[test]
    fn div_basic_truncates_toward_zero() {
        assert_eq!(i(7).checked_div(i(2)), Some(i(3)));
        assert_eq!(i(-7).checked_div(i(2)), Some(i(-3)));
        assert_eq!(i(7).checked_div(i(-2)), Some(i(-3)));
        assert_eq!(i(-7).checked_div(i(-2)), Some(i(3)));
        assert_eq!(i(6).checked_div(i(2)), Some(i(3)));
    }

    #[test]
    fn div_by_zero_is_none() {
        assert_eq!(i(5).checked_div(i(0)), None);
        assert_eq!(i(0).checked_div(i(0)), None);
    }

    #[test]
    fn div_identity() {
        for n in [1i128, -1, 42, -42, i128::MAX, i128::MIN, 12345] {
            assert_eq!(i(n).checked_div(i(1)), Some(i(n)));
            assert_eq!(i(n).checked_div(i(n)), Some(i(1)));
        }
    }

    // --- gcd ---------------------------------------------------------------

    #[test]
    fn gcd_known_answers() {
        assert_eq!(I256::gcd(i(12), i(18)), i(6));
        assert_eq!(I256::gcd(i(17), i(5)), i(1));
        assert_eq!(I256::gcd(i(0), i(5)), i(5));
        assert_eq!(I256::gcd(i(5), i(0)), i(5));
        assert_eq!(I256::gcd(i(0), i(0)), i(0));
        assert_eq!(I256::gcd(i(-12), i(18)), i(6)); // magnitude-based
        assert_eq!(I256::gcd(i(-12), i(-18)), i(6));
    }

    #[test]
    fn gcd_divides_both_sampled() {
        let vals = [1i128, 2, 3, 6, 7, 12, 18, 100, 97, 128, 1000, i128::MAX];
        for &a in &vals {
            for &b in &vals {
                let g = I256::gcd(i(a), i(b));
                if !g.is_zero() {
                    let (_, ra) = div_rem_limbs(i(a).mag, g.mag);
                    let (_, rb) = div_rem_limbs(i(b).mag, g.mag);
                    assert_eq!(ra, ZERO_LIMBS, "gcd({a},{b})={g:?} doesn't divide a");
                    assert_eq!(rb, ZERO_LIMBS, "gcd({a},{b})={g:?} doesn't divide b");
                }
            }
        }
    }

    // --- comparison ---------------------------------------------------------

    #[test]
    fn cmp_matches_i128_sampled() {
        let vals = [-1000i128, -7, -1, 0, 1, 7, 1000, i128::MAX, i128::MIN, i128::MAX - 1];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(i(a).cmp(&i(b)), a.cmp(&b), "a={a} b={b}");
            }
        }
    }

    // --- sign edge cases at i128::MIN/MAX and u128::MAX --------------------

    #[test]
    fn i128_min_max_arithmetic_round_trips() {
        let min = i(i128::MIN);
        let max = i(i128::MAX);
        assert_eq!(min.neg().to_i128(), None); // 2^127 doesn't fit i128
        assert_eq!(max.checked_add(i(1)).unwrap().to_i128(), None); // i128::MAX+1 doesn't fit
        assert_eq!(min.checked_sub(i(1)).unwrap().to_i128(), None); // i128::MIN-1 doesn't fit
        assert_eq!(max.checked_sub(i(1)).unwrap().to_i128(), Some(i128::MAX - 1));
        assert_eq!(min.checked_add(i(1)).unwrap().to_i128(), Some(i128::MIN + 1));
    }

    #[test]
    fn u128_max_representable_and_arithmetic() {
        let u = I256::from_u128(u128::MAX);
        assert_eq!(u.checked_sub(I256::from_u128(u128::MAX)), Some(I256::ZERO));
        let plus_one = u.checked_add(i(1)).unwrap();
        assert_eq!(plus_one.to_i128(), None); // 2^128 doesn't fit i128 either
        // u128::MAX * u128::MAX must not overflow I256 (fits in 256 bits: needs 256 bits exactly... check).
        assert!(u.checked_mul(u).is_some());
    }

    #[test]
    fn overflow_to_error_never_panics_and_reports_none() {
        // Construct a value near the top of I256's own range and push it over.
        let near_top = I256::from_u128(u128::MAX).checked_mul(I256::from_u128(u128::MAX)).unwrap();
        // near_top ~ 2^256 - 2^129 + 1, still fits (just barely, magnitude < 2^256).
        // Multiplying it by anything > 1 should overflow and return None, not panic.
        assert_eq!(near_top.checked_mul(i(2)), None);
        assert_eq!(near_top.checked_mul(i(1)), Some(near_top));
    }

    #[test]
    fn sub_limbs_and_div_rem_agree_with_known_values() {
        let (q, r) = div_rem_limbs(limbs_from_u128(100), limbs_from_u128(7));
        assert_eq!(limbs_to_u128_checked(q), Some(14));
        assert_eq!(limbs_to_u128_checked(r), Some(2));
    }
}
