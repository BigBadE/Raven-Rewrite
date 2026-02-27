//! Arithmetic intrinsics
//!
//! Intrinsics for overflow-checked arithmetic, bit manipulation, and rotation.

/// Arithmetic intrinsic descriptor
#[derive(Debug, Clone)]
pub struct ArithmeticIntrinsic {
    /// Intrinsic name
    pub name: &'static str,
    /// Number of arguments
    pub arg_count: usize,
    /// Whether this returns a tuple (value, overflow_flag)
    pub returns_tuple: bool,
}

impl ArithmeticIntrinsic {
    /// add_with_overflow<T>(a: T, b: T) -> (T, bool)
    pub const ADD_WITH_OVERFLOW: Self = Self {
        name: "add_with_overflow",
        arg_count: 2,
        returns_tuple: true,
    };

    /// sub_with_overflow<T>(a: T, b: T) -> (T, bool)
    pub const SUB_WITH_OVERFLOW: Self = Self {
        name: "sub_with_overflow",
        arg_count: 2,
        returns_tuple: true,
    };

    /// mul_with_overflow<T>(a: T, b: T) -> (T, bool)
    pub const MUL_WITH_OVERFLOW: Self = Self {
        name: "mul_with_overflow",
        arg_count: 2,
        returns_tuple: true,
    };

    /// wrapping_add<T>(a: T, b: T) -> T
    pub const WRAPPING_ADD: Self = Self {
        name: "wrapping_add",
        arg_count: 2,
        returns_tuple: false,
    };

    /// wrapping_sub<T>(a: T, b: T) -> T
    pub const WRAPPING_SUB: Self = Self {
        name: "wrapping_sub",
        arg_count: 2,
        returns_tuple: false,
    };

    /// wrapping_mul<T>(a: T, b: T) -> T
    pub const WRAPPING_MUL: Self = Self {
        name: "wrapping_mul",
        arg_count: 2,
        returns_tuple: false,
    };

    /// saturating_add<T>(a: T, b: T) -> T
    pub const SATURATING_ADD: Self = Self {
        name: "saturating_add",
        arg_count: 2,
        returns_tuple: false,
    };

    /// saturating_sub<T>(a: T, b: T) -> T
    pub const SATURATING_SUB: Self = Self {
        name: "saturating_sub",
        arg_count: 2,
        returns_tuple: false,
    };

    /// unchecked_add<T>(a: T, b: T) -> T (UB on overflow)
    pub const UNCHECKED_ADD: Self = Self {
        name: "unchecked_add",
        arg_count: 2,
        returns_tuple: false,
    };

    /// unchecked_sub<T>(a: T, b: T) -> T (UB on overflow)
    pub const UNCHECKED_SUB: Self = Self {
        name: "unchecked_sub",
        arg_count: 2,
        returns_tuple: false,
    };

    /// unchecked_mul<T>(a: T, b: T) -> T (UB on overflow)
    pub const UNCHECKED_MUL: Self = Self {
        name: "unchecked_mul",
        arg_count: 2,
        returns_tuple: false,
    };

    /// unchecked_div<T>(a: T, b: T) -> T (UB on division by zero)
    pub const UNCHECKED_DIV: Self = Self {
        name: "unchecked_div",
        arg_count: 2,
        returns_tuple: false,
    };

    /// exact_div<T>(a: T, b: T) -> T (UB if not evenly divisible)
    pub const EXACT_DIV: Self = Self {
        name: "exact_div",
        arg_count: 2,
        returns_tuple: false,
    };

    /// rotate_left<T>(value: T, shift: u32) -> T
    pub const ROTATE_LEFT: Self = Self {
        name: "rotate_left",
        arg_count: 2,
        returns_tuple: false,
    };

    /// rotate_right<T>(value: T, shift: u32) -> T
    pub const ROTATE_RIGHT: Self = Self {
        name: "rotate_right",
        arg_count: 2,
        returns_tuple: false,
    };

    /// ctlz<T>(value: T) -> u32 (count leading zeros)
    pub const CTLZ: Self = Self {
        name: "ctlz",
        arg_count: 1,
        returns_tuple: false,
    };

    /// cttz<T>(value: T) -> u32 (count trailing zeros)
    pub const CTTZ: Self = Self {
        name: "cttz",
        arg_count: 1,
        returns_tuple: false,
    };

    /// ctpop<T>(value: T) -> u32 (count ones / population count)
    pub const CTPOP: Self = Self {
        name: "ctpop",
        arg_count: 1,
        returns_tuple: false,
    };

    /// bitreverse<T>(value: T) -> T (reverse bits)
    pub const BITREVERSE: Self = Self {
        name: "bitreverse",
        arg_count: 1,
        returns_tuple: false,
    };

    /// bswap<T>(value: T) -> T (byte swap)
    pub const BSWAP: Self = Self {
        name: "bswap",
        arg_count: 1,
        returns_tuple: false,
    };
}
