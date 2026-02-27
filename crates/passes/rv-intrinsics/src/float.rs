//! Float intrinsics
//!
//! Intrinsics for floating-point mathematical operations.

/// Float intrinsic descriptor
#[derive(Debug, Clone)]
pub struct FloatIntrinsic {
    /// Intrinsic name
    pub name: &'static str,
    /// Number of arguments
    pub arg_count: usize,
    /// Whether this is for f32 (true) or f64 (false)
    pub is_f32: bool,
}

impl FloatIntrinsic {
    /// sqrtf32(x: f32) -> f32
    pub const SQRTF32: Self = Self { name: "sqrtf32", arg_count: 1, is_f32: true };
    /// sqrtf64(x: f64) -> f64
    pub const SQRTF64: Self = Self { name: "sqrtf64", arg_count: 1, is_f32: false };

    /// sinf32(x: f32) -> f32
    pub const SINF32: Self = Self { name: "sinf32", arg_count: 1, is_f32: true };
    /// sinf64(x: f64) -> f64
    pub const SINF64: Self = Self { name: "sinf64", arg_count: 1, is_f32: false };

    /// cosf32(x: f32) -> f32
    pub const COSF32: Self = Self { name: "cosf32", arg_count: 1, is_f32: true };
    /// cosf64(x: f64) -> f64
    pub const COSF64: Self = Self { name: "cosf64", arg_count: 1, is_f32: false };

    /// powf32(x: f32, y: f32) -> f32
    pub const POWF32: Self = Self { name: "powf32", arg_count: 2, is_f32: true };
    /// powf64(x: f64, y: f64) -> f64
    pub const POWF64: Self = Self { name: "powf64", arg_count: 2, is_f32: false };

    /// expf32(x: f32) -> f32
    pub const EXPF32: Self = Self { name: "expf32", arg_count: 1, is_f32: true };
    /// expf64(x: f64) -> f64
    pub const EXPF64: Self = Self { name: "expf64", arg_count: 1, is_f32: false };

    /// logf32(x: f32) -> f32
    pub const LOGF32: Self = Self { name: "logf32", arg_count: 1, is_f32: true };
    /// logf64(x: f64) -> f64
    pub const LOGF64: Self = Self { name: "logf64", arg_count: 1, is_f32: false };

    /// floorf32(x: f32) -> f32
    pub const FLOORF32: Self = Self { name: "floorf32", arg_count: 1, is_f32: true };
    /// floorf64(x: f64) -> f64
    pub const FLOORF64: Self = Self { name: "floorf64", arg_count: 1, is_f32: false };

    /// ceilf32(x: f32) -> f32
    pub const CEILF32: Self = Self { name: "ceilf32", arg_count: 1, is_f32: true };
    /// ceilf64(x: f64) -> f64
    pub const CEILF64: Self = Self { name: "ceilf64", arg_count: 1, is_f32: false };

    /// truncf32(x: f32) -> f32
    pub const TRUNCF32: Self = Self { name: "truncf32", arg_count: 1, is_f32: true };
    /// truncf64(x: f64) -> f64
    pub const TRUNCF64: Self = Self { name: "truncf64", arg_count: 1, is_f32: false };

    /// roundf32(x: f32) -> f32
    pub const ROUNDF32: Self = Self { name: "roundf32", arg_count: 1, is_f32: true };
    /// roundf64(x: f64) -> f64
    pub const ROUNDF64: Self = Self { name: "roundf64", arg_count: 1, is_f32: false };

    /// fmaf32(a: f32, b: f32, c: f32) -> f32 (fused multiply-add: a * b + c)
    pub const FMAF32: Self = Self { name: "fmaf32", arg_count: 3, is_f32: true };
    /// fmaf64(a: f64, b: f64, c: f64) -> f64
    pub const FMAF64: Self = Self { name: "fmaf64", arg_count: 3, is_f32: false };
}
