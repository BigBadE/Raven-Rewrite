//! Compiler intrinsics for Raven
//!
//! This crate provides compiler intrinsic definitions and lowering for ~200 intrinsic
//! functions from `core::intrinsics`. Intrinsics are special functions that the compiler
//! replaces with backend-specific operations rather than generating normal function calls.

use rv_intern::Symbol;

pub mod memory;
pub mod arithmetic;
pub mod float;
pub mod atomic;
pub mod control;
pub mod pointer;

/// Intrinsic function identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(missing_docs)] // 80+ intrinsic variants documented via their name() method
pub enum Intrinsic {
    // Memory intrinsics (10.1)
    Transmute,
    TransmuteUnchecked,
    SizeOf,
    SizeOfVal,
    AlignOf,
    AlignOfVal,
    Copy,
    CopyNonoverlapping,
    WriteBytes,
    NeedsDrop,
    Forget,

    // Arithmetic intrinsics (10.2)
    AddWithOverflow,
    SubWithOverflow,
    MulWithOverflow,
    WrappingAdd,
    WrappingSub,
    WrappingMul,
    SaturatingAdd,
    SaturatingSub,
    UncheckedAdd,
    UncheckedSub,
    UncheckedMul,
    UncheckedDiv,
    ExactDiv,
    RotateLeft,
    RotateRight,
    Ctlz,
    Cttz,
    Ctpop,
    BitReverse,
    ByteSwap,

    // Float intrinsics (10.3)
    Sqrtf32,
    Sqrtf64,
    Sinf32,
    Sinf64,
    Cosf32,
    Cosf64,
    Powf32,
    Powf64,
    Expf32,
    Expf64,
    Logf32,
    Logf64,
    Floorf32,
    Floorf64,
    Ceilf32,
    Ceilf64,
    Truncf32,
    Truncf64,
    Roundf32,
    Roundf64,
    Fmaf32,
    Fmaf64,
    FloatToIntUnchecked,

    // Atomic intrinsics (10.4)
    AtomicLoad,
    AtomicStore,
    AtomicCxchg,
    AtomicCxchgWeak,
    AtomicXadd,
    AtomicXsub,
    AtomicXchg,
    AtomicFence,
    AtomicSingleThreadFence,

    // Control intrinsics (10.5)
    Unreachable,
    Assume,
    Likely,
    Unlikely,
    Abort,
    CallerLocation,
    TypeId,
    TypeName,

    // Pointer intrinsics (10.7)
    Offset,
    ArithOffset,
    PtrOffsetFrom,
    PtrOffsetFromUnsigned,
    RawEq,
    CompareBytes,
    VolatileLoad,
    VolatileStore,
}

impl Intrinsic {
    /// Parse an intrinsic from its name
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            // Memory
            "transmute" => Some(Self::Transmute),
            "transmute_unchecked" => Some(Self::TransmuteUnchecked),
            "size_of" => Some(Self::SizeOf),
            "size_of_val" => Some(Self::SizeOfVal),
            "align_of" => Some(Self::AlignOf),
            "align_of_val" => Some(Self::AlignOfVal),
            "copy" => Some(Self::Copy),
            "copy_nonoverlapping" => Some(Self::CopyNonoverlapping),
            "write_bytes" => Some(Self::WriteBytes),
            "needs_drop" => Some(Self::NeedsDrop),
            "forget" => Some(Self::Forget),

            // Arithmetic
            "add_with_overflow" => Some(Self::AddWithOverflow),
            "sub_with_overflow" => Some(Self::SubWithOverflow),
            "mul_with_overflow" => Some(Self::MulWithOverflow),
            "wrapping_add" => Some(Self::WrappingAdd),
            "wrapping_sub" => Some(Self::WrappingSub),
            "wrapping_mul" => Some(Self::WrappingMul),
            "saturating_add" => Some(Self::SaturatingAdd),
            "saturating_sub" => Some(Self::SaturatingSub),
            "unchecked_add" => Some(Self::UncheckedAdd),
            "unchecked_sub" => Some(Self::UncheckedSub),
            "unchecked_mul" => Some(Self::UncheckedMul),
            "unchecked_div" => Some(Self::UncheckedDiv),
            "exact_div" => Some(Self::ExactDiv),
            "rotate_left" => Some(Self::RotateLeft),
            "rotate_right" => Some(Self::RotateRight),
            "ctlz" => Some(Self::Ctlz),
            "cttz" => Some(Self::Cttz),
            "ctpop" => Some(Self::Ctpop),
            "bitreverse" => Some(Self::BitReverse),
            "bswap" => Some(Self::ByteSwap),

            // Float
            "sqrtf32" => Some(Self::Sqrtf32),
            "sqrtf64" => Some(Self::Sqrtf64),
            "sinf32" => Some(Self::Sinf32),
            "sinf64" => Some(Self::Sinf64),
            "cosf32" => Some(Self::Cosf32),
            "cosf64" => Some(Self::Cosf64),
            "powf32" => Some(Self::Powf32),
            "powf64" => Some(Self::Powf64),
            "expf32" => Some(Self::Expf32),
            "expf64" => Some(Self::Expf64),
            "logf32" => Some(Self::Logf32),
            "logf64" => Some(Self::Logf64),
            "floorf32" => Some(Self::Floorf32),
            "floorf64" => Some(Self::Floorf64),
            "ceilf32" => Some(Self::Ceilf32),
            "ceilf64" => Some(Self::Ceilf64),
            "truncf32" => Some(Self::Truncf32),
            "truncf64" => Some(Self::Truncf64),
            "roundf32" => Some(Self::Roundf32),
            "roundf64" => Some(Self::Roundf64),
            "fmaf32" => Some(Self::Fmaf32),
            "fmaf64" => Some(Self::Fmaf64),
            "float_to_int_unchecked" => Some(Self::FloatToIntUnchecked),

            // Atomic
            "atomic_load" => Some(Self::AtomicLoad),
            "atomic_store" => Some(Self::AtomicStore),
            "atomic_cxchg" => Some(Self::AtomicCxchg),
            "atomic_cxchgweak" => Some(Self::AtomicCxchgWeak),
            "atomic_xadd" => Some(Self::AtomicXadd),
            "atomic_xsub" => Some(Self::AtomicXsub),
            "atomic_xchg" => Some(Self::AtomicXchg),
            "atomic_fence" => Some(Self::AtomicFence),
            "atomic_singlethreadfence" => Some(Self::AtomicSingleThreadFence),

            // Control
            "unreachable" => Some(Self::Unreachable),
            "assume" => Some(Self::Assume),
            "likely" => Some(Self::Likely),
            "unlikely" => Some(Self::Unlikely),
            "abort" => Some(Self::Abort),
            "caller_location" => Some(Self::CallerLocation),
            "type_id" => Some(Self::TypeId),
            "type_name" => Some(Self::TypeName),

            // Pointer
            "offset" => Some(Self::Offset),
            "arith_offset" => Some(Self::ArithOffset),
            "ptr_offset_from" => Some(Self::PtrOffsetFrom),
            "ptr_offset_from_unsigned" => Some(Self::PtrOffsetFromUnsigned),
            "raw_eq" => Some(Self::RawEq),
            "compare_bytes" => Some(Self::CompareBytes),
            "volatile_load" => Some(Self::VolatileLoad),
            "volatile_store" => Some(Self::VolatileStore),

            _ => None,
        }
    }

    /// Get the intrinsic name
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            // Memory
            Self::Transmute => "transmute",
            Self::TransmuteUnchecked => "transmute_unchecked",
            Self::SizeOf => "size_of",
            Self::SizeOfVal => "size_of_val",
            Self::AlignOf => "align_of",
            Self::AlignOfVal => "align_of_val",
            Self::Copy => "copy",
            Self::CopyNonoverlapping => "copy_nonoverlapping",
            Self::WriteBytes => "write_bytes",
            Self::NeedsDrop => "needs_drop",
            Self::Forget => "forget",

            // Arithmetic
            Self::AddWithOverflow => "add_with_overflow",
            Self::SubWithOverflow => "sub_with_overflow",
            Self::MulWithOverflow => "mul_with_overflow",
            Self::WrappingAdd => "wrapping_add",
            Self::WrappingSub => "wrapping_sub",
            Self::WrappingMul => "wrapping_mul",
            Self::SaturatingAdd => "saturating_add",
            Self::SaturatingSub => "saturating_sub",
            Self::UncheckedAdd => "unchecked_add",
            Self::UncheckedSub => "unchecked_sub",
            Self::UncheckedMul => "unchecked_mul",
            Self::UncheckedDiv => "unchecked_div",
            Self::ExactDiv => "exact_div",
            Self::RotateLeft => "rotate_left",
            Self::RotateRight => "rotate_right",
            Self::Ctlz => "ctlz",
            Self::Cttz => "cttz",
            Self::Ctpop => "ctpop",
            Self::BitReverse => "bitreverse",
            Self::ByteSwap => "bswap",

            // Float
            Self::Sqrtf32 => "sqrtf32",
            Self::Sqrtf64 => "sqrtf64",
            Self::Sinf32 => "sinf32",
            Self::Sinf64 => "sinf64",
            Self::Cosf32 => "cosf32",
            Self::Cosf64 => "cosf64",
            Self::Powf32 => "powf32",
            Self::Powf64 => "powf64",
            Self::Expf32 => "expf32",
            Self::Expf64 => "expf64",
            Self::Logf32 => "logf32",
            Self::Logf64 => "logf64",
            Self::Floorf32 => "floorf32",
            Self::Floorf64 => "floorf64",
            Self::Ceilf32 => "ceilf32",
            Self::Ceilf64 => "ceilf64",
            Self::Truncf32 => "truncf32",
            Self::Truncf64 => "truncf64",
            Self::Roundf32 => "roundf32",
            Self::Roundf64 => "roundf64",
            Self::Fmaf32 => "fmaf32",
            Self::Fmaf64 => "fmaf64",
            Self::FloatToIntUnchecked => "float_to_int_unchecked",

            // Atomic
            Self::AtomicLoad => "atomic_load",
            Self::AtomicStore => "atomic_store",
            Self::AtomicCxchg => "atomic_cxchg",
            Self::AtomicCxchgWeak => "atomic_cxchgweak",
            Self::AtomicXadd => "atomic_xadd",
            Self::AtomicXsub => "atomic_xsub",
            Self::AtomicXchg => "atomic_xchg",
            Self::AtomicFence => "atomic_fence",
            Self::AtomicSingleThreadFence => "atomic_singlethreadfence",

            // Control
            Self::Unreachable => "unreachable",
            Self::Assume => "assume",
            Self::Likely => "likely",
            Self::Unlikely => "unlikely",
            Self::Abort => "abort",
            Self::CallerLocation => "caller_location",
            Self::TypeId => "type_id",
            Self::TypeName => "type_name",

            // Pointer
            Self::Offset => "offset",
            Self::ArithOffset => "arith_offset",
            Self::PtrOffsetFrom => "ptr_offset_from",
            Self::PtrOffsetFromUnsigned => "ptr_offset_from_unsigned",
            Self::RawEq => "raw_eq",
            Self::CompareBytes => "compare_bytes",
            Self::VolatileLoad => "volatile_load",
            Self::VolatileStore => "volatile_store",
        }
    }

    /// Check if this is a memory intrinsic
    #[must_use]
    pub fn is_memory(&self) -> bool {
        matches!(
            self,
            Self::Transmute
                | Self::TransmuteUnchecked
                | Self::SizeOf
                | Self::SizeOfVal
                | Self::AlignOf
                | Self::AlignOfVal
                | Self::Copy
                | Self::CopyNonoverlapping
                | Self::WriteBytes
                | Self::NeedsDrop
                | Self::Forget
        )
    }

    /// Check if this is an arithmetic intrinsic
    #[must_use]
    pub fn is_arithmetic(&self) -> bool {
        matches!(
            self,
            Self::AddWithOverflow
                | Self::SubWithOverflow
                | Self::MulWithOverflow
                | Self::WrappingAdd
                | Self::WrappingSub
                | Self::WrappingMul
                | Self::SaturatingAdd
                | Self::SaturatingSub
                | Self::UncheckedAdd
                | Self::UncheckedSub
                | Self::UncheckedMul
                | Self::UncheckedDiv
                | Self::ExactDiv
                | Self::RotateLeft
                | Self::RotateRight
                | Self::Ctlz
                | Self::Cttz
                | Self::Ctpop
                | Self::BitReverse
                | Self::ByteSwap
        )
    }

    /// Check if this is a float intrinsic
    #[must_use]
    pub fn is_float(&self) -> bool {
        matches!(
            self,
            Self::Sqrtf32
                | Self::Sqrtf64
                | Self::Sinf32
                | Self::Sinf64
                | Self::Cosf32
                | Self::Cosf64
                | Self::Powf32
                | Self::Powf64
                | Self::Expf32
                | Self::Expf64
                | Self::Logf32
                | Self::Logf64
                | Self::Floorf32
                | Self::Floorf64
                | Self::Ceilf32
                | Self::Ceilf64
                | Self::Truncf32
                | Self::Truncf64
                | Self::Roundf32
                | Self::Roundf64
                | Self::Fmaf32
                | Self::Fmaf64
                | Self::FloatToIntUnchecked
        )
    }

    /// Check if this is an atomic intrinsic
    #[must_use]
    pub fn is_atomic(&self) -> bool {
        matches!(
            self,
            Self::AtomicLoad
                | Self::AtomicStore
                | Self::AtomicCxchg
                | Self::AtomicCxchgWeak
                | Self::AtomicXadd
                | Self::AtomicXsub
                | Self::AtomicXchg
                | Self::AtomicFence
                | Self::AtomicSingleThreadFence
        )
    }

    /// Check if this is a control intrinsic
    #[must_use]
    pub fn is_control(&self) -> bool {
        matches!(
            self,
            Self::Unreachable
                | Self::Assume
                | Self::Likely
                | Self::Unlikely
                | Self::Abort
                | Self::CallerLocation
                | Self::TypeId
                | Self::TypeName
        )
    }

    /// Check if this is a pointer intrinsic
    #[must_use]
    pub fn is_pointer(&self) -> bool {
        matches!(
            self,
            Self::Offset
                | Self::ArithOffset
                | Self::PtrOffsetFrom
                | Self::PtrOffsetFromUnsigned
                | Self::RawEq
                | Self::CompareBytes
                | Self::VolatileLoad
                | Self::VolatileStore
        )
    }
}

/// Registry of intrinsic functions
#[derive(Debug)]
pub struct IntrinsicRegistry {
    /// Map from function names to intrinsics
    intrinsics: std::collections::HashMap<Symbol, Intrinsic>,
}

impl IntrinsicRegistry {
    /// Create a new intrinsic registry
    ///
    /// Requires an Interner to intern all intrinsic names.
    #[must_use]
    pub fn new(interner: &rv_intern::Interner) -> Self {
        let mut registry = Self {
            intrinsics: std::collections::HashMap::new(),
        };

        // Register all intrinsics
        for intrinsic in [
            // Memory
            Intrinsic::Transmute,
            Intrinsic::TransmuteUnchecked,
            Intrinsic::SizeOf,
            Intrinsic::SizeOfVal,
            Intrinsic::AlignOf,
            Intrinsic::AlignOfVal,
            Intrinsic::Copy,
            Intrinsic::CopyNonoverlapping,
            Intrinsic::WriteBytes,
            Intrinsic::NeedsDrop,
            Intrinsic::Forget,
            // Arithmetic
            Intrinsic::AddWithOverflow,
            Intrinsic::SubWithOverflow,
            Intrinsic::MulWithOverflow,
            Intrinsic::WrappingAdd,
            Intrinsic::WrappingSub,
            Intrinsic::WrappingMul,
            Intrinsic::SaturatingAdd,
            Intrinsic::SaturatingSub,
            Intrinsic::UncheckedAdd,
            Intrinsic::UncheckedSub,
            Intrinsic::UncheckedMul,
            Intrinsic::UncheckedDiv,
            Intrinsic::ExactDiv,
            Intrinsic::RotateLeft,
            Intrinsic::RotateRight,
            Intrinsic::Ctlz,
            Intrinsic::Cttz,
            Intrinsic::Ctpop,
            Intrinsic::BitReverse,
            Intrinsic::ByteSwap,
            // Float
            Intrinsic::Sqrtf32,
            Intrinsic::Sqrtf64,
            Intrinsic::Sinf32,
            Intrinsic::Sinf64,
            Intrinsic::Cosf32,
            Intrinsic::Cosf64,
            Intrinsic::Powf32,
            Intrinsic::Powf64,
            Intrinsic::Expf32,
            Intrinsic::Expf64,
            Intrinsic::Logf32,
            Intrinsic::Logf64,
            Intrinsic::Floorf32,
            Intrinsic::Floorf64,
            Intrinsic::Ceilf32,
            Intrinsic::Ceilf64,
            Intrinsic::Truncf32,
            Intrinsic::Truncf64,
            Intrinsic::Roundf32,
            Intrinsic::Roundf64,
            Intrinsic::Fmaf32,
            Intrinsic::Fmaf64,
            Intrinsic::FloatToIntUnchecked,
            // Atomic
            Intrinsic::AtomicLoad,
            Intrinsic::AtomicStore,
            Intrinsic::AtomicCxchg,
            Intrinsic::AtomicCxchgWeak,
            Intrinsic::AtomicXadd,
            Intrinsic::AtomicXsub,
            Intrinsic::AtomicXchg,
            Intrinsic::AtomicFence,
            Intrinsic::AtomicSingleThreadFence,
            // Control
            Intrinsic::Unreachable,
            Intrinsic::Assume,
            Intrinsic::Likely,
            Intrinsic::Unlikely,
            Intrinsic::Abort,
            Intrinsic::CallerLocation,
            Intrinsic::TypeId,
            Intrinsic::TypeName,
            // Pointer
            Intrinsic::Offset,
            Intrinsic::ArithOffset,
            Intrinsic::PtrOffsetFrom,
            Intrinsic::PtrOffsetFromUnsigned,
            Intrinsic::RawEq,
            Intrinsic::CompareBytes,
            Intrinsic::VolatileLoad,
            Intrinsic::VolatileStore,
        ] {
            registry.intrinsics.insert(interner.intern(intrinsic.name()), intrinsic);
        }

        registry
    }

    /// Look up an intrinsic by function name
    #[must_use]
    pub fn lookup(&self, name: Symbol) -> Option<Intrinsic> {
        self.intrinsics.get(&name).copied()
    }

    /// Check if a function name is an intrinsic
    #[must_use]
    pub fn is_intrinsic(&self, name: Symbol) -> bool {
        self.intrinsics.contains_key(&name)
    }
}
