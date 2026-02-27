//! Atomic intrinsics
//!
//! Intrinsics for atomic operations and memory ordering.

/// Memory ordering for atomic operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryOrdering {
    /// Relaxed ordering (no synchronization)
    Relaxed,
    /// Acquire ordering (synchronize on read)
    Acquire,
    /// Release ordering (synchronize on write)
    Release,
    /// Acquire-Release ordering (synchronize on both)
    AcqRel,
    /// Sequentially consistent ordering (total order)
    SeqCst,
}

impl MemoryOrdering {
    /// Parse memory ordering from string
    #[must_use]
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "Relaxed" => Some(Self::Relaxed),
            "Acquire" => Some(Self::Acquire),
            "Release" => Some(Self::Release),
            "AcqRel" => Some(Self::AcqRel),
            "SeqCst" => Some(Self::SeqCst),
            _ => None,
        }
    }
}

/// Atomic intrinsic descriptor
#[derive(Debug, Clone)]
pub struct AtomicIntrinsic {
    /// Intrinsic name
    pub name: &'static str,
    /// Number of arguments (excluding ordering)
    pub arg_count: usize,
    /// Whether this intrinsic returns a value
    pub returns_value: bool,
}

impl AtomicIntrinsic {
    /// atomic_load<T>(ptr: *const T, ordering: Ordering) -> T
    pub const ATOMIC_LOAD: Self = Self {
        name: "atomic_load",
        arg_count: 1,
        returns_value: true,
    };

    /// atomic_store<T>(ptr: *mut T, value: T, ordering: Ordering)
    pub const ATOMIC_STORE: Self = Self {
        name: "atomic_store",
        arg_count: 2,
        returns_value: false,
    };

    /// atomic_cxchg<T>(ptr: *mut T, old: T, new: T, success: Ordering, failure: Ordering) -> (T, bool)
    pub const ATOMIC_CXCHG: Self = Self {
        name: "atomic_cxchg",
        arg_count: 3,
        returns_value: true,
    };

    /// atomic_cxchgweak<T>(ptr: *mut T, old: T, new: T, success: Ordering, failure: Ordering) -> (T, bool)
    pub const ATOMIC_CXCHG_WEAK: Self = Self {
        name: "atomic_cxchgweak",
        arg_count: 3,
        returns_value: true,
    };

    /// atomic_xadd<T>(ptr: *mut T, value: T, ordering: Ordering) -> T
    pub const ATOMIC_XADD: Self = Self {
        name: "atomic_xadd",
        arg_count: 2,
        returns_value: true,
    };

    /// atomic_xsub<T>(ptr: *mut T, value: T, ordering: Ordering) -> T
    pub const ATOMIC_XSUB: Self = Self {
        name: "atomic_xsub",
        arg_count: 2,
        returns_value: true,
    };

    /// atomic_xchg<T>(ptr: *mut T, value: T, ordering: Ordering) -> T
    pub const ATOMIC_XCHG: Self = Self {
        name: "atomic_xchg",
        arg_count: 2,
        returns_value: true,
    };

    /// atomic_fence(ordering: Ordering)
    pub const ATOMIC_FENCE: Self = Self {
        name: "atomic_fence",
        arg_count: 0,
        returns_value: false,
    };

    /// atomic_singlethreadfence(ordering: Ordering)
    pub const ATOMIC_SINGLE_THREAD_FENCE: Self = Self {
        name: "atomic_singlethreadfence",
        arg_count: 0,
        returns_value: false,
    };
}
