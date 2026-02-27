//! Pointer intrinsics
//!
//! Intrinsics for pointer arithmetic, comparison, and volatile operations.

/// Pointer intrinsic descriptor
#[derive(Debug, Clone)]
pub struct PointerIntrinsic {
    /// Intrinsic name
    pub name: &'static str,
    /// Number of arguments
    pub arg_count: usize,
    /// Whether this is a volatile operation
    pub is_volatile: bool,
}

impl PointerIntrinsic {
    /// offset<T>(ptr: *const T, count: isize) -> *const T
    /// Calculates the offset from a pointer (wrapping semantics)
    pub const OFFSET: Self = Self {
        name: "offset",
        arg_count: 2,
        is_volatile: false,
    };

    /// arith_offset<T>(ptr: *const T, offset: isize) -> *const T
    /// Calculates the offset from a pointer (arithmetic semantics, UB on overflow)
    pub const ARITH_OFFSET: Self = Self {
        name: "arith_offset",
        arg_count: 2,
        is_volatile: false,
    };

    /// ptr_offset_from<T>(ptr: *const T, origin: *const T) -> isize
    /// Calculates the offset between two pointers (in units of T)
    pub const PTR_OFFSET_FROM: Self = Self {
        name: "ptr_offset_from",
        arg_count: 2,
        is_volatile: false,
    };

    /// ptr_offset_from_unsigned<T>(ptr: *const T, origin: *const T) -> usize
    /// Calculates the offset between two pointers (unsigned, UB if negative)
    pub const PTR_OFFSET_FROM_UNSIGNED: Self = Self {
        name: "ptr_offset_from_unsigned",
        arg_count: 2,
        is_volatile: false,
    };

    /// raw_eq<T>(a: &T, b: &T) -> bool
    /// Bitwise equality comparison (compares representation, not values)
    pub const RAW_EQ: Self = Self {
        name: "raw_eq",
        arg_count: 2,
        is_volatile: false,
    };

    /// compare_bytes(a: *const u8, b: *const u8, len: usize) -> i32
    /// Compare memory regions (like memcmp)
    pub const COMPARE_BYTES: Self = Self {
        name: "compare_bytes",
        arg_count: 3,
        is_volatile: false,
    };

    /// volatile_load<T>(ptr: *const T) -> T
    /// Performs a volatile read from a pointer
    pub const VOLATILE_LOAD: Self = Self {
        name: "volatile_load",
        arg_count: 1,
        is_volatile: true,
    };

    /// volatile_store<T>(ptr: *mut T, value: T)
    /// Performs a volatile write to a pointer
    pub const VOLATILE_STORE: Self = Self {
        name: "volatile_store",
        arg_count: 2,
        is_volatile: true,
    };
}
