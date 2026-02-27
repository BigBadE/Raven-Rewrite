//! Memory intrinsics
//!
//! Intrinsics for type manipulation, memory operations, and layout queries.

/// Memory intrinsic descriptor
#[derive(Debug, Clone)]
pub struct MemoryIntrinsic {
    /// Intrinsic name
    pub name: &'static str,
    /// Number of arguments
    pub arg_count: usize,
    /// Whether this intrinsic is const-evaluable
    pub is_const: bool,
}

impl MemoryIntrinsic {
    /// transmute<T, U>(value: T) -> U
    /// Reinterprets the bits of a value of one type as another type
    pub const TRANSMUTE: Self = Self {
        name: "transmute",
        arg_count: 1,
        is_const: true,
    };

    /// transmute_unchecked<T, U>(value: T) -> U
    /// Unchecked version of transmute (no size validation)
    pub const TRANSMUTE_UNCHECKED: Self = Self {
        name: "transmute_unchecked",
        arg_count: 1,
        is_const: true,
    };

    /// size_of<T>() -> usize
    /// Returns the size in bytes of a type
    pub const SIZE_OF: Self = Self {
        name: "size_of",
        arg_count: 0,
        is_const: true,
    };

    /// size_of_val<T: ?Sized>(value: &T) -> usize
    /// Returns the size in bytes of the pointed-to value
    pub const SIZE_OF_VAL: Self = Self {
        name: "size_of_val",
        arg_count: 1,
        is_const: false,
    };

    /// align_of<T>() -> usize
    /// Returns the alignment in bytes of a type
    pub const ALIGN_OF: Self = Self {
        name: "align_of",
        arg_count: 0,
        is_const: true,
    };

    /// align_of_val<T: ?Sized>(value: &T) -> usize
    /// Returns the alignment in bytes of the pointed-to value
    pub const ALIGN_OF_VAL: Self = Self {
        name: "align_of_val",
        arg_count: 1,
        is_const: false,
    };

    /// copy<T>(src: *const T, dst: *mut T, count: usize)
    /// Copies count * size_of::<T>() bytes from src to dst (regions may overlap)
    pub const COPY: Self = Self {
        name: "copy",
        arg_count: 3,
        is_const: false,
    };

    /// copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize)
    /// Copies count * size_of::<T>() bytes from src to dst (regions must not overlap)
    pub const COPY_NONOVERLAPPING: Self = Self {
        name: "copy_nonoverlapping",
        arg_count: 3,
        is_const: false,
    };

    /// write_bytes<T>(dst: *mut T, val: u8, count: usize)
    /// Sets count * size_of::<T>() bytes starting at dst to val (like memset)
    pub const WRITE_BYTES: Self = Self {
        name: "write_bytes",
        arg_count: 3,
        is_const: false,
    };

    /// needs_drop<T>() -> bool
    /// Returns true if dropping values of type T matters
    pub const NEEDS_DROP: Self = Self {
        name: "needs_drop",
        arg_count: 0,
        is_const: true,
    };

    /// forget<T>(value: T)
    /// Takes ownership of a value and forgets it without running its destructor
    pub const FORGET: Self = Self {
        name: "forget",
        arg_count: 1,
        is_const: false,
    };
}
