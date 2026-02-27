//! Control flow intrinsics
//!
//! Intrinsics for control flow hints, panics, and runtime type information.

/// Control intrinsic descriptor
#[derive(Debug, Clone)]
pub struct ControlIntrinsic {
    /// Intrinsic name
    pub name: &'static str,
    /// Number of arguments
    pub arg_count: usize,
    /// Whether this intrinsic terminates execution
    pub is_terminating: bool,
}

impl ControlIntrinsic {
    /// unreachable() -> !
    /// Hints to the compiler that this code path is unreachable (UB if reached)
    pub const UNREACHABLE: Self = Self {
        name: "unreachable",
        arg_count: 0,
        is_terminating: true,
    };

    /// assume(condition: bool)
    /// Hints to the optimizer that a condition is always true (UB if false)
    pub const ASSUME: Self = Self {
        name: "assume",
        arg_count: 1,
        is_terminating: false,
    };

    /// likely(condition: bool) -> bool
    /// Branch prediction hint: condition is likely true
    pub const LIKELY: Self = Self {
        name: "likely",
        arg_count: 1,
        is_terminating: false,
    };

    /// unlikely(condition: bool) -> bool
    /// Branch prediction hint: condition is likely false
    pub const UNLIKELY: Self = Self {
        name: "unlikely",
        arg_count: 1,
        is_terminating: false,
    };

    /// abort() -> !
    /// Immediately terminates the program
    pub const ABORT: Self = Self {
        name: "abort",
        arg_count: 0,
        is_terminating: true,
    };

    /// caller_location() -> &'static Location
    /// Returns the source location of the caller (for #[track_caller])
    pub const CALLER_LOCATION: Self = Self {
        name: "caller_location",
        arg_count: 0,
        is_terminating: false,
    };

    /// type_id<T>() -> u64
    /// Returns a unique identifier for the type T
    pub const TYPE_ID: Self = Self {
        name: "type_id",
        arg_count: 0,
        is_terminating: false,
    };

    /// type_name<T>() -> &'static str
    /// Returns the name of the type T
    pub const TYPE_NAME: Self = Self {
        name: "type_name",
        arg_count: 0,
        is_terminating: false,
    };
}

/// Panic handling infrastructure
#[derive(Debug, Clone)]
pub struct PanicRuntime {
    /// Whether panic-as-abort mode is enabled
    pub abort_on_panic: bool,
}

impl PanicRuntime {
    /// Create a new panic runtime with default settings
    #[must_use]
    pub fn new() -> Self {
        Self {
            abort_on_panic: false,
        }
    }

    /// Enable panic-as-abort mode
    pub fn set_abort_on_panic(&mut self, abort: bool) {
        self.abort_on_panic = abort;
    }
}

impl Default for PanicRuntime {
    fn default() -> Self {
        Self::new()
    }
}
