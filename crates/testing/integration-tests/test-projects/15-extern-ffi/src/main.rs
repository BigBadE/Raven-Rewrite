// Test external FFI declarations
// NOTE: This test project is for demonstrating FFI syntax parsing
// External functions cannot actually be called without linking against
// a library that provides them

extern "C" {
    fn custom_add(a: i64, b: i64) -> i64;
    fn get_forty_two() -> i64;
}

fn main() -> i64 {
    // Don't actually call external functions in tests
    // Just return a known value to verify compilation
    42
}
