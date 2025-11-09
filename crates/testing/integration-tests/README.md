# Integration Tests

Integration tests for the Raven compiler using Magpie package manager.

## Structure

Tests are organized as Cargo projects in the `test-projects/` directory:

```
test-projects/
├── 01-basic-arithmetic/     # Tests for arithmetic operations
│   ├── Cargo.toml
│   └── src/main.rs
├── 02-control-flow/         # Tests for if expressions
│   ├── Cargo.toml
│   └── src/main.rs
└── 03-comparisons/          # Tests for comparison operators
    ├── Cargo.toml
    └── src/main.rs
```

Each project contains:
- `Cargo.toml` - Package manifest
- `src/main.rs` - Main source file with test functions

## Test Format

Test functions follow these conventions:
- Function names start with `test_`
- Return type is `bool`
- Return `true` for success, `false` for failure

Example:
```rust
#[test]
fn test_addition() -> bool {
    if 2 + 2 == 4 {
        true
    } else {
        false
    }
}
```

## Running Tests

The test runner (`tests/magpie_tests.rs`) automatically:
1. Discovers all projects in `test-projects/`
2. Runs `magpie test` on each project
3. Collects and reports results

Run with:
```bash
cargo test --package integration-tests
```

## Test Results

Current test coverage:

### 01-basic-arithmetic (5 tests)
- ✓ test_addition
- ✓ test_subtraction
- ✓ test_multiplication
- ✓ test_division
- ✓ test_complex_expression

### 02-control-flow (4 tests)
- ✓ test_if_true
- ✓ test_if_false
- ✓ test_nested_if
- ✓ test_if_with_arithmetic

### 03-comparisons (6 tests)
- ✓ test_less_than
- ✓ test_greater_than
- ✓ test_less_equal
- ✓ test_greater_equal
- ✓ test_equality
- ✓ test_inequality

**Total: 15 tests across 3 projects**

## Adding New Tests

To add a new test project:

1. Create a new directory in `test-projects/`
2. Add `Cargo.toml` with package metadata
3. Create `src/main.rs` with a `main()` function and test functions
4. Test functions will be automatically discovered and run

## Integration with Magpie

Tests use Magpie's backend system:
- **RavenBackend**: Runs the full compilation pipeline
  - Parse (tree-sitter) → HIR → Type Inference → MIR → Interpreter
- All tests execute through the same pipeline as production code
- Tests validate end-to-end compiler functionality
