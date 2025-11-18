# Raven Compiler Test Suite

Comprehensive test suite using `compiletest_rs` - the same testing framework used by the Rust compiler (`rustc`).

This test suite provides systematic validation of the Raven compiler's behavior across multiple dimensions:
- **Error diagnostics quality**
- **Language semantics enforcement**
- **Feature correctness and completeness**
- **Edge case handling**

## Overview

The test suite is organized into four main categories, each serving a distinct purpose in ensuring compiler correctness and quality.

## Test Categories

### 1. UI Tests (`tests/ui/`)

**Purpose**: Validate error messages and compiler diagnostics.

UI tests ensure that the compiler produces clear, helpful error messages when encountering invalid code. Each `.rs` file has a matching `.stderr` file containing the expected compiler output.

**Format**:
- Use `//~ ERROR` annotations to mark expected error locations
- Include a `.stderr` file with exact expected output
- Test both error detection and error message quality

**Example**:
```rust
// tests/ui/type-mismatch-basic.rs
fn main() -> i64 {
    let x: i64 = "string"; //~ ERROR type mismatch
    x
}
```

Expected stderr:
```
error: type mismatch: expected i64, found String
 --> tests/ui/type-mismatch-basic.rs:2:18
  |
2 |     let x: i64 = "string";
  |                  ^^^^^^^^ expected i64, found String
```

**Current Tests** (15 tests):
- `type-mismatch-basic.rs` - Basic type mismatch in variable binding
- `type-mismatch-function-arg.rs` - Type mismatch in function arguments
- `undefined-variable.rs` - Use of undefined variables
- `undefined-function.rs` - Call to undefined functions
- `borrow-conflict.rs` - Conflicting mutable and immutable borrows
- `use-after-move.rs` - Use of moved values
- `lifetime-dangling-ref.rs` - Dangling reference detection
- `return-type-mismatch.rs` - Function return type mismatches
- `if-else-type-mismatch.rs` - Incompatible if-else branch types
- `method-not-found.rs` - Method resolution failures
- `field-not-found.rs` - Struct field access errors
- `match-pattern-type-mismatch.rs` - Pattern type mismatches
- `generic-type-param-count.rs` - Wrong number of type parameters
- `name-resolution-ambiguous.rs` - Duplicate definitions
- `struct-field-missing.rs` - Missing struct fields in initialization

### 2. Compile-Fail Tests (`tests/compile-fail/`)

**Purpose**: Verify that invalid programs are properly rejected.

These tests ensure the compiler correctly enforces language semantics and catches semantic errors. Programs should fail to compile with appropriate error messages.

**Format**:
- Programs that should not compile
- No `.stderr` files required (just verify compilation fails)
- Test semantic constraint enforcement

**Example**:
```rust
// tests/compile-fail/trait-bound-missing.rs
trait Display {
    fn display(&self) -> i64;
}

fn print_it<T: Display>(x: &T) -> i64 {
    x.display()
}

fn main() -> i64 {
    let x = 42;
    print_it(&x) // Error: i64 doesn't implement Display
}
```

**Current Tests** (10 tests):
- `trait-bound-missing.rs` - Missing trait implementation for generic bound
- `trait-bound-where-clause.rs` - Unsatisfied where clause constraints
- `visibility-private-function.rs` - Access to private functions
- `visibility-private-field.rs` - Access to private struct fields
- `constraint-lifetime-outlive.rs` - Lifetime constraint violations
- `constraint-associated-type.rs` - Missing associated type implementations
- `duplicate-trait-impl.rs` - Duplicate trait implementations
- `incomplete-pattern-match.rs` - Non-exhaustive pattern matching
- `recursive-type-without-indirection.rs` - Recursive types without Box
- `trait-method-signature-mismatch.rs` - Trait impl signature mismatches

### 3. Run-Pass Tests (`tests/run-pass/`)

**Purpose**: Test that valid programs compile and execute correctly.

These tests validate that the compiler correctly handles all implemented language features and that generated code executes as expected.

**Format**:
- Programs that should compile successfully
- Programs should execute and return expected values
- Test language feature correctness

**Example**:
```rust
// tests/run-pass/generic-identity.rs
fn identity<T>(x: T) -> T {
    x
}

fn main() -> i64 {
    identity(42) // Should return 42
}
```

**Current Tests** (15 tests):
- `basic-arithmetic.rs` - Basic arithmetic operations
- `basic-if-else.rs` - If-else expressions
- `basic-function-call.rs` - Function calls with parameters
- `generic-identity.rs` - Generic identity function
- `generic-max.rs` - Generic max function with comparisons
- `match-literal.rs` - Match with literal patterns
- `match-range.rs` - Match with range patterns (1..=10)
- `match-binding.rs` - Match with binding patterns
- `struct-basic.rs` - Struct creation and field access
- `struct-method.rs` - Method calls on structs
- `trait-basic.rs` - Trait implementation and method calls
- `trait-generic-bound.rs` - Generic functions with trait bounds
- `enum-basic.rs` - Enum variants and pattern matching
- `nested-blocks.rs` - Nested block expressions
- `multiple-functions.rs` - Multiple function definitions and calls

### 4. Edge Cases (`tests/edge-cases/`)

**Purpose**: Validate complex scenarios and corner cases.

These tests ensure the compiler handles sophisticated language constructs and edge cases that might expose bugs in complex scenarios.

**Format**:
- Complex, valid programs testing corner cases
- Programs should compile and run correctly
- Test compiler robustness

**Example**:
```rust
// tests/edge-cases/nested-generics-depth-3.rs
fn wrap1<T>(x: T) -> T { x }
fn wrap2<T>(x: T) -> T { wrap1(x) }
fn wrap3<T>(x: T) -> T { wrap2(x) }

fn main() -> i64 {
    wrap3(42) // Deep generic call chain
}
```

**Current Tests** (12 tests):
- `nested-generics-depth-3.rs` - Three levels of generic nesting
- `nested-generics-depth-5.rs` - Five levels of generic nesting
- `pattern-or-complex.rs` - Complex or-patterns with tuples
- `pattern-tuple-nested.rs` - Nested tuple patterns
- `pattern-struct-nested.rs` - Nested struct patterns
- `recursive-type-box.rs` - Recursive types with Box indirection
- `recursive-function-factorial.rs` - Recursive factorial function
- `recursive-function-fibonacci.rs` - Recursive Fibonacci function
- `trait-associated-type.rs` - Traits with associated types
- `trait-supertrait.rs` - Supertrait constraints
- `match-exhaustive-all-arms.rs` - Complex exhaustive pattern matching
- `generic-multiple-params.rs` - Multiple generic type parameters

## Running Tests

### Run All Tests

```bash
# Run the complete test suite
cargo test -p compiletest-integration
```

### Run Specific Test Categories

```bash
# Run only UI tests (error messages)
cargo test -p compiletest-integration run_ui_tests

# Run only compile-fail tests (semantic errors)
cargo test -p compiletest-integration run_compile_fail_tests

# Run only run-pass tests (valid programs)
cargo test -p compiletest-integration run_run_pass_tests

# Run only edge-case tests
cargo test -p compiletest-integration run_edge_case_tests
```

### Run Individual Test Files

```bash
# Run a specific test by name
cargo test -p compiletest-integration -- --test-args tests/ui/type-mismatch-basic.rs
```

## Adding New Tests

### 1. Adding a UI Test

Create both a `.rs` file and a `.stderr` file:

```rust
// tests/ui/my-new-test.rs
fn main() -> i64 {
    let x: i64 = true; //~ ERROR type mismatch
    x
}
```

```
// tests/ui/my-new-test.stderr
error: type mismatch: expected i64, found bool
 --> tests/ui/my-new-test.rs:2:18
  |
2 |     let x: i64 = true;
  |                  ^^^^ expected i64, found bool
```

### 2. Adding a Compile-Fail Test

Create just a `.rs` file:

```rust
// tests/compile-fail/my-new-test.rs
fn main() -> i64 {
    // Code that should fail to compile
    undefined_function()
}
```

### 3. Adding a Run-Pass Test

Create a `.rs` file that should compile and run:

```rust
// tests/run-pass/my-new-test.rs
fn my_function() -> i64 {
    42
}

fn main() -> i64 {
    my_function()
}
```

### 4. Adding an Edge-Case Test

Create a complex but valid `.rs` file:

```rust
// tests/edge-cases/my-new-test.rs
fn deeply_nested<T>(x: T) -> T {
    // Complex edge case code
    x
}

fn main() -> i64 {
    deeply_nested(42)
}
```

## Test File Naming Conventions

- **Descriptive names**: Use clear, descriptive names indicating what is being tested
- **Kebab-case**: Use lowercase with hyphens (e.g., `type-mismatch-basic.rs`)
- **Category prefix**: Consider prefixing with category (e.g., `borrow-conflict.rs`, `trait-bound-missing.rs`)

## Understanding Test Failures

### UI Test Failures

UI tests fail when:
- The compiler doesn't produce an error where expected
- The error message format doesn't match the `.stderr` file
- The error appears at the wrong location

**Fix approach**:
1. Run the test to see actual compiler output
2. Compare with expected `.stderr` file
3. Update either the test or the compiler as appropriate

### Compile-Fail Test Failures

Compile-fail tests fail when:
- The compiler accepts code that should be rejected
- The compiler crashes instead of producing an error

**Fix approach**:
1. Verify the test code is actually invalid
2. Debug why the compiler isn't catching the error
3. Fix the compiler's validation logic

### Run-Pass Test Failures

Run-pass tests fail when:
- The compiler rejects valid code
- The compiled program crashes or produces wrong results
- Compilation succeeds but execution fails

**Fix approach**:
1. Verify the test code is valid
2. Debug compilation or execution issues
3. Fix the compiler or code generation

## Test Coverage

### Current Coverage: 52 Tests

- **UI Tests**: 15 tests covering error messages and diagnostics
- **Compile-Fail Tests**: 10 tests covering semantic error detection
- **Run-Pass Tests**: 15 tests covering valid language features
- **Edge Cases**: 12 tests covering complex scenarios

### Coverage Areas

✅ **Well Covered**:
- Basic type checking
- Function calls and generics
- Pattern matching (literals, ranges, bindings)
- Struct and trait basics
- Name resolution errors
- Borrow checking basics

⚠️ **Partial Coverage**:
- Lifetime analysis (basic tests only)
- Trait system (basic bounds and implementations)
- Module system (minimal coverage)
- Macro expansion (not covered)

🔴 **Not Covered**:
- Procedural macros
- Async/await
- Advanced lifetime features (HRTBs)
- Const generics
- Type inference edge cases
- Closure capture modes

## Integration with CI

The test suite is designed to run in CI environments:

```yaml
# Example CI configuration
- name: Run compiletest suite
  run: cargo test -p compiletest-integration --all-features
```

## Best Practices

1. **Write tests first**: When fixing bugs, add a failing test first
2. **Test one thing**: Each test should focus on a single feature or error
3. **Use clear names**: Test names should indicate what they test
4. **Document edge cases**: Add comments explaining non-obvious test cases
5. **Keep tests minimal**: Use minimal code to demonstrate the feature/error
6. **Update stderr files**: When error messages improve, update `.stderr` files

## Comparison with rustc

This test suite follows the same structure as rustc's compiletest:
- Similar directory organization
- Same test annotation style (`//~ ERROR`)
- Compatible test runner (compiletest_rs)
- Familiar workflows for Rust developers

## Future Enhancements

Planned additions to the test suite:

1. **Incremental compilation tests**: Verify incremental behavior
2. **Performance benchmarks**: Track compilation speed
3. **Memory safety tests**: Extensive borrow checker validation
4. **Cross-platform tests**: Platform-specific behavior
5. **Fuzzing integration**: Automated test generation
6. **Regression tests**: Tests for all fixed bugs

## Contributing

When adding new compiler features:

1. Add run-pass tests for valid usage
2. Add compile-fail tests for invalid usage
3. Add UI tests for error messages
4. Add edge-case tests for complex scenarios
5. Document any new test patterns in this README

## License

Same as the Raven project (MIT OR Apache-2.0)
