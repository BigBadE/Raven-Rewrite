# Magpie - Package Manager for Raven

Magpie is a flexible package manager for the Raven programming language with support for multiple backends.

## Features

- **Cargo.toml Compatibility**: Uses Cargo.toml format for project manifests
- **Pluggable Backends**: Extensible architecture supports multiple execution backends
- **Interpreter Backend**: Built-in interpreter backend using the Raven compiler pipeline
- **Standard Commands**: Familiar commands like `build`, `run`, `test`, `check`

## Usage

### Create a New Project

```bash
magpie new my-project         # Create a binary project
magpie new my-lib --lib       # Create a library project
```

### Build a Project

```bash
magpie build                  # Build in current directory
magpie build -C /path/to/project
```

### Run a Project

```bash
magpie run                    # Run main function
magpie run -- arg1 arg2       # Pass arguments (future)
```

### Test a Project

```bash
magpie test                   # Run all test functions
```

Test functions are automatically discovered - any function starting with `test_` will be executed. Tests should return `bool` where `true` indicates success.

### Check a Project

```bash
magpie check                  # Validate syntax and types without building
```

### Clean Build Artifacts

```bash
magpie clean                  # Remove build artifacts (no-op for interpreter backend)
```

## Project Structure

Generated projects follow this structure:

```
my-project/
├── Cargo.toml
└── src/
    └── main.rs     # or lib.rs for libraries
```

## Backend Architecture

Magpie uses a trait-based backend system that allows different execution strategies:

- **RavenBackend**: Interprets code using the full Raven compiler pipeline (parse → HIR → type check → MIR → interpret)
- Future backends could include:
  - Cranelift JIT compilation
  - LLVM code generation
  - External toolchain integration (e.g., actual Cargo)

## Example

```rust
// src/main.rs
fn main() -> i64 {
    42
}

#[test]
fn test_arithmetic() -> bool {
    if 2 + 2 == 4 {
        true
    } else {
        false
    }
}
```

Run with:
```bash
magpie run    # Outputs: 42
magpie test   # Runs test_arithmetic
```

## Integration with Raven Compiler

Magpie uses the full Raven compiler pipeline:

1. **Parsing**: Source code → Syntax tree (via tree-sitter)
2. **HIR Lowering**: Syntax tree → High-level IR
3. **Type Inference**: Hindley-Milner type checking
4. **MIR Lowering**: HIR → Mid-level IR (control flow graphs)
5. **Execution**: MIR → Interpreter results
