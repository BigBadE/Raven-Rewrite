# CLAUDE.md

## Code Rules

- Use import paths instead of full paths when possible
- Do not re-export types
- Test code with `cargo test`, not `cargo run` unless explicitly needed
- Do not create tests or documentation unless asked
- Do not modify the main function or tests unless explicitly told
- Don't put imports anywhere other than the top of the file

## Architecture Overview

Raven is a multi-stage compiler written in Rust that transforms source code through several intermediate representations:

**Parser → HIR → MIR → LLVM IR → Machine Code**

### Compilation Pipeline
1. **Parser** (`language/parser/`): Parses `.rv` source files into Raw Syntax Tree
2. **HIR** (`language/hir/`): High-level IR - direct memory representation of source code with no transformations
3. **MIR** (`language/mir/`): Mid-level IR - control-flow graph representation for data flow analysis
4. **LLVM Compiler** (`language/compilers/llvm/`): Compiles MIR to LLVM IR for execution

### Core Architecture Concepts

#### Syntax Levels
The codebase uses a trait-based system where each compilation stage implements `SyntaxLevel`:
- **Raw** → **High** → **Medium** syntax levels
- Each level defines its own types for expressions, statements, functions, and type references
- Translation between levels happens via the `Translate` trait

#### Generic System
Raven implements a sophisticated generic type and function system:
- **Type Monomorphization**: `BasicGenericStruct<T>` becomes `BasicGenericStruct_i32`
- **Function Monomorphization**: `generic_func<T>` becomes `generic_func_i32`
- **Type Inference**: Automatic inference of concrete types from function arguments
- **On-demand Generation**: Monomorphized versions created only when needed

#### Key Traits and Systems
- `SyntaxLevel`: Defines the structure of each compilation stage
- `Translate`: Handles transformation between syntax levels
- `PrettyPrint`: Formatting and display of syntax structures
- `Context`: Manages translation state and symbol tables

### Directory Structure
```
language/
├── syntax/           # Core traits and type definitions
├── parser/           # Source code parsing (.rv files)
├── hir/             # High-level intermediate representation
├── mir/             # Mid-level IR with control flow graphs
├── compilers/llvm/  # LLVM backend compilation
├── runner/          # Orchestrates the compilation pipeline
└── type_system/     # Type checking and inference
tests/
├── core/            # Test source files (.rv)
└── src/main.rs      # Test harness
```

### Working with Generics
When working on generic-related code:
- **Type translation** happens in `mir/src/types.rs` with monomorphization logic
- **Function translation** in `mir/src/function.rs` and `mir/src/monomorphization.rs`
- **Type inference** for function calls in `mir/src/expression.rs`
- Generic types use `GenericTypeRef` and functions use `GenericFunctionRef`

### Test Files
Test cases are written in Raven's `.rv` syntax in `tests/core/`. The main test runner in `tests/src/main.rs` compiles these files through the full pipeline and executes them via LLVM.

## Symbol Management
The codebase uses `lasso::ThreadedRodeo` for string interning. All identifiers (function names, type names, variable names) are stored as `Spur` tokens for efficient memory usage and comparison.