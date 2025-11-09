# Raven Language & Analysis Framework

A next-generation compiler and code analysis framework built on incremental compilation.

## Status: Phase 3 Complete ✅

**Completed:**
- ✅ Phase 0: Foundation infrastructure
- ✅ Phase 1: Salsa query system & Core IR
- ✅ Phase 2: tree-sitter integration & parsing
- ✅ Phase 3: Name resolution & type system

**Current:** Phase 4 - MIR lowering & backends (🚧)

## Features Implemented

### Foundation Layer
- **rv-span** - Source location tracking (FileId, Span, FileSpan)
- **rv-intern** - Thread-safe string interning using lasso
- **rv-arena** - Arena allocator (re-exports la-arena)
- **rv-vfs** - Virtual file system with caching and deduplication
- **rv-syntax** - Generic syntax tree traits for multi-language support
- **rv-database** - Salsa 0.24 incremental query system

### Parsing & IR
- **rv-parser** - tree-sitter-rust integration with rustc-style error diagnostics
  - Full error formatting with source context and line numbers
  - Unclosed delimiter detection with dual labels
  - Color-coded terminal output via codespan-reporting
- **lang-raven** - Raven language adapter (using Rust syntax)
- **rv-hir** - High-level IR with expressions, statements, patterns, types
- **rv-mir** - Mid-level IR with control flow graphs and basic blocks

### Name Resolution & Type System
- **rv-hir-lower** - CST → HIR lowering with name resolution
  - Scope tree with lexical scoping
  - Symbol table for functions, variables, parameters
  - Expression lowering (literals, variables, calls, blocks, if, match)
  - Statement lowering (let bindings, return, expression statements)
  - Pattern lowering (bindings, wildcards)
  - Name resolution across nested scopes
- **rv-ty** - Type inference and checking
  - Type representation (primitives, functions, tuples, references, type variables)
  - Constraint-based type inference
  - Robinson's unification algorithm with occurs check
  - Type context for tracking inferred types
  - Error recovery with error types

### MIR & Code Generation
- **rv-mir** - HIR → MIR lowering with control flow graphs
  - Basic block construction from HIR expressions
  - Control flow graph generation
  - If expression lowering with SwitchInt terminator
  - Local variable allocation and management
  - Expression lowering to MIR statements and RValues
  - Type lowering from type system to MIR types
- **rv-interpreter** - Bytecode interpreter for fast development iteration
  - Runtime value representation (integers, floats, booleans, strings, tuples, structs)
  - Expression evaluation with full operator support
  - Binary operations (arithmetic, comparison, bitwise, logical)
  - Unary operations (negation, logical NOT, bitwise NOT)
  - Control flow execution (basic blocks, branching, returns)
  - SwitchInt branching for conditionals

### Testing
- **integration-tests** - Incremental compilation tests
  - Directory-based fixture system with exact error output matching
  - Rustc-style error verification in fixture files
- Strict verification: no #[allow], clippy -D warnings, file size limits
- Only meaningful tests (trivial tests removed)

## Quick Start

```bash
# Build all crates
cargo build

# Run tests
cargo test

# Verify everything (run before committing)
./scripts/verify.sh
```

## Project Structure

```
crates/
├── foundation/         # Core infrastructure
│   ├── rv-span        ✅ Source locations
│   ├── rv-intern      ✅ String interning
│   ├── rv-arena       ✅ Arena allocator
│   ├── rv-database    ✅ Salsa queries
│   ├── rv-syntax      ✅ Syntax traits
│   └── rv-vfs         ✅ Virtual file system
│
├── parser/
│   └── rv-parser      ✅ tree-sitter integration
│
├── analysis/
│   ├── rv-hir         ✅ High-level IR
│   ├── rv-mir         ✅ Mid-level IR with HIR lowering
│   ├── rv-hir-lower   ✅ CST → HIR lowering
│   ├── rv-ty          ✅ Type inference
│   └── rv-trait-solver 🚧 Trait resolution
│
├── codegen/
│   ├── rv-interpreter  ✅ Interpreter backend
│   ├── rv-cranelift    🚧 Cranelift JIT
│   └── rv-llvm         🚧 LLVM codegen
│
├── language-support/
│   └── lang-raven     ✅ Raven adapter
│
├── analyzer/
│   ├── rv-metrics     🚧 Code metrics
│   ├── rv-lint        🚧 Lint rules
│   ├── rv-duplicates  🚧 Duplicate detection
│   └── rv-query       🚧 Query API
│
├── cli/
│   ├── raven          🚧 Compiler CLI
│   └── raven-analyzer 🚧 Analyzer CLI
│
└── testing/
    └── integration-tests ✅ E2E tests
```

## Architecture

```
Source (.rs files)
    ↓ tree-sitter-rust
Concrete Syntax Tree
    ↓ lang-raven
Generic SyntaxNode
    ↓ HIR lowering (Phase 3)
High-level IR
    ↓ Type checking & name resolution (Phase 3)
Typed HIR
    ↓ MIR lowering (Phase 4)
Control Flow Graphs
    ↓ Backend selection (Phase 4)
┌─────────────┬──────────────┬──────────────┐
│ Interpreter │ Cranelift JIT│ LLVM Codegen │
│ ~50x slower │ ~3x slower   │ Full speed   │
│ 0.05s build │ 1-3s build   │ 30-60s build │
└─────────────┴──────────────┴──────────────┘
```

## Key Technologies

- **Salsa 0.24** - Incremental query system for fast recompilation
- **tree-sitter** - Multi-language parsing with error recovery
- **la-arena** - Efficient indexed arena allocation
- **Cranelift** - Fast JIT compilation for development
- **LLVM** - Production optimizations for release builds
- **Rust 2024** - Implementation language with strict lints

## Development Workflow

```bash
# Add workspace dependency
# Edit root Cargo.toml [workspace.dependencies]

# Use in crate
# crates/*/Cargo.toml:
# dependency-name.workspace = true
```

## Quality Standards

- **Linting:** All clippy lints at deny level
- **No #[allow]:** Zero tolerance for suppressed warnings
- **File size:** Max 500 lines per file
- **Tests:** Only test behavior that can fail
- **Verification:** Run `./scripts/verify.sh` before committing

## Documentation

- **[PLAN.md](./PLAN.md)** - Development roadmap and phase breakdown
- **[CLAUDE.md](./CLAUDE.md)** - Architecture notes and guidelines

## Next Milestones

**Phase 4 (Current):**
- HIR → MIR lowering with control flow
- Interpreter backend for fast iteration
- Cranelift JIT backend
- Generic monomorphization
- Function call handling

**Phase 5:**
- Code metrics and analysis tools
- Lint rule engine
- Duplicate code detection
- Multi-language support verification

See [PLAN.md](./PLAN.md) for complete roadmap.

## License

MIT OR Apache-2.0
