# Raven Language & Analysis Framework

A next-generation compiler and code analysis framework built on incremental compilation.

## Project Status: Phase 0 - Foundation ✅

Core workspace structure established with 4 foundation crates implemented.

## Goals

1. **Raven Compiler** - Fast, incremental systems programming language
   - Rust-compatible syntax (using tree-sitter-rust)
   - Sub-second dev iteration times
   - Multiple backends (Interpreter → Cranelift → LLVM)
   - Salsa-powered incremental compilation

2. **Analysis Framework** - Multi-language code analysis
   - Support Rust, Python, JavaScript, Go, and more
   - Code metrics, linting, duplicate detection
   - Incremental re-analysis
   - Language-agnostic query API

## Quick Start

```bash
# Check that everything builds
cargo check

# Build all crates
cargo build

# Run tests (when implemented)
cargo test

# Build specific crate
cargo build -p rv-span
```

## Project Structure

```
crates/
├── foundation/      # Core infrastructure
│   ├── rv-span/      ✅ Source spans and file locations
│   ├── rv-intern/    ✅ String interning with lasso
│   ├── rv-arena/     ✅ Indexed arena allocator
│   ├── rv-database/  ✅ Salsa database (placeholder)
│   ├── rv-syntax/    🚧 Syntax tree traits
│   └── rv-vfs/       🚧 Virtual file system
│
├── parser/          🚧 tree-sitter-rust integration
├── analysis/        🚧 HIR, MIR, type system
├── codegen/         🚧 Interpreter, Cranelift, LLVM backends
├── language-support/🚧 Multi-language adapters
├── analyzer/        🚧 Metrics, lints, duplicates
├── cli/             🚧 Command-line interfaces
└── testing/         🚧 Test utilities and fixtures
```

## Documentation

- **[PLAN.md](./PLAN.md)** - Complete 48-week development roadmap
- **[CLAUDE.md](./CLAUDE.md)** - Development guidelines and architecture notes

## Key Technologies

- **Salsa** - Incremental query system for fast recompilation
- **tree-sitter** - Multi-language parsing with error recovery
- **Cranelift** - Fast JIT compilation for development builds
- **LLVM** - Production-grade optimization for release builds
- **Rust 2021** - Implementation language

## Development Workflow

All dependencies are managed at workspace level in the root `Cargo.toml`:

```bash
# Add a new workspace dependency
# Edit Cargo.toml [workspace.dependencies]

# Use in a crate
# crates/*/Cargo.toml:
# some-crate = { workspace = true }
```

## Next Steps

See **Phase 1** in [PLAN.md](./PLAN.md):
- Implement Salsa query system
- Define HIR and MIR data structures
- Create test infrastructure

## License

MIT OR Apache-2.0

---

**Note:** This is a from-scratch rewrite. The previous implementation has been archived in git stash.
