# CLAUDE.md

## Project Overview

Raven is being rebuilt from scratch as a **dual-purpose system**:
1. **Raven Compiler** - Fast incremental compiler with Rust-compatible syntax
2. **Analysis Framework** - Multi-language code analysis tool

See [PLAN.md](./PLAN.md) for complete development roadmap.

## Current Phase: Phase 0 - Foundation

We are setting up the workspace structure and core infrastructure crates.

## Code Rules

- All dependencies must use `.workspace = true` format
- Use `rv-` prefix for all internal crates (not `ra-`)
- Follow the crate structure defined in PLAN.md
- Do not create tests or documentation unless explicitly asked
- All workspace configuration goes in root `Cargo.toml`

## Architecture (Target State)

**Compilation Pipeline:**
```
Rust source (.rs files)
    ↓ (tree-sitter-rust parser)
HIR (High-level IR)
    ↓ (name resolution, type inference)
MIR (Mid-level IR - control flow graphs)
    ↓ (backend selection)
┌────────────┬──────────────┬──────────────┐
│ Interpreter│ Cranelift JIT│ LLVM Codegen │
└────────────┴──────────────┴──────────────┘
```

**Key Technologies:**
- **Salsa**: Incremental query system (Phase 1)
- **tree-sitter**: Multi-language parsing
- **Cranelift**: Fast JIT compilation
- **LLVM**: Production optimizations

## Workspace Structure

```
crates/
├── foundation/
│   ├── rv-span/      ✅ Source spans and locations
│   ├── rv-intern/    ✅ String interning
│   ├── rv-arena/     ✅ Arena allocator
│   ├── rv-database/  ✅ Salsa database (placeholder)
│   ├── rv-syntax/    🚧 Syntax tree traits
│   └── rv-vfs/       🚧 Virtual file system
│
├── parser/           🚧 tree-sitter integration
├── analysis/         🚧 HIR, MIR, type system
├── codegen/          🚧 Backends
├── language-support/ 🚧 Multi-language adapters
├── analyzer/         🚧 Analysis tools
├── cli/              🚧 CLIs
└── testing/          🚧 Test utilities
```

## Development Commands

```bash
# Check all crates compile
cargo check

# Run tests (when implemented)
cargo test

# Build specific crate
cargo build -p rv-span

# Format code
cargo fmt

# Lint
cargo clippy
```

## Implementation Notes

- **Syntax**: Currently using Rust syntax via `tree-sitter-rust`
- **File Extension**: `.rs` files (may add `.rv` later)
- **Salsa Integration**: Deferred to Phase 1
- **Old Codebase**: Archived in git stash