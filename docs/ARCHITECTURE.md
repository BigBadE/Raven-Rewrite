# Raven Architecture

## Overview

Raven is a dual-purpose system combining a fast incremental compiler with a multi-language code analysis framework. This document describes the architectural design and key components.

## System Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     Source Code (.rs)                        │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│              tree-sitter Parser (CST)                        │
│  • Language-agnostic parsing                                 │
│  • Incremental reparsing                                     │
│  • Error recovery                                            │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│              High-level IR (HIR)                             │
│  • Name resolution                                           │
│  • Scope tree                                                │
│  • Symbol table                                              │
│  • Type inference                                            │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│              Mid-level IR (MIR)                              │
│  • Control flow graphs                                       │
│  • Basic blocks                                              │
│  • Place-based memory model                                  │
│  • Terminators (Goto, SwitchInt, Return)                     │
└────────────────────┬────────────────────────────────────────┘
                     │
        ┌────────────┼────────────┐
        ▼            ▼            ▼
   ┌─────────┐  ┌─────────┐  ┌─────────┐
   │Interpret│  │Cranelift│  │  LLVM   │
   │  -er    │  │   JIT   │  │ Codegen │
   └─────────┘  └─────────┘  └─────────┘
```

## Core Components

### 1. Foundation Layer (`crates/foundation/`)

#### rv-span
- Source location tracking with `FileId`, `Span`, `FileSpan`
- Used throughout the compiler for error reporting
- Zero-cost abstractions (newtype wrappers)

#### rv-intern
- String interning using `lasso` crate
- Thread-safe symbol management
- Reduces memory usage and enables fast string comparisons

#### rv-arena
- Re-exports `la-arena` for AST node allocation
- Arena-based memory management
- Provides `Idx<T>` for type-safe indices

#### rv-database
- Salsa 0.24 integration for incremental compilation
- Query-based architecture
- Automatic dependency tracking and invalidation

#### rv-vfs
- Virtual file system with file tracking
- Caching for fast file access
- Supports both real and in-memory files

#### rv-syntax
- Language-agnostic syntax tree traits
- Generic `SyntaxNode` representation
- Bridge between parser and HIR

### 2. Parser Layer (`crates/parser/`)

#### rv-parser
- tree-sitter integration
- Stateless parser design (thread-safe)
- Error recovery with detailed diagnostics

#### lang-raven
- Raven language adapter using Rust grammar
- CST to SyntaxNode conversion
- Rustc-style error formatting

### 3. Analysis Layer (`crates/analysis/`)

#### rv-hir
- High-level intermediate representation
- Expression, statement, pattern, type nodes
- Arena-based storage with `ExprId`, `StmtId` indices
- `DefId` system for definitions

#### rv-hir-lower
- CST → HIR lowering
- Name resolution across scopes
- Scope tree construction
- Symbol table management

#### rv-ty
- Type representation with type arena
- Constraint-based type inference
- Unification algorithm with occurs check
- Type context for tracking inferred types
- Supports primitives, functions, tuples, references, type variables

#### rv-mir
- Mid-level IR with control flow graphs
- Basic block construction
- Place-based memory model
- Statement types: Assign, StorageLive, StorageDead, Nop
- Terminators: Return, Goto, SwitchInt, Unreachable
- RValue operations: BinaryOp, UnaryOp, Use

### 4. Backend Layer (`crates/backend/`)

#### rv-interpreter
- Bytecode interpreter for fast development iteration
- Runtime value representation
- Control flow execution
- No compilation overhead

#### rv-cranelift
- JIT compilation via Cranelift
- Fast compilation times
- Native code execution
- MIR → Cranelift IR translation

#### rv-mono
- Monomorphization infrastructure
- Generic function instance management
- Call graph discovery

### 5. Analyzer Layer (`crates/analyzer/`)

#### rv-metrics
- Code complexity analysis
- Cyclomatic complexity (McCabe)
- Cognitive complexity (SonarSource)
- Nesting depth measurement

#### rv-lint
- Extensible lint rule engine
- Built-in rules:
  - ComplexityRule
  - TooManyParametersRule
  - DeepNestingRule
  - CognitiveComplexityRule
  - UnusedVariableRule
- Diagnostic system with spans and suggestions

#### rv-duplicates
- AST-based duplicate code detection
- Hash-based structural comparison
- Similarity scoring
- Cross-function duplicate detection

### 6. CLI Layer (`crates/cli/`)

#### raven
- Main compiler CLI
- Commands: build, run, check, new
- Backend selection (interpreter or JIT)
- Project scaffolding

#### raven-analyzer
- Static analysis CLI
- Commands: lint, metrics, duplicates
- JSON and text output formats
- Configurable thresholds

## Data Flow

### Compilation Pipeline

1. **Source Input**
   - Files read from VFS
   - Content stored in Salsa database

2. **Parsing**
   - tree-sitter produces CST
   - Language adapter converts to generic SyntaxNode
   - Parse errors collected

3. **HIR Lowering**
   - Scope tree construction
   - Symbol table population
   - Expression/statement lowering
   - Name resolution

4. **Type Checking**
   - Constraint generation
   - Type inference via unification
   - Type error detection

5. **MIR Lowering**
   - Control flow graph construction
   - Basic block generation
   - Terminator placement

6. **Backend Execution**
   - **Interpreter**: Direct MIR evaluation
   - **JIT**: Cranelift compilation → native code
   - **LLVM**: (Future) Optimized machine code

### Analysis Pipeline

1. **Source Input**
   - Files loaded via VFS

2. **Parsing & HIR**
   - Same as compilation pipeline

3. **Analysis**
   - **Metrics**: Complexity calculation on HIR/MIR
   - **Linting**: Rule application on HIR
   - **Duplicates**: Hash-based comparison of HIR nodes

4. **Reporting**
   - Diagnostics with source spans
   - JSON or formatted text output

## Key Design Decisions

### Salsa for Incremental Compilation
- Query-based architecture
- Automatic dependency tracking
- Efficient recompilation on changes

### Arena-based Memory Management
- Fast allocation
- Type-safe indices instead of pointers
- Eliminates lifetime complexity in IR

### tree-sitter for Parsing
- Language-agnostic
- Incremental reparsing
- Excellent error recovery
- Supports multiple languages

### Dual Backend Strategy
- **Interpreter**: Fast iteration during development
- **JIT**: Production-speed native code
- **LLVM**: (Future) Maximum optimization

### Place-based MIR
- Inspired by Rust's MIR
- Explicit memory operations
- Easier optimization
- Clear semantics

## Performance Characteristics

| Operation | Target | Status |
|-----------|--------|--------|
| Parse 10k LOC | <0.1s | ✅ Achieved |
| Type-check 10k LOC | <0.5s | ✅ Achieved |
| Incremental rebuild (body change) | <0.1s | ✅ Achieved |
| Cranelift compile 1k LOC | <1s | ✅ Achieved |
| Analysis 10k LOC | <0.5s | ✅ Achieved |

## Error Handling

### Parse Errors
- Rustc-style formatting with codespan-reporting
- Source context with line numbers
- Color-coded terminal output
- Dual labels for unclosed delimiters

### Type Errors
- Span-based error reporting
- Type mismatch details
- Inference failure messages

### Lint Diagnostics
- Severity levels (Info, Warning, Error)
- Actionable suggestions
- Rule-specific messages

## Testing Strategy

### Unit Tests
- Each crate has focused unit tests
- Test core functionality in isolation
- Fast feedback loop

### Integration Tests
- End-to-end compilation tests
- Backend comparison tests
- Analysis tool tests

### Test Requirements
- No trivial tests allowed
- Must verify behavior that can fail
- Clear assertions

## Future Extensions

### Phase 8: LLVM Backend
- Full LLVM IR generation
- Optimization passes
- Production releases

### Phase 9: Language Server Protocol
- LSP implementation
- IDE integration
- Real-time diagnostics

### Phase 10: Advanced Features
- Debugger integration
- Package registry
- Performance profiler
- Additional language adapters
