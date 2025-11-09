# Backend Integration Testing

Comprehensive testing for all three Raven backends.

## Backends

### 1. Interpreter (`rv-interpreter`)
- **Type**: Direct AST/HIR interpretation
- **Use Case**: Development, debugging, testing
- **Pros**: Fast compilation, easy debugging
- **Cons**: Slower execution

### 2. Cranelift JIT (`rv-cranelift`)
- **Type**: Just-in-time compilation
- **Use Case**: Interactive development, scripting
- **Pros**: Fast compilation, good runtime performance
- **Cons**: Not as optimized as LLVM

### 3. LLVM (`rv-llvm-backend`)
- **Type**: Ahead-of-time compilation with LLVM
- **Use Case**: Production builds, maximum performance
- **Pros**: Best optimization, production-ready
- **Cons**: Slower compilation, requires LLVM installation

## Testing Strategy

### Phase 1: HIR Testing ✅ COMPLETE
- Parse source code to HIR
- Verify all language features parse correctly
- Test error recovery
- **Status**: 20 tests passing

### Phase 2: MIR Generation 🚧 IN PROGRESS
- Lower HIR to MIR (control flow graphs)
- Validate SSA form
- Test optimization passes
- **Status**: Infrastructure in place, lowering in development

### Phase 3: Backend Execution 📋 PLANNED
- Execute MIR on all three backends
- Compare results for correctness
- Test edge cases and error handling

### Phase 4: Optimization Verification 📋 PLANNED
- Test LLVM optimization levels (None, Less, Default, Aggressive)
- Verify optimizations preserve semantics
- Benchmark performance improvements

## Current Test Coverage

### HIR Tests (20 tests)
```
✅ test_parse_simple_function
✅ test_parse_multiple_functions
✅ test_control_flow_hir
✅ test_complex_expression_hir
✅ test_function_calls_hir
✅ test_nested_blocks_hir
✅ test_loop_hir
✅ test_match_expression_hir
✅ test_struct_and_impl_hir
✅ test_generic_function_hir
✅ test_recursive_function_hir
✅ test_all_operators_hir
✅ test_comparisons_hir
✅ test_logical_operators_hir
```

### Backend Availability Tests (6 tests)
```
✅ test_interpreter_backend_available
✅ test_cranelift_backend_available
✅ test_llvm_backend_available (with --features llvm)
✅ test_llvm_backend_graceful_fallback
✅ test_all_backends_in_workspace
✅ test_hir_to_mir_lower_stub
```

## LLVM Backend Integration

The LLVM backend has been fully integrated:

```rust
// Example: Compile to LLVM IR
use rv_llvm_backend::{compile_to_llvm_ir, OptLevel};

let llvm_ir = compile_to_llvm_ir(&mir_functions, OptLevel::Default)?;
println!("{}", llvm_ir);
```

### LLVM Features
- ✅ Type lowering (all Raven types → LLVM types)
- ✅ Function compilation
- ✅ Expression codegen (16 binary ops, 2 unary ops)
- ✅ Control flow (branches, switches, calls)
- ✅ Optimization passes (7 passes across 4 levels)
- ✅ Object file generation
- ✅ Feature flag for optional LLVM

### Running LLVM Tests

**Without LLVM:**
```bash
cargo test -p integration-tests
# LLVM tests gracefully skipped
```

**With LLVM:**
```bash
# Install LLVM 18.0 first
cargo test -p integration-tests --features llvm
# All LLVM tests run
```

## Future Backend Comparison Tests

Once MIR integration is complete:

```rust
#[test]
fn test_all_backends_factorial() {
    let source = r#"
        fn factorial(n: i32) -> i32 {
            if n <= 1 { return 1; }
            n * factorial(n - 1)
        }
    "#;
    
    let interpreter_result = execute_interpreter(source, 5);
    let cranelift_result = execute_cranelift(source, 5);
    let llvm_result = execute_llvm(source, 5);
    
    assert_eq!(interpreter_result, 120);
    assert_eq!(cranelift_result, 120);
    assert_eq!(llvm_result, 120);
}
```

## Performance Benchmarking

When execution is integrated:

```rust
#[bench]
fn bench_backends_fibonacci() {
    let source = "fn fib(n: i32) -> i32 { ... }";
    
    // Measure compilation time
    bench_compile_interpreter(source);
    bench_compile_cranelift(source);
    bench_compile_llvm_opt_none(source);
    bench_compile_llvm_opt_aggressive(source);
    
    // Measure execution time
    bench_execute_interpreter(source, 30);
    bench_execute_cranelift(source, 30);
    bench_execute_llvm(source, 30);
}
```

Expected results:
- **Compilation**: Interpreter < Cranelift < LLVM
- **Execution**: LLVM < Cranelift < Interpreter
- **Total (compile + execute short)**: Interpreter fastest
- **Total (compile + execute long)**: LLVM fastest

## Contributing

When adding backend features:

1. Add unit tests in the backend crate
2. Add integration tests in this crate
3. Test with all three backends when possible
4. Document any backend-specific behavior
5. Update this file

## CI/CD

Backend tests run on all platforms:

```yaml
- Linux (Ubuntu 22.04)
- macOS (latest)
- Windows (latest)
```

Both configurations:
- Without LLVM (default)
- With LLVM (when available)
