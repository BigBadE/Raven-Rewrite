# Raven Compiler Test Status Report

**Total Test Configurations:** 1

## Overall Summary

| Backend | OS | Total | Passed | Failed | Ignored | Pass Rate |
|---------|----|----|--------|--------|---------|-----------|
| ⚠️ all | ubuntu-latest | 148 | 85 | 60 | 3 | 57.4% |

## Test Projects Status

*No project-specific tests found.*

## Backend Details

### ⚠️ All

- **Total Tests:** 148
- **Passed:** 85
- **Failed:** 60
- **Pass Rate:** 57.4%


## Failed Tests

### all on ubuntu-latest

**Test:** `run_compile_fail_tests`
**Project:** unknown

```
test [run-pass] run-pass/match-range.rs ... FAILED
test [run-pass] run-pass/multiple-functions.rs ... FAILED
test [run-pass] edge-cases/trait-supertrait.rs ... FAILED

failures:

failures:
    [run-pass] edge-cases/generic-multiple-params.rs
    [run-pass] edge-cases/match-exhaustive-all-arms.rs
    [run-pass] edge-cases/nested-generics-depth-3.rs
```

**Test:** `run_edge_case_tests`
**Project:** unknown

```
test [run-pass] run-pass/nested-blocks.rs ... FAILED
test [run-pass] run-pass/struct-basic.rs ... FAILED
test [run-pass] run-pass/struct-method.rs ... FAILED
test [run-pass] run-pass/trait-basic.rs ... FAILED
test [run-pass] run-pass/trait-generic-bound.rs ... FAILED

failures:

failures:
    [run-pass] run-pass/basic-arithmetic.rs
```

**Test:** `run_run_pass_tests`
**Project:** unknown

```
running 15 tests
test [ui] ui/borrow-conflict.rs ... FAILED
test [ui] ui/field-not-found.rs ... FAILED
test [ui] ui/generic-type-param-count.rs ... FAILED
test [ui] ui/if-else-type-mismatch.rs ... FAILED
test [ui] ui/lifetime-dangling-ref.rs ... FAILED
test [ui] ui/match-pattern-type-mismatch.rs ... FAILED
test [ui] ui/method-not-found.rs ... FAILED
test [ui] ui/name-resolution-ambiguous.rs ... FAILED
test [ui] ui/struct-field-missing.rs ... FAILED
```

**Test:** `run_ui_tests`
**Project:** unknown

```
failures:

---- run_compile_fail_tests stdout ----

thread '[compile-fail] compile-fail/constraint-associated-type.rs' (17915) panicked at /home/runner/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/compiletest_rs-0.11.2/src/runtest.rs:1479:14:
failed to exec `LD_LIBRARY_PATH=":target/compiletest/constraint-associated-type.stage-id.aux:/home/runner/work/Raven-Rewrite/Raven-Rewrite/target/debug/build/bzip2-sys-808dd54f87f8a633/out/lib:/home/runner/work/Raven-Rewrite/Raven-Rewrite/target/deb...
```

**Test:** `test_all_projects`
**Project:** unknown

```
failures:

---- test_all_projects stdout ----

==== Testing project: 01-basic-arithmetic ====

  -- Interpreter Backend --
Testing basic-arithmetic v0.1.0
Running test: test_subtraction
  ✓ test_subtraction
```


## Legend

- ✅ All tests passing (100%)
- ⚠️ Some tests failing (partial pass)
- ❌ All tests failing or not run
- 🔹 Backend not tested on this OS
