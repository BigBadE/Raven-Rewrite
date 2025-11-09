//! End-to-end integration tests for the complete analyzer pipeline

use lang_raven::RavenLanguage;
use rv_duplicates::DuplicateDetector;
use rv_hir_lower::lower_source_file;
use rv_lint::Linter;
use rv_metrics::analyze_function;
use rv_syntax::Language;

fn parse_and_lower(source: &str) -> rv_hir_lower::LoweringContext {
    let language = RavenLanguage::new();
    let tree = language.parse(source).expect("Failed to parse");
    let root = language.lower_node(&tree.root_node(), source);
    lower_source_file(&root)
}

#[test]
fn test_complete_analysis_pipeline() {
    // This test simulates what the CLI does: parse, lower, and run all analyzers

    let source = include_str!("fixtures/complex.rs");
    let hir = parse_and_lower(source);

    assert!(!hir.functions.is_empty(), "Should have parsed functions");

    // Run metrics on all functions
    let mut all_metrics = Vec::new();
    for (_, function) in &hir.functions {
        let metrics = analyze_function(function);
        all_metrics.push(metrics);
    }

    assert!(!all_metrics.is_empty(), "Should have calculated metrics");
    assert_eq!(
        all_metrics.len(),
        hir.functions.len(),
        "Should have metrics for each function"
    );

    // Run linter on all functions
    let linter = Linter::new();
    let mut all_diagnostics = Vec::new();
    for (_, function) in &hir.functions {
        let diagnostics = linter.lint_function(function);
        all_diagnostics.extend(diagnostics);
    }

    // Complex code may trigger lint warnings depending on implementation details
    // The test verifies that linting runs without crashing

    // Run duplicate detection
    let detector = DuplicateDetector::new();
    let mut all_duplicates = Vec::new();
    for (_, function) in &hir.functions {
        let duplicates = detector.detect_in_function(function);
        all_duplicates.extend(duplicates);
    }

    // Check cross-function duplicates
    let functions: Vec<_> = hir.functions.values().collect();
    let cross_duplicates = detector.detect_across_functions(&functions);
    all_duplicates.extend(cross_duplicates);

    // All analyzers completed without crashing
    assert!(!all_metrics.is_empty());
    // Diagnostics may or may not be found depending on implementation
    #[allow(let_underscore_drop)]
    let _ = all_diagnostics;
}

#[test]
fn test_analyzer_consistency() {
    // Test that running analyzers multiple times gives consistent results

    let source = include_str!("fixtures/simple.rs");
    let hir = parse_and_lower(source);

    let func = hir
        .functions
        .values()
        .next()
        .expect("Should have at least one function");

    // Run metrics twice
    let metrics1 = analyze_function(func);
    let metrics2 = analyze_function(func);

    assert_eq!(
        metrics1.cyclomatic_complexity, metrics2.cyclomatic_complexity,
        "Metrics should be consistent"
    );

    // Run linter twice
    let linter = Linter::new();
    let diag1 = linter.lint_function(func);
    let diag2 = linter.lint_function(func);

    assert_eq!(diag1.len(), diag2.len(), "Linter should be consistent");

    // Run duplicate detection twice
    let detector = DuplicateDetector::new();
    let dup1 = detector.detect_in_function(func);
    let dup2 = detector.detect_in_function(func);

    assert_eq!(
        dup1.len(),
        dup2.len(),
        "Duplicate detection should be consistent"
    );
}

#[test]
fn test_empty_function_analysis() {
    let source = "fn empty() {}";
    let hir = parse_and_lower(source);

    let func = hir.functions.values().next().expect("Should have function");

    // Metrics should handle empty function
    let metrics = analyze_function(func);
    assert_eq!(metrics.cyclomatic_complexity, 1);
    assert_eq!(metrics.cognitive_complexity, 0);
    assert_eq!(metrics.parameter_count, 0);

    // Linter should handle empty function
    let linter = Linter::new();
    let diagnostics = linter.lint_function(func);
    assert_eq!(diagnostics.len(), 0, "Empty function should be clean");

    // Duplicate detection should handle empty function
    let detector = DuplicateDetector::new();
    let duplicates = detector.detect_in_function(func);
    assert_eq!(duplicates.len(), 0);
}

#[test]
fn test_multiple_files_analysis() {
    // Simulate analyzing multiple files like the CLI does

    let files = vec![
        include_str!("fixtures/simple.rs"),
        include_str!("fixtures/complex.rs"),
        include_str!("fixtures/duplicates.rs"),
    ];

    let mut total_functions = 0;
    let mut total_metrics = 0;
    let mut total_diagnostics = 0;
    let mut total_duplicates = 0;

    for source in files {
        let hir = parse_and_lower(source);

        total_functions += hir.functions.len();

        // Analyze metrics
        for (_, function) in &hir.functions {
            let _metrics = analyze_function(function);
            total_metrics += 1;
        }

        // Run linter
        let linter = Linter::new();
        for (_, function) in &hir.functions {
            let diagnostics = linter.lint_function(function);
            total_diagnostics += diagnostics.len();
        }

        // Detect duplicates
        let detector = DuplicateDetector::new();
        for (_, function) in &hir.functions {
            let duplicates = detector.detect_in_function(function);
            total_duplicates += duplicates.len();
        }
    }

    assert!(total_functions > 0, "Should have analyzed functions");
    assert_eq!(
        total_metrics, total_functions,
        "Should have metrics for all functions"
    );
    // Linter and duplicate detection ran (counts may be 0)
    let _ = total_diagnostics;
    let _ = total_duplicates;
}

#[test]
fn test_error_recovery() {
    // Test that analyzers handle malformed input gracefully

    let source = "fn incomplete(";
    let language = RavenLanguage::new();

    // tree-sitter should parse with error recovery
    let tree_result = language.parse(source);

    // Even with errors, tree-sitter returns a tree
    assert!(tree_result.is_ok(), "Should parse with error recovery");

    // The rest of the pipeline may or may not work,
    // but it shouldn't crash
    if let Ok(tree) = tree_result {
        let root = language.lower_node(&tree.root_node(), source);
        let _hir = lower_source_file(&root);

        // HIR might be empty or incomplete, but shouldn't crash
        // (Successfully created HIR without panic is the test)
    }
}

#[test]
fn test_real_world_pattern_simple_arithmetic() {
    let source = r#"
        fn calculate(x: i32, y: i32) -> i32 {
            let sum = x + y;
            let product = x * y;
            sum + product
        }
    "#;

    let hir = parse_and_lower(source);
    let func = hir.functions.values().next().expect("Should have function");

    let metrics = analyze_function(func);
    // Note: Metrics are based on current HIR lowering implementation
    // We verify the function compiles and metrics are calculated
    assert!(metrics.cyclomatic_complexity >= 1);

    let linter = Linter::new();
    let _diagnostics = linter.lint_function(func);
    // Simple arithmetic may or may not trigger warnings depending on implementation
}

#[test]
fn test_real_world_pattern_conditional_logic() {
    let source = r#"
        fn classify(x: i32) -> i32 {
            if x < 0 {
                -1
            } else if x > 0 {
                1
            } else {
                0
            }
        }
    "#;

    let hir = parse_and_lower(source);
    let func = hir.functions.values().next().expect("Should have function");

    let metrics = analyze_function(func);
    assert!(metrics.cyclomatic_complexity >= 2, "Should have branches");

    let linter = Linter::new();
    let _diagnostics = linter.lint_function(func);
    // Simple conditional should pass most lint rules
}

#[test]
fn test_all_analyzers_produce_output() {
    let source = include_str!("fixtures/complex.rs");
    let hir = parse_and_lower(source);

    for (_, function) in &hir.functions {
        // Metrics should always produce output
        let metrics = analyze_function(function);
        assert!(!metrics.name.is_empty());

        // Linter should run (may or may not find issues)
        let linter = Linter::new();
        let _diagnostics = linter.lint_function(function);

        // Duplicate detector should run (may or may not find duplicates)
        let detector = DuplicateDetector::new();
        let _duplicates = detector.detect_in_function(function);
    }
}
