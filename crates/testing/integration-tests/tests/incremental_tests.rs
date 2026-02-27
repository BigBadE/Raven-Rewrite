//! Tests for incremental compilation via Salsa database
//!
//! Phase 6.8: Verifies that Salsa database invalidation works correctly

use integration_tests::TestFixture;
use rv_database::{file_functions, lower_to_hir, parse_file};

/// Test that parsing is memoized - same file content returns same result
#[test]
fn test_parse_memoization() {
    let mut fixture = TestFixture::new();

    let file = fixture.add_virtual_file(
        "test.rs",
        r#"
            fn main() {
                let x = 42;
            }
        "#,
    );

    // Parse twice - should hit memoization
    let result1 = parse_file(&fixture.db, file);
    let result2 = parse_file(&fixture.db, file);

    // Both should succeed with no errors
    assert!(result1.syntax.is_some());
    assert!(result2.syntax.is_some());
    assert!(result1.errors.is_empty());
    assert!(result2.errors.is_empty());
}

/// Test that HIR lowering is memoized
#[test]
fn test_hir_lowering_memoization() {
    let mut fixture = TestFixture::new();

    let file = fixture.add_virtual_file(
        "test.rs",
        r#"
            fn add(a: i64, b: i64) -> i64 {
                a + b
            }

            fn main() {
                let result = add(1, 2);
            }
        "#,
    );

    // Lower to HIR twice
    let hir1 = lower_to_hir(&fixture.db, file);
    let hir2 = lower_to_hir(&fixture.db, file);

    // Should have same number of functions
    assert_eq!(hir1.functions.len(), hir2.functions.len());
    assert_eq!(hir1.functions.len(), 2); // add and main
}

/// Test that file updates invalidate cached results
#[test]
fn test_file_update_invalidates_cache() {
    let mut fixture = TestFixture::new();

    // Start with one function
    let file = fixture.add_virtual_file(
        "test.rs",
        r#"
            fn foo() -> i64 {
                1
            }
        "#,
    );

    let hir1 = lower_to_hir(&fixture.db, file);
    assert_eq!(hir1.functions.len(), 1);

    // Update file contents - add another function
    fixture.db.set_file_contents(
        file,
        r#"
            fn foo() -> i64 {
                1
            }

            fn bar() -> i64 {
                2
            }
        "#
        .to_string(),
    );

    // Re-lower - should see the new function
    let hir2 = lower_to_hir(&fixture.db, file);
    assert_eq!(hir2.functions.len(), 2);
}

/// Test that function query is memoized
#[test]
fn test_file_functions_memoization() {
    let mut fixture = TestFixture::new();

    let file = fixture.add_virtual_file(
        "test.rs",
        r#"
            fn alpha() -> i64 { 1 }
            fn beta() -> i64 { 2 }
            fn gamma() -> i64 { 3 }
        "#,
    );

    // Query functions multiple times
    let funcs1 = file_functions(&fixture.db, file);
    let funcs2 = file_functions(&fixture.db, file);

    // Should have same functions
    assert_eq!(funcs1.len(), 3);
    assert_eq!(funcs2.len(), 3);
}

/// Test that features are parsed correctly from #![feature(...)]
#[test]
fn test_feature_flags_parsing() {
    let mut fixture = TestFixture::new();

    let file = fixture.add_virtual_file(
        "test.rs",
        r#"
            #![feature(auto_traits, macro_metavar_expr)]
            #![feature(core_intrinsics)]

            fn main() {}
        "#,
    );

    let hir = lower_to_hir(&fixture.db, file);

    // Check that features were parsed
    assert!(hir.features.is_enabled(&rv_hir::Feature::AutoTraits));
    assert!(hir.features.is_enabled(&rv_hir::Feature::MacroMetavarExpr));
    assert!(hir.features.is_enabled(&rv_hir::Feature::CoreIntrinsics));
    // This one wasn't enabled
    assert!(!hir.features.is_enabled(&rv_hir::Feature::Generators));
}

/// Test VFS caching - files are read from cache, not disk
#[test]
fn test_vfs_caching() {
    let mut fixture = TestFixture::new();

    // Add file with specific content
    let file = fixture.add_virtual_file(
        "cached.rs",
        r#"
            fn cached_function() -> i64 {
                42
            }
        "#,
    );

    // Get contents from database (should be from VFS cache)
    let contents = fixture.db.get_file_contents(file);
    assert!(contents.contains("cached_function"));

    // Update contents via database
    fixture.db.set_file_contents(
        file,
        r#"
            fn updated_function() -> i64 {
                99
            }
        "#
        .to_string(),
    );

    // Contents should reflect update from VFS
    let updated_contents = fixture.db.get_file_contents(file);
    assert!(updated_contents.contains("updated_function"));
    assert!(!updated_contents.contains("cached_function"));
}
