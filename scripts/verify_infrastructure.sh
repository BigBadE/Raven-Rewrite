#!/bin/bash
# Verification script for test status tracking infrastructure

set -e

echo "=== Verifying Test Status Tracking Infrastructure ==="
echo ""

# Check all required files exist
echo "1. Checking required files..."
FILES=(
    "scripts/parse_test_results.py"
    "scripts/generate_status_report.py"
    "scripts/update_docs.py"
    ".github/workflows/test-status.yml"
    "TEST_STATUS.md"
)

for file in "${FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "  ✓ $file exists"
    else
        echo "  ✗ $file MISSING"
        exit 1
    fi
done

echo ""
echo "2. Checking script permissions..."
for script in scripts/*.py; do
    if [ -x "$script" ]; then
        echo "  ✓ $script is executable"
    else
        echo "  ✗ $script is not executable"
        exit 1
    fi
done

echo ""
echo "3. Validating Python syntax..."
for script in scripts/*.py; do
    if python -m py_compile "$script" 2>/dev/null; then
        echo "  ✓ $script syntax valid"
    else
        echo "  ✗ $script has syntax errors"
        exit 1
    fi
done

echo ""
echo "4. Validating GitHub Actions YAML..."
if python -c "import yaml; yaml.safe_load(open('.github/workflows/test-status.yml'))" 2>/dev/null; then
    echo "  ✓ test-status.yml is valid YAML"
else
    echo "  ✗ test-status.yml has syntax errors"
    exit 1
fi

echo ""
echo "5. Testing parse_test_results.py help..."
if python scripts/parse_test_results.py --help > /dev/null 2>&1; then
    echo "  ✓ parse_test_results.py --help works"
else
    echo "  ✗ parse_test_results.py --help failed"
    exit 1
fi

echo ""
echo "6. Testing generate_status_report.py help..."
if python scripts/generate_status_report.py --help > /dev/null 2>&1; then
    echo "  ✓ generate_status_report.py --help works"
else
    echo "  ✗ generate_status_report.py --help failed"
    exit 1
fi

echo ""
echo "7. Testing update_docs.py help..."
if python scripts/update_docs.py --help > /dev/null 2>&1; then
    echo "  ✓ update_docs.py --help works"
else
    echo "  ✗ update_docs.py --help failed"
    exit 1
fi

echo ""
echo "8. Checking documentation..."
if [ -f "scripts/README.md" ]; then
    line_count=$(wc -l < scripts/README.md)
    if [ "$line_count" -gt 50 ]; then
        echo "  ✓ scripts/README.md exists and is comprehensive ($line_count lines)"
    else
        echo "  ✗ scripts/README.md is too short"
        exit 1
    fi
else
    echo "  ✗ scripts/README.md missing"
    exit 1
fi

echo ""
echo "9. Checking TEST_STATUS.md content..."
if grep -q "Raven Compiler Test Status Report" TEST_STATUS.md; then
    echo "  ✓ TEST_STATUS.md has proper title"
else
    echo "  ✗ TEST_STATUS.md missing title"
    exit 1
fi

if grep -q "Overall Summary" TEST_STATUS.md; then
    echo "  ✓ TEST_STATUS.md has summary section"
else
    echo "  ✗ TEST_STATUS.md missing summary"
    exit 1
fi

echo ""
echo "=== All Checks Passed ✓ ==="
echo ""
echo "Infrastructure is ready for use!"
echo ""
echo "Quick Start:"
echo "  1. Run tests: cargo test --workspace --no-fail-fast > test_output.txt 2>&1"
echo "  2. Parse: python scripts/parse_test_results.py test_output.txt --os \$(uname -s) --backend all -o results.json"
echo "  3. Report: python scripts/generate_status_report.py results.json -o TEST_STATUS.md"
echo "  4. Update: python scripts/update_docs.py TEST_STATUS.md CLAUDE.md --dry-run"
