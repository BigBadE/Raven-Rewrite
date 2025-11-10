# Raven Test Infrastructure Scripts

This directory contains Python scripts for automated test result tracking and documentation updates.

## Scripts

### 1. `parse_test_results.py`

Parses `cargo test` output into structured JSON.

**Usage:**
```bash
python scripts/parse_test_results.py test_output.txt --os windows-latest --backend llvm -o results.json
```

**Arguments:**
- `input`: Input file with cargo test output (required)
- `--os`: Operating system name (default: "unknown")
- `--backend`: Backend type - interpreter, cranelift, llvm, or all (default: "all")
- `-o, --output`: Output JSON file (default: stdout)
- `--pretty`: Pretty-print JSON

**Output Format:**
```json
{
  "os": "windows-latest",
  "backend": "llvm",
  "total": 79,
  "passed": 76,
  "failed": 3,
  "ignored": 0,
  "tests": [
    {
      "name": "test_name",
      "status": "ok",
      "backend": "llvm",
      "project": "01-basic-arithmetic",
      "error": null
    }
  ]
}
```

### 2. `generate_status_report.py`

Generates markdown test status report from JSON results.

**Usage:**
```bash
python scripts/generate_status_report.py results/*.json -o TEST_STATUS.md
```

**Arguments:**
- `inputs`: One or more JSON files from parse_test_results.py (required)
- `-o, --output`: Output markdown file (default: stdout)

**Features:**
- Summary table with pass rates
- Per-project status matrix
- Backend-specific details
- Failed test details with error messages

### 3. `update_docs.py`

Updates CLAUDE.md based on TEST_STATUS.md.

**Usage:**
```bash
python scripts/update_docs.py TEST_STATUS.md CLAUDE.md [--dry-run] [--backup]
```

**Arguments:**
- `test_status`: Path to TEST_STATUS.md (required)
- `claude_md`: Path to CLAUDE.md to update (required)
- `--dry-run`: Preview changes without modifying files
- `--backup`: Create backup of CLAUDE.md before updating

**Updates:**
- Fixes incorrect test count claims
- Updates phase status markers (✅ to ⚠️ for failures)
- Adds reference to TEST_STATUS.md

## Complete Workflow

### Manual Test Run

```bash
# 1. Run all tests
cargo test --workspace --no-fail-fast > test_output.txt 2>&1

# 2. Parse results
python scripts/parse_test_results.py test_output.txt \
  --os windows-latest \
  --backend all \
  -o results.json \
  --pretty

# 3. Generate status report
python scripts/generate_status_report.py results.json -o TEST_STATUS.md

# 4. Update documentation (preview first)
python scripts/update_docs.py TEST_STATUS.md CLAUDE.md --dry-run

# 5. Apply updates
python scripts/update_docs.py TEST_STATUS.md CLAUDE.md --backup
```

### Automated via GitHub Actions

The workflow in `.github/workflows/test-status.yml` automatically:
1. Runs tests on 3 OS platforms (Ubuntu, Windows, macOS)
2. Parses results for each configuration
3. Generates combined TEST_STATUS.md
4. Updates CLAUDE.md
5. Creates PR with documentation updates

**Trigger:** Push to master or pull request

## Requirements

- Python 3.7+
- Standard library only (no external dependencies)

## Testing the Scripts

```bash
# Test parser
python scripts/parse_test_results.py test_output.txt --pretty

# Test report generator
python scripts/generate_status_report.py results.json

# Test doc updater (dry-run)
python scripts/update_docs.py TEST_STATUS.md CLAUDE.md --dry-run
```

## Integration with CI/CD

See `.github/workflows/test-status.yml` for the complete GitHub Actions workflow that uses these scripts to automatically track and document test status across multiple platforms and configurations.
