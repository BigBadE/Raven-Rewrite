#!/usr/bin/env bash

set -euo pipefail

# Usage:
#   ./scripts/verify.sh [--cov] [--fixture]
#
# Flags:
#   --cov       Run coverage testing (delegates to coverage.sh)
#   --fixture   Run only fixture tests with coverage, other tests normally
#
# Environment variables:
#   MERLIN_CI   Set to skip clean step in CI environments

check_file_sizes() {
  local max_lines=500
  local violations=$(
          find crates -type f -name '*.rs' -print0 |
          xargs -0 awk -v max="$max_lines" '
            { count[FILENAME]++ }
            ENDFILE { if (count[FILENAME] > max) print FILENAME ": " count[FILENAME] " lines" }
          '
        )

  if [ -n "$violations" ]; then
    echo "ERROR: The following files exceed $max_lines lines:"
    echo "$violations"
    return 1
  fi

  return 0
}

check_allows() {
  # Find Rust files that might have allow or cfg_attr
  mapfile -t files < <(
    find crates -type f -name '*.rs' -print0 |
    xargs -0 grep -lE '#!?\[(allow|cfg_attr)' 2>&1 | grep -v "No such file"
  )

  local violations=false

  for file in "${files[@]}"; do
    # Check for disallowed allow annotations
    result=$(awk '
      function norm(s) { gsub(/[[:space:]]+/, "", s); return s }

      BEGIN { in_attr = 0; attr = "" }

      {
        # If currently collecting an attribute, continue
        if (in_attr) {
          attr = attr $0
          if (index($0, "]")) {
            n = norm(attr)
            print "DISALLOWED:::" FILENAME ":::" n
            exit 1
            in_attr = 0
            attr = ""
          }
          next
        }

        # Detect start of an attribute with allow or cfg_attr
        if ($0 ~ /#(!)?\[.*allow/ || $0 ~ /#!\[cfg_attr/) {
          attr = $0
          if (index($0, ")]")) {
            n = norm(attr)
            print "DISALLOWED:::" FILENAME ":::" n
            exit 1
            attr = ""
          } else {
            in_attr = 1
          }
        }
      }

      END {
        if (in_attr && attr != "") {
          n = norm(attr)
          print "DISALLOWED|||" FILENAME "|||" n
          exit 1
        }
      }
    ' "$file")

    if [ -n "$result" ]; then
      echo "ERROR: Found disallowed #[allow] annotation:"
      echo "$result" | awk -F':::' '{print "  File: " $2; print "  Annotation: " $3}'
      violations=true
    fi
  done

  if $violations; then
    echo "All allows must be removed. Fix the code instead of silencing warnings."
    return 1
  fi

  return 0
}

RUN_COVERAGE=false
FIXTURE_ONLY=false

for arg in "$@"; do
  case "$arg" in
    --cov)
      RUN_COVERAGE=true
      shift
      ;;
    --fixture)
      FIXTURE_ONLY=true
      shift
      ;;
    *)
      # ignore unknown args (forward compatibility)
      ;;
  esac
done

# Check file sizes
echo "[verify] Checking file sizes..."
check_file_sizes

# Check for disallowed allow annotations
echo "[verify] Checking for disallowed #[allow] annotations..."
if ! check_allows; then
  echo "FATAL: check_allows failed" >&2
  exit 1
fi

# Format, lint, and test
cargo fmt -q
cargo clippy --no-deps --bins --lib --tests --benches --all-features -- -D warnings

# Delegate to coverage.sh if --cov is passed (skip normal tests)
if [ "$RUN_COVERAGE" = true ]; then
  if [ "$FIXTURE_ONLY" = true ]; then
    # Run all tests first to ensure everything passes
    echo "[verify] Running all tests..."
    cargo nextest run --run-ignored all

    # Then generate coverage for fixtures only
    exec "$(dirname "${BASH_SOURCE[0]}")/coverage.sh" --fixture
  else
    exec "$(dirname "${BASH_SOURCE[0]}")/coverage.sh"
  fi
fi

# Run full workspace tests
echo "[verify] Running tests..."
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"

# Run main tests
cargo nextest run --run-ignored all

if [ -z "${MERLIN_CI:-}" ]; then
  echo "[coverage] Cleaning old build artifacts..."
  cargo sweep --time 1 -r
else
  echo "[coverage] Skipping clean step (MERLIN_CI set)"
fi