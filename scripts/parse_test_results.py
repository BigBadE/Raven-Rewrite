#!/usr/bin/env python3
"""
Test result parser for Raven compiler test suite.

Parses cargo test output and extracts structured test results including:
- Test names, status (ok/FAILED/ignored)
- Backend identification (interpreter/cranelift/llvm)
- Test project identification (01-basic-arithmetic, etc.)
- Error messages for failed tests
- Summary statistics (total/passed/failed/ignored)

Usage:
    python parse_test_results.py <test_output.txt> --os windows-latest --backend llvm -o results.json
    python parse_test_results.py test_output.txt  # Defaults to "unknown" OS/backend
"""

import argparse
import json
import re
import sys
from typing import Dict, List, Optional


class TestResult:
    """Represents a single test result."""

    def __init__(self, name: str, status: str, backend: Optional[str] = None,
                 project: Optional[str] = None, error: Optional[str] = None):
        self.name = name
        self.status = status
        self.backend = backend or "unknown"
        self.project = project or "unknown"
        self.error = error

    def to_dict(self) -> Dict:
        """Convert to dictionary for JSON serialization."""
        result = {
            "name": self.name,
            "status": self.status,
            "backend": self.backend,
            "project": self.project
        }
        if self.error:
            result["error"] = self.error
        return result


class TestResultParser:
    """Parser for cargo test output."""

    # Patterns for parsing test output
    TEST_RESULT_PATTERN = re.compile(r'^test\s+(\S+)\s+\.\.\.\s+(ok|FAILED|ignored)', re.MULTILINE)
    # Match cargo test summary - flexible to handle optional fields after ignored
    TEST_SUMMARY_PATTERN = re.compile(
        r'test result:\s+(?:ok|FAILED)\.\s+(\d+)\s+passed;\s+(\d+)\s+failed;\s+(\d+)\s+ignored'
    )
    PROJECT_PATTERN = re.compile(r'(\d{2}-[\w-]+)')
    BACKEND_PATTERN = re.compile(r'_(interpreter|cranelift|llvm)(?:_|\b)')

    def __init__(self, os_name: str = "unknown", backend: str = "unknown"):
        """
        Initialize parser.

        Args:
            os_name: Operating system (e.g., "windows-latest", "ubuntu-latest")
            backend: Backend type (e.g., "llvm", "cranelift", "interpreter")
        """
        self.os_name = os_name
        self.default_backend = backend
        self.tests: List[TestResult] = []
        self.summary = {
            "total": 0,
            "passed": 0,
            "failed": 0,
            "ignored": 0
        }

    def parse(self, content: str) -> Dict:
        """
        Parse test output content.

        Args:
            content: Raw cargo test output text

        Returns:
            Dictionary with parsed results and summary
        """
        self._parse_test_results(content)
        self._parse_summary(content)

        return self._build_output()

    def _parse_test_results(self, content: str):
        """Extract individual test results from output."""
        for match in self.TEST_RESULT_PATTERN.finditer(content):
            test_name = match.group(1)
            status = match.group(2).lower()

            # Extract backend from test name
            backend = self._extract_backend(test_name)

            # Extract project from test name
            project = self._extract_project(test_name)

            # For failed tests, try to find error message
            error = None
            if status == "failed":
                error = self._find_error_message(content, test_name)

            test_result = TestResult(
                name=test_name,
                status=status,
                backend=backend,
                project=project,
                error=error
            )
            self.tests.append(test_result)

    def _extract_backend(self, test_name: str) -> str:
        """Extract backend name from test name."""
        match = self.BACKEND_PATTERN.search(test_name)
        if match:
            return match.group(1)
        return self.default_backend

    def _extract_project(self, test_name: str) -> str:
        """Extract project identifier from test name."""
        match = self.PROJECT_PATTERN.search(test_name)
        if match:
            return match.group(1)
        return "unknown"

    def _find_error_message(self, content: str, test_name: str) -> Optional[str]:
        """
        Find error message for a failed test.

        Searches for the test name followed by failure output.
        Extracts up to 10 lines of error context.
        """
        # Look for "test <name> ... FAILED" followed by error output
        pattern = rf'test\s+{re.escape(test_name)}\s+\.\.\.\s+FAILED\s*\n((?:.*\n){{0,10}})'
        match = re.search(pattern, content)
        if match:
            error_lines = match.group(1).strip()
            # Limit error message length
            if len(error_lines) > 500:
                error_lines = error_lines[:500] + "..."
            return error_lines
        return None

    def _parse_summary(self, content: str):
        """Parse test summary statistics."""
        # Aggregate all summary lines (multiple exist for different test suites)
        matches = list(self.TEST_SUMMARY_PATTERN.finditer(content))
        if matches:
            total_passed = 0
            total_failed = 0
            total_ignored = 0

            for match in matches:
                total_passed += int(match.group(1))
                total_failed += int(match.group(2))
                total_ignored += int(match.group(3))

            self.summary = {
                "total": total_passed + total_failed + total_ignored,
                "passed": total_passed,
                "failed": total_failed,
                "ignored": total_ignored
            }
        else:
            # Fallback: count from parsed tests
            self.summary = {
                "total": len(self.tests),
                "passed": sum(1 for t in self.tests if t.status == "ok"),
                "failed": sum(1 for t in self.tests if t.status == "failed"),
                "ignored": sum(1 for t in self.tests if t.status == "ignored")
            }

    def _build_output(self) -> Dict:
        """Build final output dictionary."""
        return {
            "os": self.os_name,
            "backend": self.default_backend,
            "total": self.summary["total"],
            "passed": self.summary["passed"],
            "failed": self.summary["failed"],
            "ignored": self.summary["ignored"],
            "tests": [t.to_dict() for t in self.tests]
        }


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Parse cargo test output into structured JSON",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s test_output.txt
  %(prog)s test_output.txt --os ubuntu-latest --backend llvm -o results.json
  %(prog)s test_output.txt --os windows-latest --backend all
        """
    )

    parser.add_argument(
        "input",
        help="Input file containing cargo test output"
    )
    parser.add_argument(
        "--os",
        default="unknown",
        help="Operating system name (e.g., windows-latest, ubuntu-latest)"
    )
    parser.add_argument(
        "--backend",
        default="all",
        help="Backend type (interpreter, cranelift, llvm, or all)"
    )
    parser.add_argument(
        "-o", "--output",
        help="Output JSON file (default: stdout)"
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print JSON output"
    )

    args = parser.parse_args()

    # Read input file
    try:
        with open(args.input, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except FileNotFoundError:
        print(f"Error: Input file '{args.input}' not found", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error reading input file: {e}", file=sys.stderr)
        sys.exit(1)

    # Parse test results
    result_parser = TestResultParser(os_name=args.os, backend=args.backend)
    results = result_parser.parse(content)

    # Format output
    indent = 2 if args.pretty else None
    json_output = json.dumps(results, indent=indent)

    # Write output
    if args.output:
        try:
            with open(args.output, 'w', encoding='utf-8') as f:
                f.write(json_output)
            print(f"Results written to {args.output}", file=sys.stderr)
        except Exception as e:
            print(f"Error writing output file: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        print(json_output)

    # Exit with non-zero if tests failed
    if results["failed"] > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
