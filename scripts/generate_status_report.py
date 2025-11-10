#!/usr/bin/env python3
"""
Test status report generator for Raven compiler.

Aggregates test results from multiple JSON files (different OS/backend combinations)
and generates a comprehensive markdown report with:
- Summary table showing pass rates by backend and OS
- Per-project status matrix
- Detailed failure information
- Overall statistics

Usage:
    python generate_status_report.py results/*.json -o TEST_STATUS.md
    python generate_status_report.py windows.json linux.json macos.json
"""

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Set


class TestStatusReport:
    """Generates comprehensive test status reports."""

    def __init__(self):
        self.results: List[Dict] = []
        self.backends: Set[str] = set()
        self.os_list: Set[str] = set()
        self.projects: Set[str] = set()

    def add_result(self, result: Dict):
        """Add a test result from JSON file."""
        self.results.append(result)
        self.backends.add(result.get("backend", "unknown"))
        self.os_list.add(result.get("os", "unknown"))

        # Extract projects from tests
        for test in result.get("tests", []):
            project = test.get("project", "unknown")
            if project != "unknown":
                self.projects.add(project)

    def generate_report(self) -> str:
        """Generate complete markdown report."""
        if not self.results:
            return "# Test Status Report\n\nNo test results available.\n"

        lines = []
        lines.append("# Raven Compiler Test Status Report")
        lines.append("")
        lines.append(f"**Total Test Configurations:** {len(self.results)}")
        lines.append("")

        # Overall summary
        lines.append("## Overall Summary")
        lines.append("")
        lines.append(self._generate_summary_table())
        lines.append("")

        # Per-project status
        lines.append("## Test Projects Status")
        lines.append("")
        lines.append(self._generate_project_matrix())
        lines.append("")

        # Backend details
        lines.append("## Backend Details")
        lines.append("")
        lines.append(self._generate_backend_details())
        lines.append("")

        # Failed tests section
        if self._has_failures():
            lines.append("## Failed Tests")
            lines.append("")
            lines.append(self._generate_failure_details())
            lines.append("")

        # Legend
        lines.append("## Legend")
        lines.append("")
        lines.append("- ✅ All tests passing (100%)")
        lines.append("- ⚠️ Some tests failing (partial pass)")
        lines.append("- ❌ All tests failing or not run")
        lines.append("- 🔹 Backend not tested on this OS")
        lines.append("")

        return "\n".join(lines)

    def _generate_summary_table(self) -> str:
        """Generate summary table with pass rates."""
        lines = []
        lines.append("| Backend | OS | Total | Passed | Failed | Ignored | Pass Rate |")
        lines.append("|---------|----|----|--------|--------|---------|-----------|")

        # Sort results for consistent ordering
        sorted_results = sorted(
            self.results,
            key=lambda r: (r.get("backend", ""), r.get("os", ""))
        )

        for result in sorted_results:
            backend = result.get("backend", "unknown")
            os_name = result.get("os", "unknown")
            total = result.get("total", 0)
            passed = result.get("passed", 0)
            failed = result.get("failed", 0)
            ignored = result.get("ignored", 0)

            # Calculate pass rate
            if total > 0:
                pass_rate = (passed / total) * 100
                status = self._get_status_emoji(pass_rate)
            else:
                pass_rate = 0.0
                status = "❌"

            lines.append(
                f"| {status} {backend} | {os_name} | {total} | {passed} | "
                f"{failed} | {ignored} | {pass_rate:.1f}% |"
            )

        return "\n".join(lines)

    def _generate_project_matrix(self) -> str:
        """Generate per-project status matrix."""
        if not self.projects:
            return "*No project-specific tests found.*"

        lines = []

        # Group results by project
        project_results = self._group_by_project()

        # Sort projects
        sorted_projects = sorted(self.projects)

        for project in sorted_projects:
            lines.append(f"### {project}")
            lines.append("")
            lines.append("| Backend | OS | Status | Passed/Total |")
            lines.append("|---------|-------|--------|--------------|")

            if project in project_results:
                for backend_os, stats in sorted(project_results[project].items()):
                    backend, os_name = backend_os
                    total = stats["total"]
                    passed = stats["passed"]

                    if total > 0:
                        pass_rate = (passed / total) * 100
                        status = self._get_status_emoji(pass_rate)
                    else:
                        status = "🔹"
                        pass_rate = 0.0

                    lines.append(
                        f"| {backend} | {os_name} | {status} | "
                        f"{passed}/{total} ({pass_rate:.0f}%) |"
                    )

            lines.append("")

        return "\n".join(lines)

    def _generate_backend_details(self) -> str:
        """Generate detailed backend statistics."""
        lines = []

        # Group by backend
        backend_stats = defaultdict(lambda: {"total": 0, "passed": 0, "failed": 0})

        for result in self.results:
            backend = result.get("backend", "unknown")
            backend_stats[backend]["total"] += result.get("total", 0)
            backend_stats[backend]["passed"] += result.get("passed", 0)
            backend_stats[backend]["failed"] += result.get("failed", 0)

        for backend in sorted(backend_stats.keys()):
            stats = backend_stats[backend]
            total = stats["total"]
            passed = stats["passed"]
            failed = stats["failed"]

            if total > 0:
                pass_rate = (passed / total) * 100
                status = self._get_status_emoji(pass_rate)
            else:
                pass_rate = 0.0
                status = "❌"

            lines.append(f"### {status} {backend.capitalize()}")
            lines.append("")
            lines.append(f"- **Total Tests:** {total}")
            lines.append(f"- **Passed:** {passed}")
            lines.append(f"- **Failed:** {failed}")
            lines.append(f"- **Pass Rate:** {pass_rate:.1f}%")
            lines.append("")

        return "\n".join(lines)

    def _generate_failure_details(self) -> str:
        """Generate detailed failure information."""
        lines = []

        for result in self.results:
            backend = result.get("backend", "unknown")
            os_name = result.get("os", "unknown")
            failed_tests = [
                t for t in result.get("tests", [])
                if t.get("status") == "failed"
            ]

            if failed_tests:
                lines.append(f"### {backend} on {os_name}")
                lines.append("")

                for test in failed_tests:
                    test_name = test.get("name", "unknown")
                    project = test.get("project", "unknown")
                    error = test.get("error")

                    lines.append(f"**Test:** `{test_name}`")
                    lines.append(f"**Project:** {project}")

                    if error:
                        lines.append("")
                        lines.append("```")
                        lines.append(error)
                        lines.append("```")

                    lines.append("")

        return "\n".join(lines)

    def _group_by_project(self) -> Dict:
        """Group test results by project."""
        project_results = defaultdict(dict)

        for result in self.results:
            backend = result.get("backend", "unknown")
            os_name = result.get("os", "unknown")

            for test in result.get("tests", []):
                project = test.get("project", "unknown")
                if project == "unknown":
                    continue

                key = (backend, os_name)
                if key not in project_results[project]:
                    project_results[project][key] = {"total": 0, "passed": 0}

                project_results[project][key]["total"] += 1
                if test.get("status") == "ok":
                    project_results[project][key]["passed"] += 1

        return project_results

    def _get_status_emoji(self, pass_rate: float) -> str:
        """Get status emoji based on pass rate."""
        if pass_rate >= 100.0:
            return "✅"
        elif pass_rate >= 50.0:
            return "⚠️"
        else:
            return "❌"

    def _has_failures(self) -> bool:
        """Check if any results have failures."""
        return any(result.get("failed", 0) > 0 for result in self.results)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Generate test status report from JSON results",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s results/*.json -o TEST_STATUS.md
  %(prog)s windows.json linux.json --output report.md
  %(prog)s *.json  # Outputs to stdout
        """
    )

    parser.add_argument(
        "inputs",
        nargs="+",
        help="Input JSON files from parse_test_results.py"
    )
    parser.add_argument(
        "-o", "--output",
        help="Output markdown file (default: stdout)"
    )

    args = parser.parse_args()

    # Create report generator
    report = TestStatusReport()

    # Load all result files
    for input_file in args.inputs:
        try:
            with open(input_file, 'r', encoding='utf-8') as f:
                result = json.load(f)
                report.add_result(result)
        except FileNotFoundError:
            print(f"Warning: File '{input_file}' not found", file=sys.stderr)
        except json.JSONDecodeError as e:
            print(f"Warning: Invalid JSON in '{input_file}': {e}", file=sys.stderr)
        except Exception as e:
            print(f"Warning: Error reading '{input_file}': {e}", file=sys.stderr)

    # Generate report
    markdown_report = report.generate_report()

    # Write output
    if args.output:
        try:
            with open(args.output, 'w', encoding='utf-8') as f:
                f.write(markdown_report)
            print(f"Report written to {args.output}", file=sys.stderr)
        except Exception as e:
            print(f"Error writing output file: {e}", file=sys.stderr)
            sys.exit(1)
    else:
        print(markdown_report)


if __name__ == "__main__":
    main()
