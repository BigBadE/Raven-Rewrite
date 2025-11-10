#!/usr/bin/env python3
"""
Documentation updater for Raven compiler.

Updates CLAUDE.md based on TEST_STATUS.md:
- Fixes incorrect test count claims (e.g., "79/79 passing" when some fail)
- Updates phase completion status (✅ to ⚠️ for phases with failures)
- Adds reference to TEST_STATUS.md
- Preserves document structure and content

Usage:
    python update_docs.py TEST_STATUS.md CLAUDE.md
    python update_docs.py TEST_STATUS.md CLAUDE.md --dry-run  # Preview changes
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple


class DocUpdater:
    """Updates documentation based on test status."""

    def __init__(self, test_status_content: str):
        self.test_status = test_status_content
        self.changes: List[str] = []

    def update_claude_md(self, content: str) -> Tuple[str, List[str]]:
        """
        Update CLAUDE.md content.

        Args:
            content: Current CLAUDE.md content

        Returns:
            Tuple of (updated_content, list_of_changes)
        """
        updated = content
        self.changes = []

        # Extract test statistics from TEST_STATUS.md
        stats = self._extract_test_stats()

        # Update test count claims
        updated = self._update_test_counts(updated, stats)

        # Update phase status markers
        updated = self._update_phase_status(updated, stats)

        # Add TEST_STATUS.md reference if not present
        updated = self._add_test_status_reference(updated)

        return updated, self.changes

    def _extract_test_stats(self) -> Dict:
        """Extract test statistics from TEST_STATUS.md."""
        stats = {
            "total": 0,
            "passed": 0,
            "failed": 0,
            "pass_rate": 0.0,
            "by_backend": {},
            "by_project": {}
        }

        # Extract overall stats from summary table
        # Pattern: | backend | os | total | passed | failed | ignored | pass_rate |
        table_pattern = re.compile(
            r'\|\s*[✅⚠️❌🔹]?\s*(\w+)\s*\|\s*(\S+)\s*\|\s*(\d+)\s*\|'
            r'\s*(\d+)\s*\|\s*(\d+)\s*\|\s*\d+\s*\|\s*([\d.]+)%',
            re.MULTILINE
        )

        for match in table_pattern.finditer(self.test_status):
            backend = match.group(1)
            total = int(match.group(3))
            passed = int(match.group(4))
            failed = int(match.group(5))

            stats["total"] += total
            stats["passed"] += passed
            stats["failed"] += failed

            if backend not in stats["by_backend"]:
                stats["by_backend"][backend] = {
                    "total": 0,
                    "passed": 0,
                    "failed": 0
                }

            stats["by_backend"][backend]["total"] += total
            stats["by_backend"][backend]["passed"] += passed
            stats["by_backend"][backend]["failed"] += failed

        # Calculate overall pass rate
        if stats["total"] > 0:
            stats["pass_rate"] = (stats["passed"] / stats["total"]) * 100

        return stats

    def _update_test_counts(self, content: str, stats: Dict) -> str:
        """Update test count claims in document."""
        # Pattern: X/Y tests passing (Z%)
        # Pattern: X/Y passing (Z%)
        # Pattern: X/Y passing
        patterns = [
            r'(\d+)/(\d+)\s+tests?\s+passing\s*\((\d+)%\)',
            r'(\d+)/(\d+)\s+passing\s*\((\d+)%\)',
            r'(\d+)/(\d+)\s+passing'
        ]

        for pattern in patterns:
            matches = list(re.finditer(pattern, content))
            for match in matches:
                old_text = match.group(0)
                claimed_passed = int(match.group(1))
                claimed_total = int(match.group(2))

                # Check if claim is accurate
                if stats["total"] > 0:
                    actual_passed = stats["passed"]
                    actual_total = stats["total"]
                    actual_rate = stats["pass_rate"]

                    # If claim is wrong, update it
                    if claimed_passed != actual_passed or claimed_total != actual_total:
                        if '%' in old_text:
                            new_text = f"{actual_passed}/{actual_total} tests passing ({actual_rate:.0f}%)"
                        else:
                            new_text = f"{actual_passed}/{actual_total} passing"

                        content = content.replace(old_text, new_text, 1)
                        self.changes.append(
                            f"Updated test count: '{old_text}' -> '{new_text}'"
                        )

        return content

    def _update_phase_status(self, content: str, stats: Dict) -> str:
        """Update phase completion status markers."""
        # If there are failures, change ✅ to ⚠️ for relevant phases
        if stats["failed"] > 0:
            # Pattern: ## Phase N Accomplishments ✅
            phase_pattern = re.compile(r'^(##\s+Phase\s+\d+[^✅⚠️]*)(✅)', re.MULTILINE)

            def replace_status(match):
                prefix = match.group(1)
                # Check if this phase has failures by looking at content after header
                # For now, mark all phases as ⚠️ if ANY test fails
                # (More sophisticated logic would check phase-specific tests)
                self.changes.append(
                    f"Changed phase status from ✅ to ⚠️ due to test failures"
                )
                return prefix + "⚠️"

            # Only replace if there are failures
            if stats["failed"] > 0:
                content = phase_pattern.sub(replace_status, content)

        return content

    def _add_test_status_reference(self, content: str) -> str:
        """Add reference to TEST_STATUS.md if not present."""
        reference = "\n## Test Status\n\nFor detailed test results across all platforms and backends, see [TEST_STATUS.md](./TEST_STATUS.md).\n"

        # Check if reference already exists
        if "TEST_STATUS.md" not in content:
            # Add before the final line or at end
            content = content.rstrip() + "\n" + reference
            self.changes.append("Added reference to TEST_STATUS.md")

        return content


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Update CLAUDE.md based on test status",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s TEST_STATUS.md CLAUDE.md
  %(prog)s TEST_STATUS.md CLAUDE.md --dry-run  # Preview changes
  %(prog)s TEST_STATUS.md CLAUDE.md --backup   # Create backup before updating
        """
    )

    parser.add_argument(
        "test_status",
        help="Path to TEST_STATUS.md file"
    )
    parser.add_argument(
        "claude_md",
        help="Path to CLAUDE.md file to update"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show changes without modifying files"
    )
    parser.add_argument(
        "--backup",
        action="store_true",
        help="Create backup of CLAUDE.md before updating"
    )

    args = parser.parse_args()

    # Read TEST_STATUS.md
    try:
        with open(args.test_status, 'r', encoding='utf-8') as f:
            test_status_content = f.read()
    except FileNotFoundError:
        print(f"Error: Test status file '{args.test_status}' not found", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error reading test status file: {e}", file=sys.stderr)
        sys.exit(1)

    # Read CLAUDE.md
    try:
        with open(args.claude_md, 'r', encoding='utf-8') as f:
            claude_content = f.read()
    except FileNotFoundError:
        print(f"Error: Documentation file '{args.claude_md}' not found", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error reading documentation file: {e}", file=sys.stderr)
        sys.exit(1)

    # Update documentation
    updater = DocUpdater(test_status_content)
    updated_content, changes = updater.update_claude_md(claude_content)

    # Report changes
    if changes:
        print("Changes to be applied:", file=sys.stderr)
        for change in changes:
            print(f"  - {change}", file=sys.stderr)
        print(f"\nTotal changes: {len(changes)}", file=sys.stderr)
    else:
        print("No changes needed.", file=sys.stderr)

    # Handle dry-run
    if args.dry_run:
        print("\n--- Dry run mode: No files modified ---", file=sys.stderr)
        if changes:
            print("\nUpdated content preview (first 500 chars):", file=sys.stderr)
            print(updated_content[:500])
        return

    # Create backup if requested
    if args.backup and changes:
        backup_path = args.claude_md + ".backup"
        try:
            with open(backup_path, 'w', encoding='utf-8') as f:
                f.write(claude_content)
            print(f"Backup created: {backup_path}", file=sys.stderr)
        except Exception as e:
            print(f"Warning: Failed to create backup: {e}", file=sys.stderr)

    # Write updated content
    if changes:
        try:
            with open(args.claude_md, 'w', encoding='utf-8') as f:
                f.write(updated_content)
            print(f"\nSuccessfully updated {args.claude_md}", file=sys.stderr)
        except Exception as e:
            print(f"Error writing documentation file: {e}", file=sys.stderr)
            sys.exit(1)


if __name__ == "__main__":
    main()
