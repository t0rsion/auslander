#!/usr/bin/env python3
"""Enforce the 700-line ceiling for maintained text sources."""

from __future__ import annotations

import argparse
import os
import sys
import tempfile
import unittest
from collections.abc import Iterator, Sequence
from pathlib import Path

MAX_LINES = 700
TEXT_SUFFIXES = frozenset(
    {
        ".rs",
        ".py",
        ".pyi",
        ".md",
        ".toml",
        ".yml",
        ".yaml",
        ".sh",
        ".bash",
        ".zsh",
        ".fish",
        ".ksh",
    }
)
SHELL_INTERPRETERS = frozenset({"ash", "bash", "dash", "fish", "ksh", "sh", "zsh"})
EXCLUDED_DIRECTORIES = frozenset(
    {
        ".git",
        ".cache",
        ".claude",
        ".mypy_cache",
        ".pytest_cache",
        ".ruff_cache",
        ".venv",
        ".virtualenv",
        ".tox",
        ".nox",
        "__pycache__",
        "build",
        "dist",
        "node_modules",
        "site-packages",
        "target",
        "venv",
        "virtualenv",
    }
)
EXCLUDED_NAMES = frozenset({"Cargo.lock"})
ROOT = Path(__file__).resolve().parents[1]


def _excluded_directory(name: str) -> bool:
    return name in EXCLUDED_DIRECTORIES or (
        name.startswith("paper-") and name.endswith("-private")
    )


def _is_shell_script(path: Path) -> bool:
    try:
        with path.open(encoding="utf-8") as source:
            first_line = source.readline()
    except (OSError, UnicodeError):
        return False
    if not first_line.startswith("#!"):
        return False
    return any(Path(word).name in SHELL_INTERPRETERS for word in first_line[2:].split())


def _is_text_source(path: Path) -> bool:
    if path.name in EXCLUDED_NAMES:
        return False
    suffix = path.suffix.lower()
    return suffix in TEXT_SUFFIXES or (not suffix and _is_shell_script(path))


def _source_files(root: Path) -> Iterator[Path]:
    for directory, names, filenames in os.walk(root):
        names[:] = sorted(name for name in names if not _excluded_directory(name))
        for filename in sorted(filenames):
            path = Path(directory) / filename
            if _is_text_source(path):
                yield path


def _line_count(path: Path) -> int:
    return len(path.read_text(encoding="utf-8").splitlines())


def _measure(root: Path) -> list[tuple[int, Path]]:
    return sorted(
        ((_line_count(path), path) for path in _source_files(root)),
        key=lambda row: row[1].relative_to(root).as_posix(),
    )


def _violations(rows: list[tuple[int, Path]]) -> list[tuple[int, Path]]:
    return [(lines, path) for lines, path in rows if lines > MAX_LINES]


def _run_gate(root: Path) -> int:
    rows = _measure(root)
    violations = _violations(rows)
    print(f"text-source line budget: {len(rows)} files, maximum {MAX_LINES} lines")
    for lines, path in violations:
        relative = path.relative_to(root).as_posix()
        print(f"{relative}: {lines} lines, maximum {MAX_LINES}", file=sys.stderr)
    return int(bool(violations))


class _TextLineBudgetTests(unittest.TestCase):
    def test_supported_sources_and_exclusions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            supported = {
                "code.rs",
                "code.py",
                "stub.pyi",
                "guide.md",
                "config.toml",
                "ci.yml",
                "ci.yaml",
                "run.sh",
                "run.bash",
                "run",
            }
            for relative in supported:
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(
                    "#!/bin/sh\n" if relative == "run" else "x\n", encoding="utf-8"
                )
            for directory_name in EXCLUDED_DIRECTORIES:
                path = root / directory_name / "hidden.md"
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("x\n", encoding="utf-8")
            private = root / "paper-example-private" / "hidden.md"
            private.parent.mkdir(parents=True, exist_ok=True)
            private.write_text("x\n", encoding="utf-8")
            (root / "data.json").write_text("x\n", encoding="utf-8")
            (root / "Cargo.lock").write_text("x\n", encoding="utf-8")
            (root / "run.pyc").write_bytes(b"\x00\x01")
            (root / "python-script").write_text(
                "#!/usr/bin/env python3\n", encoding="utf-8"
            )

            found = {path.relative_to(root).as_posix() for path in _source_files(root)}
            self.assertEqual(found, supported)

    def test_exact_limit_passes_and_next_line_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "at-limit.md").write_text("x\n" * MAX_LINES, encoding="utf-8")
            (root / "over-limit.md").write_text(
                "x\n" * (MAX_LINES + 1), encoding="utf-8"
            )

            rows = {path.name: lines for lines, path in _measure(root)}
            self.assertEqual(rows["at-limit.md"], MAX_LINES)
            self.assertEqual(rows["over-limit.md"], MAX_LINES + 1)
            violations = _violations(_measure(root))
            self.assertEqual(violations, [(MAX_LINES + 1, root / "over-limit.md")])


def _self_test() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(_TextLineBudgetTests)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    return int(not result.wasSuccessful())


def _arguments(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run the focused scanner tests instead of checking the repository",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _arguments(argv)
    if args.self_test:
        return _self_test()
    return _run_gate(ROOT)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeError) as error:
        print(f"text-source line check failed: {error}", file=sys.stderr)
        raise SystemExit(2) from None
