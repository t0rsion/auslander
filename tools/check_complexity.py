#!/usr/bin/env python3
"""Audit source McCabe complexity for maintained Rust, Python, and GAP code."""

from __future__ import annotations

import argparse
import ast
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from collections.abc import Iterator, Sequence
from pathlib import Path
from typing import Any
from unittest.mock import patch

try:
    from .check_complexity_gap import gap_functions as _gap_parser
    from .check_complexity_macros import (
        macro_invocations as _macro_invocations,
    )
    from .check_complexity_macros import (
        rust_macros as _macro_parser,
    )
    from .check_complexity_source import tokens as _source_tokens
except ImportError:
    from check_complexity_gap import gap_functions as _gap_parser
    from check_complexity_macros import (
        macro_invocations as _macro_invocations,
    )
    from check_complexity_macros import (
        rust_macros as _macro_parser,
    )
    from check_complexity_source import tokens as _source_tokens


ANALYZER = "rust-code-analysis-cli"
ANALYZER_VERSION = "0.0.25"
MAX_COMPLEXITY = 10
BANDS = ("1-5", "6-10", "11-15", ">15")
SOURCE_SUFFIXES = {".rs": "rust", ".py": "python", ".pyi": "python", ".g": "gap"}
EXCLUDED_DIRECTORIES = frozenset(
    {
        ".git",
        ".cache",
        ".claude",
        ".mypy_cache",
        ".pytest_cache",
        ".ruff_cache",
        ".tox",
        ".venv",
        ".virtualenv",
        "__pycache__",
        "build",
        "dist",
        "external__qpa",
        "node_modules",
        "site-packages",
        "target",
        "venv",
        "vendor",
        "virtualenv",
    }
)
ROOT = Path(__file__).resolve().parents[1]


def _band(value: int) -> str:
    if value <= 5:
        return "1-5"
    if value <= 10:
        return "6-10"
    if value <= 15:
        return "11-15"
    return ">15"


def _excluded_directory(name: str) -> bool:
    return name in EXCLUDED_DIRECTORIES or (
        name.startswith("paper-") and name.endswith("-private")
    )


def _spaces(space: dict[str, Any]) -> Iterator[dict[str, Any]]:
    for child in space.get("spaces", []):
        yield child
        yield from _spaces(child)


def _cyclomatic(space: dict[str, Any]) -> int:
    try:
        value = float(space["metrics"]["cyclomatic"]["sum"])
    except (KeyError, TypeError, ValueError) as error:
        raise RuntimeError("analyzer output has no cyclomatic metric") from error
    return round(value)


def _direct_cyclomatic(space: dict[str, Any]) -> int:
    nested = sum(_cyclomatic(child) for child in space.get("spaces", []))
    direct = _cyclomatic(space) - nested
    if direct < 1:
        name = space.get("name", "<anonymous>")
        raise RuntimeError(f"analyzer gave {name} direct complexity {direct}")
    return direct


def _analyzer() -> str:
    executable = shutil.which(ANALYZER)
    if executable is None:
        raise RuntimeError(
            f"{ANALYZER} {ANALYZER_VERSION} is required; install it with cargo"
        )
    version = subprocess.run(
        [executable, "--version"], check=True, capture_output=True, text=True
    ).stdout.strip()
    expected = f"{ANALYZER} {ANALYZER_VERSION}"
    if version != expected:
        raise RuntimeError(f"expected {expected}, found {version}")
    return executable


def _source_files(root: Path) -> list[Path]:
    found: list[Path] = []
    for directory, names, filenames in os.walk(root):
        names[:] = sorted(name for name in names if not _excluded_directory(name))
        for filename in sorted(filenames):
            path = Path(directory) / filename
            if path.suffix.lower() in SOURCE_SUFFIXES:
                found.append(path)
    return sorted(found, key=lambda path: path.relative_to(root).as_posix())


def _line_count(path: Path) -> int:
    return len(path.read_text(encoding="utf-8").splitlines())


def _relative(path: str, root: Path) -> str:
    candidate = Path(path)
    if candidate.is_absolute():
        try:
            return candidate.relative_to(root).as_posix()
        except ValueError as error:
            raise RuntimeError(
                f"analyzer path is outside the repository: {path}"
            ) from error
    return Path(os.path.normpath(path)).as_posix()


def _analysis(executable: str, root: Path) -> Iterator[dict[str, Any]]:
    for directory, glob in (
        ("crates", "**/*.rs"),
        ("crates", "**/*.py"),
        ("tools", "**/*.rs"),
        ("tools", "**/*.py"),
    ):
        if not (root / directory).is_dir():
            continue
        command = [
            executable,
            "-p",
            directory,
            "-m",
            "-O",
            "json",
            "-j",
            "1",
            "-I",
            glob,
        ]
        completed = subprocess.run(
            command, cwd=root, check=True, capture_output=True, text=True
        )
        for line in completed.stdout.splitlines():
            if line:
                yield json.loads(line)


def _analyzer_inventory(files: Sequence[Path], root: Path) -> set[str]:
    return {
        path.relative_to(root).as_posix()
        for path in files
        if path.suffix.lower() in {".rs", ".py"}
    }


def _analysis_coverage(inventory: set[str], analyzed: set[str]) -> None:
    missing = sorted(inventory - analyzed)
    if missing:
        listed = "\n".join(f"  {path}" for path in missing)
        raise RuntimeError(
            "analyzer omitted maintained Rust/Python files:\n" + listed
        )


def _scope(
    *,
    path: str,
    language: str,
    kind: str,
    name: str,
    start_line: int,
    end_line: int,
    complexity: int,
    metric: str,
    raw_complexity: int | None = None,
    extra: dict[str, Any] | None = None,
) -> dict[str, Any]:
    result: dict[str, Any] = {
        "complexity": complexity,
        "end_line": end_line,
        "kind": kind,
        "language": language,
        "loc": end_line - start_line + 1,
        "metric": metric,
        "name": name,
        "path": path,
        "start_line": start_line,
    }
    if raw_complexity is not None:
        result["raw_complexity"] = raw_complexity
    if extra:
        result.update(extra)
    return result


def _analyzer_scopes(
    executable: str, root: Path, files: Sequence[Path]
) -> list[dict[str, Any]]:
    inventory = _analyzer_inventory(files, root)
    analyzed: set[str] = set()
    scopes: list[dict[str, Any]] = []
    for unit in _analysis(executable, root):
        path = _relative(str(unit["name"]), root)
        if path not in inventory:
            continue
        analyzed.add(path)
        language = SOURCE_SUFFIXES[Path(path).suffix.lower()]
        for space in _spaces(unit):
            if space.get("kind") not in {"function", "closure"}:
                continue
            start_line = int(space["start_line"])
            end_line = int(space["end_line"])
            scopes.append(
                _scope(
                    path=path,
                    language=language,
                    kind=str(space["kind"]),
                    name=str(space.get("name", "")),
                    start_line=start_line,
                    end_line=end_line,
                    complexity=_direct_cyclomatic(space),
                    raw_complexity=_cyclomatic(space),
                    metric=f"{ANALYZER}-{ANALYZER_VERSION}",
                )
            )
    _analysis_coverage(inventory, analyzed)
    return scopes


def _python_decisions(node: ast.AST, root: bool = True) -> int:
    if not root and isinstance(
        node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
    ):
        return 0
    decisions = 0
    if isinstance(node, (ast.If, ast.For, ast.AsyncFor, ast.While, ast.IfExp)):
        decisions += 1
    elif isinstance(node, ast.BoolOp):
        decisions += len(node.values) - 1
    elif isinstance(node, ast.Try):
        decisions += len(node.handlers)
    elif isinstance(node, ast.Match):
        decisions += len(node.cases)
    elif isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
        decisions += len(node.generators)
    for child in ast.iter_child_nodes(node):
        decisions += _python_decisions(child, root=False)
    return decisions


def _stub_visit(
    node: ast.AST, relative: str, depth: int = 0
) -> Iterator[dict[str, Any]]:
    for child in ast.iter_child_nodes(node):
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield _scope(
                path=relative,
                language="python",
                kind="closure" if depth else "function",
                name=child.name,
                start_line=int(child.lineno),
                end_line=int(getattr(child, "end_lineno", child.lineno)),
                complexity=1 + _python_decisions(child),
                metric="python-ast-stub-source",
            )
            yield from _stub_visit(child, relative, depth + 1)
        else:
            yield from _stub_visit(child, relative, depth)


def _stub_scopes(root: Path, files: Sequence[Path]) -> list[dict[str, Any]]:
    scopes: list[dict[str, Any]] = []
    for path in files:
        if path.suffix.lower() != ".pyi":
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        scopes.extend(_stub_visit(tree, path.relative_to(root).as_posix()))
    return scopes


def _rust_macros(path: Path, root: Path) -> list[dict[str, Any]]:
    return _macro_parser(path, root, _scope)


def _gap_functions(path: Path, root: Path) -> list[dict[str, Any]]:
    return _gap_parser(path, root, _scope)


def _scope_summary(scopes: Sequence[dict[str, Any]]) -> dict[str, Any]:
    counts = {band: 0 for band in BANDS}
    by_language = {language: 0 for language in ("gap", "python", "rust")}
    maximum = 0
    for scope in scopes:
        complexity = int(scope["complexity"])
        counts[_band(complexity)] += 1
        by_language[str(scope["language"])] += 1
        maximum = max(maximum, complexity)
    return {
        "bands": counts,
        "by_language": by_language,
        "max": maximum,
        "total": len(scopes),
    }


def _file_inventory(
    root: Path, files: Sequence[Path]
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    by_language = {
        language: {"files": 0, "physical_loc": 0}
        for language in ("gap", "python", "rust")
    }
    rows = []
    for path in files:
        language = SOURCE_SUFFIXES[path.suffix.lower()]
        lines = _line_count(path)
        by_language[language]["files"] += 1
        by_language[language]["physical_loc"] += lines
        rows.append(
            {
                "language": language,
                "loc": lines,
                "path": path.relative_to(root).as_posix(),
            }
        )
    return by_language, rows


def _special_scopes(
    files: Sequence[Path], root: Path
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, int]]:
    gap_scopes: list[dict[str, Any]] = []
    macro_scopes: list[dict[str, Any]] = []
    rust_files = [path for path in files if path.suffix.lower() == ".rs"]
    for path in files:
        if path.suffix.lower() == ".g":
            gap_scopes.extend(_gap_functions(path, root))
        elif path.suffix.lower() == ".rs":
            macro_scopes.extend(_rust_macros(path, root))
    names = {str(scope["name"]) for scope in macro_scopes}
    invocation_counts = _macro_invocations(rust_files, names)
    for scope in macro_scopes:
        scope["invocations"] = invocation_counts[str(scope["name"])]
    return gap_scopes, macro_scopes, invocation_counts


def _scope_key(scope: dict[str, Any]) -> tuple[Any, ...]:
    return (scope["path"], scope["start_line"], scope["end_line"], scope["name"])


def _sort_scopes(*groups: list[dict[str, Any]]) -> None:
    for scopes in groups:
        scopes.sort(key=_scope_key)


def _violations(scopes: Sequence[dict[str, Any]]) -> list[dict[str, Any]]:
    return [scope for scope in scopes if scope["complexity"] > MAX_COMPLEXITY]


def _audit(root: Path, executable: str) -> dict[str, Any]:
    files = _source_files(root)
    by_language, file_rows = _file_inventory(root, files)
    callable_scopes = _analyzer_scopes(executable, root, files)
    callable_scopes.extend(_stub_scopes(root, files))
    gap_scopes, macro_scopes, invocation_counts = _special_scopes(files, root)
    callable_scopes.extend(gap_scopes)
    _sort_scopes(callable_scopes, macro_scopes)
    source_loc = sum(row["loc"] for row in file_rows)
    callable_violations = _violations(callable_scopes)
    macro_violations = _violations(macro_scopes)
    return {
        "bands": BANDS,
        "files": file_rows,
        "metric": "direct-source-mccabe",
        "policy": {
            "1-5": "leave",
            "6-10": "refactor when touched",
            "11-15": "refactor now",
            ">15": "split",
            "gate": "complexity at most 10 for callables and macro templates",
        },
        "scope": {
            "all": _scope_summary([*callable_scopes, *macro_scopes]),
            "callables": _scope_summary(callable_scopes),
            "macros": _scope_summary(macro_scopes),
        },
        "source": {
            "files": len(file_rows),
            "physical_loc": source_loc,
            "by_language": by_language,
        },
        "macro_source_limit": {
            "expansion_bound_measured": False,
            "invocations": sum(invocation_counts.values()),
            "templates": len(macro_scopes),
            "text": "Macro templates are measured before expansion. Invocation output is not measured.",
        },
        "scopes": {
            "callables": callable_scopes,
            "macros": macro_scopes,
        },
        "violations": {
            "callables": callable_violations,
            "macros": macro_violations,
        },
    }


def _json_text(audit: dict[str, Any]) -> str:
    return json.dumps(audit, indent=2, sort_keys=True) + "\n"


def _print_summary(audit: dict[str, Any]) -> None:
    source = audit["source"]
    print(
        f"maintained source: {source['files']} files, {source['physical_loc']} physical lines"
    )
    for kind in ("callables", "macros"):
        summary = audit["scope"][kind]
        bands = ", ".join(f"{band}={summary['bands'][band]}" for band in BANDS)
        print(f"{kind}: {summary['total']} scopes, max={summary['max']}, {bands}")
    for kind, violations in audit["violations"].items():
        for scope in violations:
            print(
                f"{scope['path']}:{scope['start_line']}: {scope['name'] or '<anonymous>'} "
                f"has complexity {scope['complexity']} ({kind})",
                file=sys.stderr,
            )
    print(
        "policy: 1-5 leave; 6-10 refactor when touched; 11-15 refactor now; >15 split"
    )


class _ComplexityTests(unittest.TestCase):
    def test_band_boundaries(self) -> None:
        self.assertEqual(
            [_band(value) for value in (1, 5, 6, 10, 11, 15, 16)],
            ["1-5", "1-5", "6-10", "6-10", "11-15", "11-15", ">15"],
        )

    def test_direct_analyzer_complexity_subtracts_nested_space(self) -> None:
        space = {
            "metrics": {"cyclomatic": {"sum": 8.0}},
            "spaces": [{"metrics": {"cyclomatic": {"sum": 3.0}}, "spaces": []}],
        }
        self.assertEqual(_direct_cyclomatic(space), 5)

    def test_gap_parser_handles_comments_strings_and_nested_functions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "sample.g"
            path.write_text(
                "Outer := function(x)\n"
                "  # if in a comment\n"
                '  if x and "if" <> "for" then\n'
                "    Inner := function(y)\n"
                "      for i in [1 .. y] do\n"
                "      od;\n"
                "    end;\n"
                "  elif x then\n"
                "  fi;\n"
                "end;\n",
                encoding="utf-8",
            )
            scopes = _gap_functions(path, root)
        self.assertEqual(
            [(scope["name"], scope["complexity"]) for scope in scopes],
            [("Outer", 4), ("Inner", 2)],
        )

    def test_gap_parser_rejects_unclosed_function(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "broken.g"
            path.write_text("broken := function()\n", encoding="utf-8")
            with self.assertRaises(RuntimeError):
                _gap_functions(path, root)

    def test_rust_macro_parser_counts_source_decisions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "sample.rs"
            path.write_text(
                "macro_rules! choose { ($value:expr) => { if $value && true { () } }; }\n"
                "fn main() { choose!(true); }\n",
                encoding="utf-8",
            )
            macros = _rust_macros(path, root)
        self.assertEqual(macros[0]["name"], "choose")
        self.assertEqual(macros[0]["complexity"], 3)

    def test_rust_tokens_skip_nested_comments_and_literals(self) -> None:
        source = (
            "fn sample() {\n"
            "  /* if\n"
            "     /* match && */\n"
            "     for */\n"
            "  let escaped = '\\n';\n"
            "  let quote = '\\\'';\n"
            "  let hex = '\\x69';\n"
            "  let unicode = '\\u{69}';\n"
            "  let raw = r#\"if match && for\"#;\n"
            "  let reference: &'a str = value;\n"
            "  if true {}\n"
            "}\n"
        )
        source_tokens = _source_tokens(source, "rust")
        token_texts = [token.text for token in source_tokens]
        self.assertEqual(token_texts.count("if"), 1)
        for decision in ("match", "for", "&&"):
            self.assertNotIn(decision, token_texts)
        self.assertEqual(
            _source_tokens("'\\n' '\\\\' '\\x69' '\\u{69}' '\\'' b'\\n'", "rust"),
            [],
        )
        self.assertEqual(
            [token.text for token in _source_tokens("&'a str + &'static str", "rust")],
            ["&", "'", "a", "str", "+", "&", "'", "static", "str"],
        )
        if_token = next(token for token in source_tokens if token.text == "if")
        self.assertEqual(if_token.line, 11)

    def test_source_files_include_gap_and_exclude_generated_directories(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative in ("a.rs", "b.py", "c.pyi", "d.g"):
                (root / relative).write_text("x\n", encoding="utf-8")
            (root / "target" / "generated.rs").parent.mkdir()
            (root / "target" / "generated.rs").write_text("x\n", encoding="utf-8")
            (root / "paper-example-private" / "draft.py").parent.mkdir()
            (root / "paper-example-private" / "draft.py").write_text(
                "x\n", encoding="utf-8"
            )
            found = {path.relative_to(root).as_posix() for path in _source_files(root)}
        self.assertEqual(found, {"a.rs", "b.py", "c.pyi", "d.g"})

    def test_analyzer_coverage_ignores_unmaintained_units_and_rejects_omissions(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            kept_rust = root / "kept.rs"
            kept_python = root / "kept.py"
            kept_rust.write_text("fn kept() {}\n", encoding="utf-8")
            kept_python.write_text("def kept(): ...\n", encoding="utf-8")
            generated = root / "target" / "generated.rs"
            generated.parent.mkdir()
            generated.write_text("fn generated() {}\n", encoding="utf-8")
            files = _source_files(root)
            units = [
                {"name": "kept.rs", "spaces": []},
                {"name": "target/generated.rs", "spaces": []},
            ]
            with patch(
                f"{__name__}._analysis", return_value=iter(units)
            ):
                with self.assertRaisesRegex(RuntimeError, "kept.py"):
                    _analyzer_scopes("unused", root, files)

            units.append({"name": "kept.py", "spaces": []})
            with patch(
                f"{__name__}._analysis", return_value=iter(units)
            ):
                self.assertEqual(_analyzer_scopes("unused", root, files), [])

    def test_json_output_is_deterministic(self) -> None:
        audit = {"scopes": {"callables": [], "macros": []}, "source": {"files": 0}}
        equivalent = {"source": {"files": 0}, "scopes": {"macros": [], "callables": []}}
        expected = '{\n  "scopes": {\n    "callables": [],\n    "macros": []\n  },\n  "source": {\n    "files": 0\n  }\n}\n'
        self.assertEqual(_json_text(audit), _json_text(equivalent))
        self.assertEqual(_json_text(audit), expected)


def _self_test() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(_ComplexityTests)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    return int(not result.wasSuccessful())


def _arguments(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run focused scanner tests instead of checking the repository",
    )
    parser.add_argument(
        "--json",
        metavar="PATH",
        help="write deterministic audit JSON to PATH, or '-' for stdout",
    )
    parser.add_argument(
        "--root", type=Path, default=ROOT, help="repository root to audit"
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _arguments(argv)
    if args.self_test:
        return _self_test()
    root = args.root.resolve()
    executable = _analyzer()
    audit = _audit(root, executable)
    if args.json == "-":
        sys.stdout.write(_json_text(audit))
    else:
        _print_summary(audit)
        if args.json:
            Path(args.json).write_text(_json_text(audit), encoding="utf-8")
    return int(bool(audit["violations"]["callables"] or audit["violations"]["macros"]))


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        OSError,
        RuntimeError,
        subprocess.CalledProcessError,
        json.JSONDecodeError,
        SyntaxError,
    ) as error:
        print(f"complexity check failed: {error}", file=sys.stderr)
        raise SystemExit(2) from None
