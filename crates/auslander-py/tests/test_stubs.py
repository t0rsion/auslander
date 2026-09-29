"""Check the type stubs against the compiled module."""

import ast
import builtins
from pathlib import Path

import pytest

import auslander
from auslander import _core

PACKAGE = Path(auslander.__file__).parent


def _stub(name):
    return ast.parse((PACKAGE / name).read_text())


def _declared_names():
    names = set()
    for path in PACKAGE.glob("_*.pyi"):
        for node in _stub(path.name).body:
            if isinstance(node, (ast.ClassDef, ast.FunctionDef)):
                names.add(node.name)
            elif isinstance(node, ast.AnnAssign):
                names.add(node.target.id)
    return names


def test_every_public_core_name_has_a_stub():
    public = {name for name in dir(_core) if not name.startswith("_")}

    assert public - _declared_names() == set()


def _members(node):
    return [
        item.name
        for item in node.body
        if isinstance(item, ast.FunctionDef) and item.name != "__init__"
    ]


@pytest.mark.parametrize(
    "node",
    [node for node in _stub("_derived.pyi").body if isinstance(node, ast.ClassDef)],
    ids=lambda node: node.name,
)
def test_derived_stub_members_exist_at_runtime(node):
    runtime = getattr(auslander, node.name)

    assert [name for name in _members(node) if not hasattr(runtime, name)] == []


def test_exception_stubs_name_the_runtime_bases():
    for node in _stub("_exceptions.pyi").body:
        base = node.bases[0].id
        expected = getattr(builtins, base, None) or getattr(auslander, base)
        assert getattr(auslander, node.name).__bases__ == (expected,), node.name
