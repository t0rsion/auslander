"""Named live values and checked recipe persistence."""

from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

from .checkpoint import _write_canonical_json
from .parser import parse_presentation

_SCHEMA = "auslander-session-v2"
_MISSING = object()


class Session:
    """Own named core values, reconstructible recipes, and display settings."""

    def __init__(self, field: int = 2) -> None:
        from ._core import PrimeField

        self.field = PrimeField(field)
        self._values: dict[str, Any] = {}
        self._recipes: dict[str, dict[str, Any]] = {}
        self._algebra_fields: dict[str, int] = {}
        self.artifacts: dict[str, str] = {}
        self.display: dict[str, int] = {"max_chars": 12000, "max_items": 200}

    @property
    def names(self) -> tuple[str, ...]:
        """Return stored value names in sorted order."""
        return tuple(sorted(self._values))

    def __getitem__(self, name: str) -> Any:
        return self._values[name]

    def bind(self, name: str, value: Any) -> Any:
        """Bind one live value that has no persisted constructor recipe."""
        _name(name)
        if name in self._values:
            raise ValueError(f"session name {name!r} is already bound")
        self._values[name] = value
        field = _value_field(value)
        if field is not None:
            self._algebra_fields[name] = field
        elif _is_algebra(value):
            self._algebra_fields[name] = self.field.p
        return value

    def algebra(self, name: str, presentation: str) -> Any:
        """Parse, build, and name one checked algebra presentation."""
        _name(name)
        parsed = parse_presentation(presentation)
        recipe = {
            "kind": "algebra",
            "field": parsed.field,
            "text": presentation,
        }
        existing = self._reuse(name, recipe)
        if existing is not _MISSING:
            return existing
        value = parsed.build()
        self._values[name] = value
        self._algebra_fields[name] = parsed.field
        self._recipes[name] = recipe
        return value

    def module(
        self,
        name: str,
        algebra_name: str,
        dims: list[int],
        maps: list[list[list[int]]],
    ) -> Any:
        """Build and name one module over a named session algebra."""
        _name(name)
        _name(algebra_name)
        algebra = self._values.get(algebra_name, _MISSING)
        if algebra is _MISSING:
            raise ValueError(f"unknown session algebra {algebra_name!r}")
        if not _is_algebra(algebra):
            raise ValueError(f"session name {algebra_name!r} is not bound to an Algebra")
        field = self._algebra_field(algebra_name, algebra)
        recipe = {
            "kind": "module",
            "algebra": algebra_name,
            "dims": deepcopy(dims),
            "field": field,
            "maps": deepcopy(maps),
        }
        existing = self._reuse(name, recipe)
        if existing is not _MISSING:
            return existing
        from ._core import PrimeField

        value = algebra.module(dims, maps, field=PrimeField(field))
        self._values[name] = value
        self._recipes[name] = recipe
        return value

    def add_artifact(self, name: str, text: str) -> None:
        """Verify and store one canonical portable value by name."""
        _artifact_name(name)
        result = verify_file_text(text)
        canonical = _canonical_text(result)
        previous = self.artifacts.get(name, _MISSING)
        if previous is not _MISSING and previous != canonical:
            raise ValueError(f"session artifact name {name!r} is already bound")
        self.artifacts[name] = canonical

    def save(self, path: str | Path) -> None:
        """Write recipes and canonical artifacts, never a Python object graph."""
        self._validate_persisted_dependencies()
        document = {
            "schema": _SCHEMA,
            "field": self.field.p,
            "recipes": self._recipes,
            "artifacts": self.artifacts,
            "display": self.display,
        }
        _write_canonical_json(
            path,
            json.dumps(
                document, allow_nan=False, sort_keys=True, separators=(",", ":")
            ),
        )

    @classmethod
    def load(cls, path: str | Path) -> Session:
        """Rebuild every stored value through checked public constructors."""
        document = json.loads(
            Path(path).read_text(encoding="utf-8"),
            object_pairs_hook=_pairs,
            parse_constant=_reject_constant,
        )
        _validate_document(document)
        session = cls(document["field"])
        _load_recipes(session, document["recipes"])
        _load_artifacts(session, document["artifacts"])
        _load_display(session, document["display"])
        return session

    def _reuse(self, name: str, recipe: dict[str, Any]) -> Any:
        existing = self._values.get(name, _MISSING)
        if existing is _MISSING:
            return _MISSING
        previous = self._recipes.get(name)
        if previous == recipe:
            return existing
        if previous is None:
            raise ValueError(f"session name {name!r} is already bound")
        if previous.get("kind") != recipe.get("kind"):
            raise ValueError(
                f"session name {name!r} is already bound to a different value kind"
            )
        raise ValueError(f"session name {name!r} has a different recipe")

    def _algebra_field(self, name: str, algebra: Any) -> int:
        field = self._algebra_fields.get(name)
        if field is None:
            field = _value_field(algebra)
        if field is None:
            field = self.field.p
        self._algebra_fields[name] = field
        return field

    def _validate_persisted_dependencies(self) -> None:
        for name, recipe in self._recipes.items():
            if not isinstance(recipe, dict) or recipe.get("kind") != "module":
                continue
            algebra_name = recipe.get("algebra")
            algebra_recipe = (
                self._recipes.get(algebra_name)
                if isinstance(algebra_name, str)
                else None
            )
            if (
                not isinstance(algebra_recipe, dict)
                or algebra_recipe.get("kind") != "algebra"
            ):
                raise ValueError(
                    f"cannot save session: module recipe {name!r} references "
                    f"{algebra_name!r}, which has no persisted algebra recipe; "
                    "use session.algebra(...)"
                )


def _name(name: str) -> None:
    if not isinstance(name, str) or not name.isidentifier():
        raise ValueError("a session name must be a Python identifier")


def _artifact_name(name: str) -> None:
    if not isinstance(name, str) or not name:
        raise ValueError("an artifact name must be nonempty text")


def _value_field(value: Any) -> int | None:
    field = getattr(value, "field", None)
    if field is None:
        return None
    modulus = getattr(field, "p", field)
    if isinstance(modulus, bool) or not isinstance(modulus, int):
        return None
    return modulus


def _is_algebra(value: Any) -> bool:
    from ._core import Algebra

    return isinstance(value, Algebra)


def _canonical_text(value: Any) -> str:
    canonical = getattr(value, "canonical_json", None)
    if not isinstance(canonical, str):
        kind = getattr(value, "kind", "portable value")
        raise ValueError(f"{kind} verification did not complete")
    return canonical


def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate session field {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise ValueError(f"JSON constant {value!r} is not allowed")


def _validate_document(document: Any) -> None:
    if not isinstance(document, dict):
        raise ValueError("session document must be an object")
    if document.get("schema") != _SCHEMA:
        raise ValueError("unsupported session schema")
    expected = {"schema", "field", "recipes", "artifacts", "display"}
    if set(document) != expected:
        raise ValueError("session document has missing or unknown fields")
    if isinstance(document["field"], bool) or not isinstance(document["field"], int):
        raise ValueError("session field must be an integer")


def _require_mapping(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"session {label} must be an object")
    return value


def _recipe_fields(recipe: Any, name: str, expected: set[str]) -> dict[str, Any]:
    value = _require_mapping(recipe, f"recipe {name!r}")
    if set(value) != expected:
        raise ValueError(f"session recipe {name!r} has missing or unknown fields")
    return value


def _load_recipe(session: Session, name: str, recipe: Any) -> bool:
    _name(name)
    kind = recipe.get("kind") if isinstance(recipe, dict) else None
    if kind == "algebra":
        _load_algebra_recipe(session, name, recipe)
        return True
    if kind == "module":
        return _load_module_recipe(session, name, recipe)
    raise ValueError(f"session recipe {name!r} has unknown kind")


def _load_algebra_recipe(session: Session, name: str, recipe: Any) -> None:
    value = _recipe_fields(recipe, name, {"kind", "field", "text"})
    field = _recipe_integer(value["field"], name)
    parsed = parse_presentation(value["text"])
    if parsed.field != field:
        raise ValueError(
            f"session recipe {name!r} field does not match its presentation"
        )
    session.algebra(name, value["text"])


def _load_module_recipe(session: Session, name: str, recipe: Any) -> bool:
    value = _recipe_fields(recipe, name, {"kind", "algebra", "dims", "field", "maps"})
    algebra_name = value["algebra"]
    _name(algebra_name)
    field = _recipe_integer(value["field"], name)
    if algebra_name not in session._values:
        return False
    expected = session._algebra_field(algebra_name, session._values[algebra_name])
    if field != expected:
        raise ValueError(f"session recipe {name!r} field does not match its algebra")
    session.module(name, algebra_name, value["dims"], value["maps"])
    return True


def _recipe_integer(value: Any, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"session recipe {name!r}.field must be an integer")
    return value


def _load_recipes(session: Session, recipes: Any) -> None:
    pending = dict(_require_mapping(recipes, "recipes"))
    while pending:
        progressed = False
        for name, recipe in list(pending.items()):
            if _load_recipe(session, name, recipe):
                del pending[name]
                progressed = True
        if not progressed:
            raise ValueError("session recipes contain a missing algebra dependency")


def _load_artifacts(session: Session, artifacts: Any) -> None:
    for name, text in _require_mapping(artifacts, "artifacts").items():
        session.add_artifact(name, text)


def _load_display(session: Session, display: Any) -> None:
    values = _require_mapping(display, "display")
    session.display = {}
    for key, value in values.items():
        if (
            not isinstance(key, str)
            or isinstance(value, bool)
            or not isinstance(value, int)
        ):
            raise ValueError("session display values must be integers")
        session.display[key] = value


def verify_file_text(text: str, limits: Any | None = None) -> Any:
    """Verify one bounded portable value through the workflow dispatcher."""
    from .workflow_io import verify_file_text as _verify_file_text

    return _verify_file_text(text, limits)


def verify_file(path: str | Path, limits: Any | None = None) -> Any:
    """Read and verify one bounded portable value through the workflow dispatcher."""
    from .workflow_io import verify_file as _verify_file

    return _verify_file(path, limits)
