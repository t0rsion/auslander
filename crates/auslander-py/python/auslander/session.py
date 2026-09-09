"""Named live values and checked recipe persistence."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .parser import parse_presentation


_SCHEMA = "auslander-session-v1"


class Session:
    """Own named core values, reconstructible recipes, and display settings."""

    def __init__(self, field: int = 2) -> None:
        from ._core import PrimeField

        self.field = PrimeField(field)
        self._values: dict[str, Any] = {}
        self._recipes: dict[str, dict[str, Any]] = {}
        self.artifacts: dict[str, str] = {}
        self.display: dict[str, int] = {"max_chars": 12000, "max_items": 200}

    @property
    def names(self) -> tuple[str, ...]:
        """The stored names in sorted order."""
        return tuple(sorted(self._values))

    def __getitem__(self, name: str) -> Any:
        return self._values[name]

    def bind(self, name: str, value: Any) -> Any:
        """Bind a live value that is not persisted as a constructor recipe."""
        if not name.isidentifier():
            raise ValueError("a session name must be a Python identifier")
        self._values[name] = value
        self._recipes.pop(name, None)
        return value

    def algebra(self, name: str, presentation: str) -> Any:
        """Parse, build, and name one checked algebra presentation."""
        if name in self._values:
            return self._values[name]
        parsed = parse_presentation(presentation)
        value = parsed.build()
        from ._core import PrimeField

        self.field = PrimeField(parsed.field)
        self._values[name] = value
        self._recipes[name] = {"kind": "algebra", "text": presentation}
        return value

    def module(
        self,
        name: str,
        algebra_name: str,
        dims: list[int],
        maps: list[list[list[int]]],
    ) -> Any:
        """Build and name one module over a named session algebra."""
        if name in self._values:
            return self._values[name]
        algebra = self._values[algebra_name]
        value = algebra.module(self.field, dims, maps)
        self._values[name] = value
        self._recipes[name] = {
            "kind": "module",
            "algebra": algebra_name,
            "dims": dims,
            "maps": maps,
        }
        return value

    def add_artifact(self, name: str, text: str) -> None:
        """Store canonical artifact text after independent verification."""
        result = verify_file_text(text)
        self.artifacts[name] = result.canonical_json

    def save(self, path: str | Path) -> None:
        """Write recipes and canonical artifacts, never a Python object graph."""
        document = {
            "schema": _SCHEMA,
            "field": self.field.p,
            "recipes": self._recipes,
            "artifacts": self.artifacts,
            "display": self.display,
        }
        Path(path).write_text(
            json.dumps(document, sort_keys=True, separators=(",", ":")),
            encoding="utf-8",
        )

    @classmethod
    def load(cls, path: str | Path) -> "Session":
        """Rebuild every value through checked public constructors."""
        document = json.loads(Path(path).read_text(encoding="utf-8"))
        _validate_document(document)
        session = cls(document["field"])
        _load_recipes(session, document["recipes"])
        _load_artifacts(session, document["artifacts"])
        _load_display(session, document["display"])
        return session


def _validate_document(document: Any) -> None:
    expected = {"schema", "field", "recipes", "artifacts", "display"}
    if not isinstance(document, dict) or set(document) != expected:
        raise ValueError("session document has missing or unknown fields")
    if document["schema"] != _SCHEMA:
        raise ValueError("unsupported session schema")


def _require_mapping(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"session {label} must be an object")
    return value


def _load_recipe(session: Session, name: str, recipe: dict[str, Any]) -> bool:
    if recipe.get("kind") == "algebra":
        session.algebra(name, recipe["text"])
        return True
    if recipe.get("kind") == "module" and recipe.get("algebra") in session._values:
        session.module(name, recipe["algebra"], recipe["dims"], recipe["maps"])
        return True
    return False


def _load_recipes(session: Session, recipes: Any) -> None:
    pending = dict(_require_mapping(recipes, "recipes"))
    while pending:
        progressed = False
        for name, recipe in list(pending.items()):
            if _load_recipe(session, name, recipe):
                del pending[name]
                progressed = True
        if not progressed:
            raise ValueError("session recipes contain an unknown kind or missing dependency")


def _load_artifacts(session: Session, artifacts: Any) -> None:
    for name, text in _require_mapping(artifacts, "artifacts").items():
        session.add_artifact(name, text)


def _load_display(session: Session, display: Any) -> None:
    session.display = {key: int(value) for key, value in _require_mapping(display, "display").items()}


def verify_file_text(text: str) -> Any:
    """Verify artifact text through the extension's independent verifier."""
    from ._core import verify_derived_artifact

    return verify_derived_artifact(text)


def verify_file(path: str | Path) -> Any:
    """Verify one local artifact and return its typed core result."""
    return verify_file_text(Path(path).read_text(encoding="utf-8"))
