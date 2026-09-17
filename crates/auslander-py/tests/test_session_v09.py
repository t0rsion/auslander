"""Session field ownership and schema-dispatched artifact verification."""

from __future__ import annotations

import json
from pathlib import Path

import auslander
import pytest
from auslander.session import verify_file_text

PRESENTATION_F2 = """
field 2
vertices 0 1
arrows a:0->1
"""
PRESENTATION_F5 = PRESENTATION_F2.replace("field 2", "field 5")


def test_session_replays_modules_with_each_algebra_field(tmp_path: Path) -> None:
    session = auslander.Session(2)
    session.algebra("A2", PRESENTATION_F2)
    session.algebra("A5", PRESENTATION_F5)
    module2 = session.module("M2", "A2", [1, 1], [[[4]]])
    module5 = session.module("M5", "A5", [1, 1], [[[4]]])

    assert module2.maps == [[[0]]]
    assert module5.maps == [[[4]]]
    path = tmp_path / "mixed-fields.json"
    session.save(path)

    document = json.loads(path.read_text(encoding="utf-8"))
    assert document["schema"] == "auslander-session-v2"
    assert document["recipes"]["M2"]["field"] == 2
    assert document["recipes"]["M5"]["field"] == 5

    loaded = auslander.Session.load(path)
    assert loaded["M2"].maps == [[[0]]]
    assert loaded["M5"].maps == [[[4]]]


def test_bound_field_free_algebra_keeps_the_session_default_field() -> None:
    session = auslander.Session(2)
    field_free = auslander.Algebra.linear_an(2)
    session.bind("A", field_free)
    session.algebra("B", PRESENTATION_F5)

    module = session.module("M", "A", [1, 1], [[[4]]])
    assert module.maps == [[[0]]]
    assert session.field.p == 2


def test_session_save_keeps_its_initial_default_field(tmp_path: Path) -> None:
    session = auslander.Session(2)
    session.algebra("A2", PRESENTATION_F2)
    session.algebra("A5", PRESENTATION_F5)
    path = tmp_path / "default-field.json"
    session.save(path)
    assert json.loads(path.read_text(encoding="utf-8"))["field"] == 2


def test_save_rejects_live_algebra_dependencies_without_touching_destination(
    tmp_path: Path,
) -> None:
    session = auslander.Session(2)
    session.bind("A", auslander.Algebra.linear_an(2))
    session.module("M", "A", [1, 1], [[[0]]])
    path = tmp_path / "session.json"
    path.write_text("keep this file", encoding="utf-8")

    with pytest.raises(ValueError, match="no persisted algebra recipe.*session.algebra"):
        session.save(path)
    assert path.read_text(encoding="utf-8") == "keep this file"


def test_module_rejects_a_named_non_algebra_value() -> None:
    session = auslander.Session(2)
    session.bind("value", object())

    with pytest.raises(ValueError, match="not bound to an Algebra"):
        session.module("M", "value", [1], [[]])


def _session_with_a2() -> auslander.Session:
    session = auslander.Session(2)
    session.algebra("A", PRESENTATION_F2)
    return session


def test_session_reuses_an_identical_algebra_recipe() -> None:
    session = _session_with_a2()
    assert session.algebra("A", PRESENTATION_F2) is session["A"]


def test_session_rejects_a_changed_algebra_recipe() -> None:
    session = _session_with_a2()
    with pytest.raises(ValueError, match="different recipe"):
        session.algebra("A", PRESENTATION_F5)


def test_session_rejects_a_module_using_an_algebra_name() -> None:
    session = _session_with_a2()
    with pytest.raises(ValueError, match="already bound"):
        session.module("A", "A", [1, 1], [[[0]]])


def test_session_rejects_a_live_binding_using_an_algebra_name() -> None:
    session = _session_with_a2()
    with pytest.raises(ValueError, match="already bound"):
        session.bind("A", object())


def test_session_rejects_an_algebra_using_a_module_name() -> None:
    session = _session_with_a2()
    session.module("M", "A", [1, 1], [[[0]]])
    with pytest.raises(ValueError, match="already bound"):
        session.algebra("M", PRESENTATION_F2)


def test_session_schema_v1_is_rejected_explicitly(tmp_path: Path) -> None:
    document = {
        "schema": "auslander-session-v1",
        "field": 2,
        "recipes": {},
        "artifacts": {},
        "display": {"max_chars": 12000, "max_items": 200},
    }
    path = tmp_path / "old-session.json"
    path.write_text(json.dumps(document), encoding="utf-8")
    with pytest.raises(ValueError, match="unsupported session schema"):
        auslander.Session.load(path)


def test_session_rejects_boolean_field_and_workflow_rejects_unhashable_schema(
    tmp_path: Path,
) -> None:
    document = {
        "schema": "auslander-session-v2",
        "field": True,
        "recipes": {},
        "artifacts": {},
        "display": {},
    }
    path = tmp_path / "boolean-field.json"
    path.write_text(json.dumps(document), encoding="utf-8")
    with pytest.raises(ValueError, match="field must be an integer"):
        auslander.Session.load(path)
    with pytest.raises(ValueError, match="scalar values"):
        verify_file_text('{"schema":[],"kind":"census-v1"}')


def _portable_values() -> dict[str, str]:
    field = auslander.PrimeField(2)
    algebra = auslander.Algebra.linear_an(2, field)
    census = auslander.run_census(
        algebra,
        [1, 1],
        limits=auslander.CensusLimits(max_candidates=100, max_work_units=1000),
    )
    verified_census = census.verify()
    stream = auslander.start_homological_stream(
        verified_census,
        1,
        auslander.HomologicalStreamConfig(max_live_sources=2),
    )
    homological = stream.checkpoint
    while homological.status == "active":
        homological = stream.advance()
    theorem = auslander.build_self_ext_locus_artifact(homological.verify(), 1, 1)
    definition = auslander.define(PRESENTATION_F2, [1, 1])
    return {
        "derived": auslander.build_derived_artifact(algebra, [("left", 1)]),
        "census": census.canonical_json,
        "homological": homological.canonical_json,
        "theorem": theorem.canonical_json,
        "workflow": definition.canonical_json,
    }


@pytest.mark.parametrize(
    ("kind", "class_name"),
    [
        ("derived", "VerifiedDerivedArtifact"),
        ("census", "VerifiedCensusCheckpoint"),
        ("homological", "VerifiedHomologicalCheckpoint"),
        ("theorem", "VerifiedSelfExtLocusArtifact"),
        ("workflow", "WorkflowDefinition"),
    ],
)
def test_verify_file_dispatches_all_portable_workflow_kinds(
    tmp_path: Path,
    kind: str,
    class_name: str,
) -> None:
    text = _portable_values()[kind]
    path = tmp_path / f"{kind}.json"
    path.write_text(text, encoding="utf-8")
    result = auslander.verify_file(path)
    assert isinstance(result, getattr(auslander, class_name))
    assert result.canonical_json == text


def test_session_artifacts_round_trip_after_dispatch(tmp_path: Path) -> None:
    session = auslander.Session(2)
    values = _portable_values()
    for kind, text in values.items():
        session.add_artifact(kind, text)
    session.add_artifact("A2-left", values["workflow"])
    path = tmp_path / "artifacts.json"
    session.save(path)

    loaded = auslander.Session.load(path)
    assert loaded.artifacts == {**values, "A2-left": values["workflow"]}

    with pytest.raises(ValueError, match="unsupported portable value schema"):
        verify_file_text('{"schema":"auslander-computation-v0"}')
