"""Test the portable derived atlas: export, replay, tamper rejection, and dispatch."""

import json
from pathlib import Path

import pytest

import auslander

F2 = auslander.PrimeField(2)
COMMITTED = (
    Path(__file__).resolve().parents[2]
    / "auslander/artifacts/research/derived-atlas-f2-n3.json"
)
SEAL = ',"fingerprint":"'


def _classify(vertices, control=None):
    family = auslander.connected_gentle_algebras(vertices, F2)
    return auslander.classify_derived(family, control=control)


def _reseal(document):
    """Canonical text of `document` with a fingerprint that matches its body."""
    text = json.dumps(document, separators=(",", ":"))
    body = text[: text.rindex(SEAL)]
    value = 0xCBF29CE484222325
    for byte in body.encode():
        value = ((value ^ byte) * 0x100000001B3) % 2**64
    return f'{body}{SEAL}{value:016x}"}}'


@pytest.fixture(scope="module")
def n2():
    return _classify(2)


@pytest.mark.parametrize("vertices", [1, 2])
def test_export_and_replay_round_trip(vertices, tmp_path):
    result = _classify(vertices)
    path = result.export(tmp_path / "atlas.json")
    replayed = auslander.verify_derived_atlas(path)

    assert (result.verification, result.fingerprint) == ("computed", None)
    assert replayed.verification == "replayed"
    assert replayed.fingerprint == result.to_artifact().fingerprint
    assert replayed.to_artifact().canonical_json == path.read_text()
    again = auslander.verify_derived_atlas(path.read_text())
    assert again.fingerprint == replayed.fingerprint


def test_replay_rebuilds_the_classification(n2):
    replayed = auslander.verify_derived_atlas(n2.to_artifact().canonical_json)

    assert [c.members for c in replayed.classes] == [c.members for c in n2.classes]
    assert len(replayed.separations) == len(n2.separations)
    assert replayed.status == n2.status
    assert replayed.verify()


def test_committed_atlas_replays():
    text = COMMITTED.read_text()
    artifact = auslander.DerivedAtlasArtifact(text)
    result = auslander.verify_derived_atlas(COMMITTED)

    assert (artifact.verification, artifact.has_valid_fingerprint) == ("unverified", True)
    assert result.verification == "replayed"
    assert result.fingerprint == artifact.fingerprint == json.loads(text)["fingerprint"]
    counts = (len(result.family), len(result.classes), len(result.unresolved))
    assert counts == (artifact.member_count, artifact.class_count, artifact.unresolved_count)
    assert result.status == artifact.status
    assert result.to_artifact().canonical_json == text
    assert "verification replayed" in repr(result)


def test_tampered_atlas_is_rejected(n2):
    text = n2.to_artifact().canonical_json
    document = json.loads(text)
    assert _reseal(document) == text

    digit = "1" if text[-3] == "0" else "0"
    flipped = text[:-3] + digit + text[-2:]
    assert not auslander.DerivedAtlasArtifact(flipped).has_valid_fingerprint
    with pytest.raises(ValueError, match="fingerprint does not match"):
        auslander.verify_derived_atlas(flipped)

    document["separations"][0]["left"][0] += 1
    classes = document["separations"][0]["classes"]
    message = f"separation of classes {classes[0]} and {classes[1]} does not hold"
    with pytest.raises(ValueError, match=message):
        auslander.DerivedAtlasArtifact(_reseal(document)).verify()

    with pytest.raises(ValueError, match="not canonical"):
        auslander.verify_derived_atlas(text.replace(":", ": ", 1))


def test_cancelled_replay_is_a_typed_cut(n2):
    control = auslander.ComputationControl()
    control.cancel()
    cut = auslander.verify_derived_atlas(n2.to_artifact().canonical_json, control)

    assert isinstance(cut, auslander.IncompleteArtifactVerification)
    assert (cut.kind, cut.completed) == ("cancelled", 0)


def test_cancelled_reading_has_no_artifact():
    control = auslander.ComputationControl()
    control.cancel()
    result = _classify(2, control)

    with pytest.raises(ValueError, match="was cancelled"):
        result.to_artifact()


def test_portable_dispatch_handles_the_derived_atlas(n2, tmp_path):
    path = n2.export(tmp_path / "atlas.json")
    text = path.read_text()
    fingerprint = n2.to_artifact().fingerprint

    assert auslander.verify_file(path).fingerprint == fingerprint
    assert auslander.verify(path).verification == "replayed"
    assert auslander.verify(auslander.DerivedAtlasArtifact(text)).fingerprint == fingerprint
    inspection = auslander.inspect(path)
    assert (inspection.kind, inspection.status) == ("derived_atlas", n2.status)
    assert (inspection.verification, inspection.fingerprint) == ("unverified", fingerprint)
    assert inspection.scope["classes"] == len(n2.classes)
    with pytest.raises(TypeError, match="limits do not apply to a derived atlas"):
        auslander.verify_file(path, auslander.CensusVerifyLimits())

    copy = auslander.checkpoint(auslander.DerivedAtlasArtifact(text), tmp_path / "copy.json")
    assert copy.read_text() == text


def test_session_stores_the_derived_atlas(n2, tmp_path):
    text = n2.to_artifact().canonical_json
    session = auslander.Session()
    session.add_artifact("atlas", text)
    session.save(tmp_path / "session.json")

    loaded = auslander.Session.load(tmp_path / "session.json")
    assert loaded.artifacts == {"atlas": text}
