"""Check computation and verification status in public explanations."""

import auslander

FIELD = auslander.PrimeField(5)


def _census(limits=None):
    algebra = auslander.Algebra.linear_an(2)
    return auslander.CensusCheckpoint.run(algebra, [1, 1], FIELD, limits=limits)


def _gentle_catalog():
    quiver = auslander.Quiver(4, [(0, 1), (1, 2), (3, 2)])
    algebra = auslander.Algebra(quiver, [[0, 1]], FIELD)
    return auslander.catalog(algebra)


def test_cut_checkpoint_reports_computation_cut_and_unverified_input():
    checkpoint = _census(auslander.CensusLimits(max_candidates=0))

    explanation = auslander.explain(checkpoint)

    assert checkpoint.status == "cut"
    assert explanation.status == "cut"
    assert explanation.verification == "unverified"
    assert explanation.unfinished == "candidate_limit"


def test_verified_cut_preserves_cut_status_and_reports_replay():
    verified = _census(auslander.CensusLimits(max_candidates=0)).verify()

    explanation = auslander.explain(verified)

    assert verified.status == "cut"
    assert explanation.status == "cut"
    assert explanation.verification == "replayed"


def test_verified_atlas_cut_preserves_cut_status_and_reports_replay():
    atlas = _gentle_catalog().atlas(3)
    artifact = atlas.export(
        [1, 1, 1, 1], auslander.MultiplicityLimits(max_solutions=1)
    )
    verified = auslander.verify_catalog_atlas_artifact(artifact.canonical_json)

    explanation = auslander.explain(verified)

    assert verified.status == "cut"
    assert explanation.status == "cut"
    assert explanation.verification == "replayed"
    assert auslander.explain(verified.enumeration_status).status == "cut"
    assert explanation.unfinished == "solution_limit"


def test_coordinate_progress_does_not_infer_completion_from_verify_method():
    catalog = auslander.Algebra.linear_an(2).catalog(FIELD)
    module = catalog.entries[0]
    result = catalog.coordinates(
        module,
        limits=auslander.CatalogCoordinateLimits(max_work_units=0),
    )

    explanation = auslander.explain(result.progress)

    assert result.status == "cut"
    assert explanation.status == "value"
    assert explanation.verification == "computed"


def test_complete_checkpoint_remains_unverified_until_replay():
    checkpoint = _census()

    explanation = auslander.explain(checkpoint)

    assert checkpoint.status == "complete"
    assert explanation.status == "complete"
    assert explanation.verification == "unverified"


def test_undetermined_tilting_result_keeps_unknown_status():
    algebra = auslander.Algebra.dual_numbers()
    module = algebra.simple(0, field=FIELD)
    result = auslander.ClassicalTiltingModule.classify(
        module, auslander.TiltingLimits(2, 3)
    )

    explanation = auslander.explain(result)

    assert result.is_tilting is None
    assert explanation.status == "undetermined"
    assert explanation.verification == "unverified"
    assert explanation.unfinished == "projective_dimension"


def test_derived_and_resolution_endings_use_typed_statuses():
    algebra = auslander.Algebra.an_with_relations(3, [(0, 2)])
    source = auslander.BoundedComplex(0, [algebra.simple(0, field=FIELD)], [])
    target = auslander.BoundedComplex(0, [algebra.simple(2, field=FIELD)], [])
    derived = source.derived_hom(target, auslander.DerivedHomLimits(max_degrees=1))
    resolution = algebra.simple(0, field=FIELD).resolve(0)

    assert auslander.explain(derived).status == "cut"
    assert auslander.explain(resolution).status == "cut"
    assert auslander.explain(resolution.projective_dimension).status == "at_least"
