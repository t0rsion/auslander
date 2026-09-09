/// Mismatch descriptions from comparing the library against a validated
/// document. Every fixture's algebra is rebuilt from its recorded
/// presentation; a construction failure is a mismatch, not a skip. The
/// fixture set itself is pinned by the v6 manifest and `V8_EXTRA_FIXTURES`.
pub(crate) fn compare(doc: &Document) -> Vec<String> {
    compare_at(doc, SttDepth::Shape)
}

pub(crate) fn in_fixture_manifest(family: &str, case: &str, v8: bool) -> bool {
    FIXTURE_MANIFEST
        .iter()
        .chain(V8_EXTRA_FIXTURES.iter().filter(|_| v8))
        .any(|&(manifest_family, manifest_case)| manifest_family == family && manifest_case == case)
}

pub(crate) fn compare_required_fixtures(mismatches: &mut Vec<String>, doc: &Document, v8: bool) {
    for &(family, case) in FIXTURE_MANIFEST
        .iter()
        .chain(V8_EXTRA_FIXTURES.iter().filter(|_| v8))
    {
        if !doc
            .fixtures
            .iter()
            .any(|fx| fx.family == family && fx.case == case)
        {
            mismatches.push(format!("{family}/{case}: missing from oracle file"));
        }
    }
}

pub(crate) fn compare_document_fixture(
    mismatches: &mut Vec<String>,
    doc: &Document,
    fixture: &Fixture,
    depth: SttDepth,
    v8: bool,
) {
    let ctx = format!("{}/{}", fixture.family, fixture.case);
    if !in_fixture_manifest(&fixture.family, &fixture.case, v8) {
        mismatches.push(format!("{ctx}: not in the fixture manifest"));
    }
    match computed_for(fixture, doc.left_convention) {
        Ok(ours) => compare_fixture(mismatches, &ctx, fixture, &ours),
        Err(error) => mismatches.push(format!("{ctx}: {error}")),
    }
    if !doc.left_convention {
        compare_classical_tilting(mismatches, &ctx, fixture);
    }
    if let Some(stt) = &fixture.stt
        && !doc.left_convention
    {
        let enumerate = matches!(stt.indecomposables, Closure::Closed { .. });
        match stt_for(fixture, enumerate) {
            Ok(ours) => compare_stt(mismatches, &ctx, fixture, &ours, depth),
            Err(error) => mismatches.push(format!("{ctx}: {error}")),
        }
    }
}

pub(crate) fn compare_document_fixtures(
    mismatches: &mut Vec<String>,
    doc: &Document,
    v8: bool,
    depth: SttDepth,
) {
    for fixture in &doc.fixtures {
        compare_document_fixture(mismatches, doc, fixture, depth, v8);
    }
}

pub(crate) fn compare_at(doc: &Document, depth: SttDepth) -> Vec<String> {
    let mut mismatches = Vec::new();
    let v8 = doc.fixtures.iter().all(|fx| fx.stt.is_some());
    compare_required_fixtures(&mut mismatches, doc, v8);
    compare_document_fixtures(&mut mismatches, doc, v8, depth);
    mismatches
}
