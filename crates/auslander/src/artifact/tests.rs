use super::*;
use crate::algebra::linear_an;
use crate::batch_stream::{
    HomologicalStreamBudget, HomologicalStreamConfig, HomologicalStreamStep,
    homological_stream_from_census,
};
use crate::census::{Census, CensusLimits, CensusPortable};
use crate::field::PrimeField;
use crate::theorem_artifact::SelfExtLocusArtifact;

const THEOREM: &str =
    include_str!("../../artifacts/research/commutative-square-f2-d1111-self-ext-1-3.json");
const ATLAS: &str = include_str!("../../artifacts/research/derived-atlas-f2-n3.json");

fn census_portable(limits: CensusLimits) -> CensusPortable {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let outcome = Census::new(&algebra, vec![1, 1])
        .unwrap()
        .run_with(limits, None);
    CensusPortable::from_outcome(&outcome).unwrap()
}

fn census_text(limits: CensusLimits) -> String {
    census_portable(limits).to_canonical_json()
}

fn verified(text: &str) -> VerifiedArtifact {
    match verify_artifact(text, &ArtifactLimits::default(), &ComputationControl::new()).unwrap() {
        ArtifactVerification::Verified(value) => *value,
        ArtifactVerification::Stopped { cut, .. } => panic!("verification stopped: {cut:?}"),
    }
}

#[test]
fn every_registered_header_selects_its_kind() {
    for kind in ArtifactKind::ALL {
        let text = match kind.payload_kind() {
            Some(payload) => format!(
                "{{\"schema\":\"{}\",\"kind\":\"{payload}\"}}",
                kind.schema()
            ),
            None => format!("{{\"schema\":\"{}\"}}", kind.schema()),
        };
        assert_eq!(read_kind(&text).unwrap(), kind, "{text}");
    }
}

#[test]
fn unknown_and_obsolete_headers_name_what_was_found() {
    let cases = [
        (
            r#"{"schema":"auslander-computation-v0"}"#,
            "\"auslander-computation-v0\"",
        ),
        (
            r#"{"schema":"auslander-computation-v1","kind":"census-v9"}"#,
            "\"census-v9\"",
        ),
        (
            r#"{"schema":"auslander-computation-v1","kind":"homological-self-pair-stream-v1"}"#,
            "current kind \"homological-self-pair-stream-v2\"",
        ),
        (r#"{"schema":[]}"#, "at byte 10"),
        (r#"{"kind":"census-v1"}"#, "expected key \"schema\""),
    ];
    for (text, expected) in cases {
        let error = read_kind(text).unwrap_err();
        assert!(error.kind().is_none());
        assert!(
            error.to_string().contains(expected),
            "{error} lacks {expected}"
        );
    }
    assert!(matches!(
        read_kind(cases[2].0),
        Err(PortableArtifactError::ObsoleteKind {
            current: ArtifactKind::HomologicalStream,
            ..
        })
    ));
}

/// Replay of `auslander-derived-v1` kept unreduced cones, so both the header
/// dispatch and the derived parser name `auslander-derived-v2` instead.
#[test]
fn the_unreduced_derived_schema_is_obsolete() {
    let text = r#"{"schema":"auslander-derived-v1","source":[]}"#;
    let error = read_kind(text).unwrap_err();
    assert!(matches!(
        &error,
        PortableArtifactError::ObsoleteKind {
            found,
            current: ArtifactKind::DerivedEquivalence,
        } if found == "auslander-derived-v1"
    ));
    assert!(
        error
            .to_string()
            .contains("current kind \"auslander-derived-v2\"")
    );
    let parsed = crate::derived_artifact::DerivedArtifact::from_json(
        text,
        crate::derived_artifact::ArtifactParseLimits::default(),
    );
    assert!(matches!(
        parsed,
        Err(crate::derived_artifact::ArtifactError::ObsoleteSchema {
            current: "auslander-derived-v2",
            ..
        })
    ));
}

#[test]
fn committed_theorem_artifact_verifies_through_the_dispatch() {
    let value = verified(THEOREM);
    let report = value.report();
    assert_eq!(value.status(), ArtifactStatus::Verified);
    assert_eq!(report.kind(), ArtifactKind::SelfExtLocus);
    assert_eq!(report.canonical_json(), THEOREM.trim_end());
    let inspected = inspect_artifact(THEOREM.trim_end(), &ArtifactLimits::default()).unwrap();
    assert_eq!(&inspected, report);
    assert!(matches!(
        value.value(),
        VerifiedArtifactValue::SelfExtLocus(_)
    ));
}

/// Every connected gentle algebra with at most 3 vertices over `F_2`.
#[test]
fn committed_derived_atlas_verifies_through_the_dispatch() {
    let value = verified(ATLAS);
    let report = value.report();
    assert_eq!(value.status(), ArtifactStatus::Verified);
    assert_eq!(report.kind(), ArtifactKind::DerivedAtlas);
    assert_eq!(report.canonical_json(), ATLAS);
    let labels: Vec<_> = report.summary().iter().map(|(label, _)| *label).collect();
    let expected = [
        "field",
        "members",
        "classes",
        "merges",
        "separations",
        "unresolved",
        "status",
    ];
    assert_eq!(labels, expected);
    assert_eq!(report.summary()[6].1, "complete");
    let inspected = inspect_artifact(ATLAS, &ArtifactLimits::default()).unwrap();
    assert_eq!(&inspected, report);
    let VerifiedArtifactValue::DerivedAtlas(atlas) = value.value() else {
        panic!("the dispatch selects the atlas verifier");
    };
    assert!(atlas.classification().verify());
    let control = ComputationControl::new();
    control.cancel();
    let stopped = verify_artifact(ATLAS, &ArtifactLimits::default(), &control).unwrap();
    assert!(matches!(
        stopped,
        ArtifactVerification::Stopped {
            kind: ArtifactKind::DerivedAtlas,
            cut: ArtifactVerificationCut::Cancelled {
                completed_mutations: 0
            },
        }
    ));
}

/// Replay checks each walk record only against the merges. Rerunning the
/// classification of the committed family under its stored limits, with
/// discovery, writes the committed bytes again.
#[test]
fn the_committed_derived_atlas_is_reproduced_from_scratch() {
    let value = verified(ATLAS);
    let VerifiedArtifactValue::DerivedAtlas(atlas) = value.value() else {
        panic!("the dispatch selects the atlas verifier");
    };
    let replayed = atlas.classification();
    let control = ComputationControl::new();
    let fresh = crate::derived_classification::classify_derived(
        replayed.family(),
        replayed.limits(),
        &control,
    )
    .unwrap();
    assert_eq!(fresh.to_artifact().unwrap().to_canonical_json(), ATLAS);
}

#[test]
fn a_cut_census_verifies_as_a_cut_prefix() {
    let complete = verified(&census_text(CensusLimits::default()));
    assert_eq!(complete.status(), ArtifactStatus::Verified);
    let cut = verified(&census_text(CensusLimits {
        max_candidates: 3,
        ..CensusLimits::default()
    }));
    assert_eq!(cut.status(), ArtifactStatus::VerifiedCut);
    assert_eq!(cut.report().kind(), ArtifactKind::Census);
    assert!(!cut.report().is_complete());
}

#[test]
fn a_tampered_value_is_rejected_by_its_own_verifier() {
    let text = census_text(CensusLimits::default());
    let position = text.find("\"cursor\":").unwrap() + "\"cursor\":".len();
    let mut tampered = text.into_bytes();
    tampered[position] = if tampered[position] == b'1' {
        b'2'
    } else {
        b'1'
    };
    let tampered = String::from_utf8(tampered).unwrap();
    let limits = ArtifactLimits::default();
    let error = verify_artifact(&tampered, &limits, &ComputationControl::new()).unwrap_err();
    assert_eq!(error.kind(), Some(ArtifactKind::Census));
}

#[test]
fn a_default_budget_checkpoint_and_its_theorem_verify_through_the_dispatch() {
    let census = census_portable(CensusLimits::default())
        .verify(Default::default())
        .unwrap();
    let config = HomologicalStreamConfig::default();
    assert_eq!(config.budget, HomologicalStreamBudget::UNBOUNDED);
    let mut stream = homological_stream_from_census(&census, 2, config, None).unwrap();
    while let HomologicalStreamStep::Chunk(_) = stream.next_chunk() {}
    let checkpoint = stream.checkpoint();
    let text = checkpoint.to_canonical_json();
    let theorem = SelfExtLocusArtifact::from_verified_checkpoint(
        &checkpoint.verify(Default::default()).unwrap(),
        1,
        2,
    )
    .unwrap()
    .to_canonical_json();
    let unbounded = u64::MAX.to_string();
    for (text, kind) in [
        (&text, ArtifactKind::HomologicalStream),
        (&theorem, ArtifactKind::SelfExtLocus),
    ] {
        assert!(text.contains(&unbounded), "{kind:?}");
        let value = verified(text);
        assert_eq!(value.status(), ArtifactStatus::Verified);
        assert_eq!(value.report().kind(), kind);
        let widened = text.replacen(&unbounded, &format!("{unbounded}0"), 1);
        let limits = ArtifactLimits::default();
        let error = verify_artifact(&widened, &limits, &ComputationControl::new()).unwrap_err();
        assert!(error.to_string().contains("integer exceeds u64"), "{error}");
    }
}
