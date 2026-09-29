use std::sync::{Arc, OnceLock};

use super::super::tests::{silting_limits, silting_pair};
use super::super::{
    ClassificationLimits, ClassificationStatus, DerivedClassification, classify_derived,
};
use super::*;
use crate::algebra::{Algebra, AlgebraBuildError, commutative_square, linear_an, path_algebra};
use crate::completion::{Outcome, complete};
use crate::control::ComputationControl;
use crate::derived_artifact::{ArtifactMutation, ArtifactVerificationCut};
use crate::derived_invariant::{DerivedInvariantKind, InvariantLimits};
use crate::equivalence_discovery::DiscoveryLimits;
use crate::field::PrimeField;
use crate::gentle::connected_gentle_algebras;
use crate::hochschild::BarLimits;
use crate::portable::fingerprint;
use crate::quiver::{ArrowId, Quiver};
use crate::relation::{Presentation, Relation};
use crate::target::TargetLimits;

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn limits() -> ClassificationLimits {
    ClassificationLimits {
        invariants: InvariantLimits {
            hochschild_degree: 2,
            bar: BarLimits {
                max_tensor_tuples: 10_000,
                max_cochain_dim: 100_000,
                max_matrix_entries: 10_000_000,
                max_work_units: 1_000_000_000,
            },
        },
        discovery: DiscoveryLimits {
            max_vertices: 8,
            max_directed_mutations: 32,
            max_total_terms: 256,
            max_matrix_entries: 16_384,
            ..DiscoveryLimits::default()
        },
        target: TargetLimits::default(),
    }
}

fn classify(family: &[Arc<Algebra>]) -> DerivedClassification {
    classify_derived(family, &limits(), &ComputationControl::new()).unwrap()
}

/// The commutative square is not gentle and has the Cartan data of `D_4`.
/// It is derived equivalent to the `D_4` path algebra, but no recovered
/// target has the certificate of either, so that pair stays open.
fn mixed_family() -> [Arc<Algebra>; 4] {
    let d4 = path_algebra(Quiver::new(4, &[(0, 3), (1, 3), (2, 3)]).unwrap(), f2()).unwrap();
    [
        commutative_square(f2()),
        linear_an(4, f2()),
        commutative_square(f2()),
        d4,
    ]
}

/// The atlases of the connected gentle algebras with 2 and 3 vertices over
/// `F_2` and of [`mixed_family`], computed once per test binary.
fn atlases() -> &'static [DerivedAtlasArtifact; 3] {
    static ATLASES: OnceLock<[DerivedAtlasArtifact; 3]> = OnceLock::new();
    ATLASES.get_or_init(|| {
        let [two, three] = [2, 3].map(|n| {
            let family = connected_gentle_algebras(n, f2()).unwrap();
            classify(&family).to_artifact().unwrap()
        });
        [two, three, classify(&mixed_family()).to_artifact().unwrap()]
    })
}

fn verify_text(text: &str, limits: DerivedAtlasVerifyLimits) -> DerivedAtlasVerification {
    verify_derived_atlas_artifact(text, limits, &ComputationControl::new()).unwrap()
}

fn verified(artifact: &DerivedAtlasArtifact) -> VerifiedDerivedAtlas {
    let text = artifact.to_canonical_json();
    match verify_text(&text, DerivedAtlasVerifyLimits::default()) {
        DerivedAtlasVerification::Verified(value) => *value,
        DerivedAtlasVerification::Stopped(cut) => panic!("verification stopped: {cut:?}"),
    }
}

/// Recomputes the fingerprint after an edit, so the edit reaches the checks
/// behind the fingerprint.
fn resealed(edit: impl FnOnce(&mut DerivedAtlasArtifact), atlas: usize) -> String {
    let mut artifact = atlases()[atlas].clone();
    edit(&mut artifact);
    artifact.fingerprint = fingerprint(&artifact.canonical_without_fingerprint());
    artifact.to_canonical_json()
}

fn rejection(text: &str) -> DerivedAtlasError {
    let limits = DerivedAtlasVerifyLimits::default();
    verify_derived_atlas_artifact(text, limits, &ComputationControl::new()).unwrap_err()
}

/// The class and position of the first merge with a recipe.
fn walked_merge(artifact: &DerivedAtlasArtifact) -> (usize, usize) {
    let mut classes = artifact.classes.iter().enumerate();
    classes
        .find_map(|(c, class)| Some((c, class.merges.iter().position(|m| !m.recipe.is_empty())?)))
        .unwrap()
}

#[test]
fn atlases_round_trip_and_verify() {
    for (artifact, status) in atlases().iter().zip([
        ClassificationStatus::Complete,
        ClassificationStatus::Complete,
        ClassificationStatus::Incomplete,
    ]) {
        assert_eq!(artifact.status(), status);
        let text = artifact.to_canonical_json();
        let parsed = DerivedAtlasArtifact::from_json(&text, Default::default()).unwrap();
        assert_eq!(&parsed, artifact);
        let value = verified(&parsed);
        let rebuilt = value.classification();
        assert!(rebuilt.verify());
        assert_eq!(rebuilt.to_artifact().unwrap().to_canonical_json(), text);
    }
}

#[test]
fn identical_input_gives_identical_bytes() {
    let family = connected_gentle_algebras(2, f2()).unwrap();
    let again = classify(&family).to_artifact().unwrap();
    assert_eq!(again.to_canonical_json(), atlases()[0].to_canonical_json());
}

/// The layout of the n = 2 atlas, key by key.
#[test]
fn the_layout_is_pinned() {
    let text = atlases()[0].to_canonical_json();
    let prefix = "{\"schema\":\"auslander-computation-v1\",\"kind\":\"derived-atlas-v1\",\
                  \"engine\":\"derived-classification-v1\",\"field\":2,\"limits\":{\"invariants\":\
                  {\"hochschild_degree\":2,\"max_tensor_tuples\":10000,";
    assert!(text.starts_with(prefix), "{text}");
    for key in [
        "\"discovery\":{\"max_vertices\":8,",
        "\"target\":{\"max_endo_dimension\":",
        "}},\"members\":[\"{",
        "],\"invariants\":[[{\"kind\":\"vertex_count\",\"reading\":\"finished\",\"value\":[2]}",
        "{\"kind\":\"aag_function\",\"reading\":\"finished\",\"value\":[",
        "],\"classes\":[{\"members\":[",
        "\"merges\":[{\"source\":",
        ",\"recipe\":[[",
        ",\"vertex_map\":[",
        ",\"arrow_images\":[[",
        "],\"separations\":[{\"classes\":[0,1],\"members\":[",
        ",\"kind\":\"cartan_determinant\",\"left\":[",
        "],\"unresolved\":[],\"walks\":[{\"member\":",
        ",\"stop\":{\"kind\":\"",
        ",\"target_cuts\":0,",
        "}],\"status\":\"complete\",\"fingerprint\":\"",
    ] {
        assert!(text.contains(key), "{key}");
    }
}

/// The commutative square is not gentle, so its gentle readings are not
/// applicable, and its duplicate merges with an empty recipe.
#[test]
fn a_non_gentle_family_round_trips() {
    let artifact = &atlases()[2];
    for kind in [
        DerivedInvariantKind::AagFunction,
        DerivedInvariantKind::WindingClass,
    ] {
        assert_eq!(
            artifact.invariants()[0][kind as usize],
            AtlasReading::NotApplicable
        );
    }
    assert!(artifact.classes()[0].merges()[0].recipe().is_empty());
    assert_eq!(artifact.unresolved().len(), 1);
    let value = verified(artifact);
    assert_eq!(value.classification().classes().len(), 3);
}

/// Every stored winding class of the n = 3 atlas decodes to a known tag.
#[test]
fn winding_classes_are_tagged() {
    let kind = DerivedInvariantKind::WindingClass as usize;
    for readings in atlases()[1].invariants() {
        let AtlasReading::Finished(value) = &readings[kind] else {
            panic!("every gentle member has a winding class");
        };
        assert!(matches!(value[..], [0] | [1, _] | [2] | [3] | [4, 0 | 1]));
    }
}

#[test]
fn a_cancelled_classification_has_no_atlas() {
    let control = ComputationControl::new();
    control.cancel();
    let family = connected_gentle_algebras(2, f2()).unwrap();
    let result = classify_derived(&family, &limits(), &control).unwrap();
    assert!(matches!(
        result.to_artifact(),
        Err(DerivedAtlasError::CancelledReading { member: 0 })
    ));
    assert!(matches!(
        classify(&[]).to_artifact(),
        Err(DerivedAtlasError::EmptyFamily)
    ));
}

#[test]
fn cancellation_and_ceilings_give_typed_cuts() {
    let text = atlases()[0].to_canonical_json();
    let control = ComputationControl::new();
    control.cancel();
    let outcome = verify_derived_atlas_artifact(&text, Default::default(), &control).unwrap();
    assert!(matches!(
        outcome,
        DerivedAtlasVerification::Stopped(ArtifactVerificationCut::Cancelled {
            completed_mutations: 0
        })
    ));
    let mut limits = DerivedAtlasVerifyLimits::default();
    limits.replay.max_work_units = 0;
    assert!(matches!(
        verify_text(&text, limits),
        DerivedAtlasVerification::Stopped(ArtifactVerificationCut::WorkLimit {
            completed: 0,
            limit: 0
        })
    ));
    let limits = DerivedAtlasVerifyLimits {
        max_hochschild_degree: 1,
        ..Default::default()
    };
    assert!(matches!(
        verify_text(&text, limits),
        DerivedAtlasVerification::Stopped(ArtifactVerificationCut::DeclaredLimit {
            field: "hochschild_degree",
            declared: 2,
            limit: 1
        })
    ));
}

#[test]
fn an_omitted_member_is_rejected() {
    let text = resealed(
        |a| {
            a.members.pop();
            a.invariants.pop();
        },
        0,
    );
    assert!(matches!(rejection(&text), DerivedAtlasError::Partition));
}

#[test]
fn a_duplicate_class_member_is_rejected() {
    let text = resealed(|a| a.classes[1].members.insert(0, 0), 0);
    assert!(matches!(rejection(&text), DerivedAtlasError::Partition));
}

#[test]
fn a_modified_invariant_value_is_rejected() {
    let kind = DerivedInvariantKind::CartanDeterminant;
    let text = resealed(
        |a| a.invariants[3][kind as usize] = AtlasReading::Finished(vec![-7]),
        0,
    );
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::ReadingMismatch {
            member: 3,
            kind: DerivedInvariantKind::CartanDeterminant
        }
    ));
}

#[test]
fn a_modified_isomorphism_coordinate_is_rejected() {
    let (class, merge) = walked_merge(&atlases()[0]);
    let text = resealed(
        |a| {
            let image = &mut a.classes[class].merges[merge].arrow_images[0];
            image.iter_mut().for_each(|value| *value = 1 - *value);
        },
        0,
    );
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::Isomorphism { .. }
    ));
    let text = resealed(|a| a.classes[class].merges[merge].arrow_images[0][0] = 2, 0);
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::Isomorphism { .. }
    ));
}

#[test]
fn a_modified_recipe_is_rejected() {
    let (class, merge) = walked_merge(&atlases()[0]);
    let text = resealed(
        |a| {
            let recipe = &mut a.classes[class].merges[merge].recipe;
            recipe[0] = ArtifactMutation::new(recipe[0].direction(), 99);
        },
        0,
    );
    assert!(matches!(rejection(&text), DerivedAtlasError::Replay { .. }));
}

/// The silting walk merges [`silting_pair`] along a recipe through a silting
/// complex. Declaring a tilting walk fails the replay of that recipe.
#[test]
fn a_flipped_through_silting_flag_is_rejected() {
    let control = ComputationControl::new();
    let result = classify_derived(&silting_pair(), &silting_limits(), &control).unwrap();
    let mut artifact = result.to_artifact().unwrap();
    let text = artifact.to_canonical_json();
    assert!(text.contains(",\"max_hom_spaces\":4096,\"through_silting\":true},"));
    verified(&artifact);
    let flipped = text.replacen("\"through_silting\":true", "\"through_silting\":false", 1);
    assert!(matches!(
        rejection(&flipped),
        DerivedAtlasError::FingerprintMismatch
    ));
    artifact.limits.discovery.through_silting = false;
    artifact.fingerprint = fingerprint(&artifact.canonical_without_fingerprint());
    let text = artifact.to_canonical_json();
    assert!(matches!(rejection(&text), DerivedAtlasError::Replay { .. }));
}

#[test]
fn a_forged_separation_with_equal_values_is_rejected() {
    let text = resealed(
        |a| a.separations[0].right = a.separations[0].left.clone(),
        0,
    );
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::Separation { classes: (0, 1) }
    ));
    let text = resealed(
        |a| a.separations[0].kind = DerivedInvariantKind::VertexCount,
        0,
    );
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::Separation { classes: (0, 1) }
    ));
}

/// The classes of members 0 and 3 form the one unresolved pair of the
/// mixed atlas. A merge across them breaks the spanning tree of its class,
/// and a separation of them lists the pair twice.
#[test]
fn an_unresolved_pair_claimed_as_merged_is_rejected() {
    let atlas = &atlases()[2];
    let [open] = atlas.unresolved() else {
        panic!("one unresolved pair expected");
    };
    let (left, right) = open.classes();
    assert_eq!(atlas.classes()[left].members(), [0, 2]);
    assert_eq!(atlas.classes()[right].members(), [3]);
    let text = resealed(
        |a| {
            let mut forged = a.classes[left].merges[0].clone();
            (forged.source, forged.member) = (0, 3);
            a.classes[left].merges.push(forged);
        },
        2,
    );
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::SpanningTree { class } if class == left
    ));
    let text = resealed(
        |a| {
            let mut separation = a.separations[0].clone();
            separation.classes = (left, right);
            a.separations.push(separation);
        },
        2,
    );
    assert!(matches!(rejection(&text), DerivedAtlasError::PairCoverage));
    let text = resealed(|a| a.status = ClassificationStatus::Complete, 2);
    assert!(matches!(rejection(&text), DerivedAtlasError::Status));
    let text = resealed(
        |a| {
            a.unresolved[0].walks.pop();
        },
        2,
    );
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::UnresolvedWalks { .. }
    ));
}

/// Each structural check rejects its own forgery before any replay.
#[test]
fn structural_forgeries_name_the_failed_check() {
    let text = resealed(|a| drop(a.invariants.pop()), 0);
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::RowCount {
            rows: 8,
            members: 9
        }
    ));
    let (class, _) = walked_merge(&atlases()[0]);
    let text = resealed(|a| a.classes[class].merges.clear(), 0);
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::SpanningTree { class: c } if c == class
    ));
    let text = resealed(|a| drop(a.separations.pop()), 0);
    assert!(matches!(rejection(&text), DerivedAtlasError::PairCoverage));
    let text = resealed(|a| a.walks[0].merges += 1, 0);
    assert!(matches!(rejection(&text), DerivedAtlasError::Walks));
    let text = resealed(|a| a.walks.swap(0, 1), 1);
    assert!(matches!(rejection(&text), DerivedAtlasError::Walks));
}

/// A member that does not rebuild names the member and the failed step:
/// the atlas field, the certificate field, the certificate verifier, or the
/// algebra build.
#[test]
fn members_that_do_not_rebuild_are_typed() {
    let text = resealed(|a| a.field = 4, 0);
    assert!(matches!(rejection(&text), DerivedAtlasError::Field(_)));
    let text = resealed(|a| a.members[1].field = 3, 0);
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::FieldMismatch {
            member: 1,
            found: 3
        }
    ));
    let text = resealed(|a| drop(a.members[1].normal_words.pop()), 0);
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::Verify { member: 1, .. }
    ));
    // `k[x]/(x³ - x²)` has a verified certificate, but its arrow ideal is
    // not nilpotent, so no algebra is built from it.
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let (one, loop_word) = (f2().one(), |length| vec![ArrowId(0); length]);
    let terms = vec![(one, loop_word(3)), (one, loop_word(2))];
    let relation = Relation::new(&quiver, f2(), terms).unwrap();
    let presentation = Presentation::new(quiver, f2(), vec![relation]).unwrap();
    let Outcome::Complete(certificate) = complete(&presentation, &Default::default()) else {
        panic!("x³ - x² completes");
    };
    let text = resealed(|a| a.members[0] = certificate, 0);
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::Algebra {
            member: 0,
            error: AlgebraBuildError::NonAdmissible { .. }
        }
    ));
    let malformed =
        atlases()[0]
            .to_canonical_json()
            .replacen("[\"{\\\"schema\\\"", "[\"{\\\"schemo\\\"", 1);
    assert!(matches!(
        rejection(&malformed),
        DerivedAtlasError::Certificate { member: 0, .. }
    ));
}

/// The atlas of the connected gentle algebras with 2 vertices over `F_3`
/// stores field 3 and replays to the same bytes.
#[test]
fn an_f3_atlas_round_trips() {
    let f3 = PrimeField::new(3).unwrap();
    let artifact = classify(&connected_gentle_algebras(2, f3).unwrap())
        .to_artifact()
        .unwrap();
    let text = artifact.to_canonical_json();
    assert!(text.contains("\"field\":3,"));
    let value = verified(&artifact);
    assert_eq!(value.classification().classes().len(), 8);
    assert_eq!(
        value
            .classification()
            .to_artifact()
            .unwrap()
            .to_canonical_json(),
        text
    );
}

#[test]
fn an_altered_fingerprint_is_rejected() {
    let text = atlases()[0].to_canonical_json();
    let position = text.len() - 3;
    let mut bytes = text.into_bytes();
    bytes[position] = if bytes[position] == b'0' { b'1' } else { b'0' };
    let text = String::from_utf8(bytes).unwrap();
    assert!(matches!(
        rejection(&text),
        DerivedAtlasError::FingerprintMismatch
    ));
}

#[test]
fn the_parser_is_strict() {
    let text = atlases()[0].to_canonical_json();
    let replace = |from: &str, to: &str| rejection(&text.replacen(from, to, 1));
    assert!(matches!(
        replace("auslander-computation-v1", "auslander-computation-v2"),
        DerivedAtlasError::Schema { .. }
    ));
    assert!(matches!(
        replace("derived-atlas-v1", "derived-atlas-v2"),
        DerivedAtlasError::Kind { .. }
    ));
    assert!(matches!(
        replace("derived-classification-v1", "x"),
        DerivedAtlasError::Engine { .. }
    ));
    assert!(matches!(
        replace("\"field\":2", "\"field\":2,\"extra\":0"),
        DerivedAtlasError::Syntax { .. }
    ));
    assert!(matches!(
        replace("\"field\":2", "\"field\": 2"),
        DerivedAtlasError::NonCanonical
    ));
    assert!(matches!(
        replace("\"reading\":\"finished\"", "\"reading\":\"guessed\""),
        DerivedAtlasError::Syntax { .. }
    ));
    let limits = DerivedAtlasParseLimits {
        max_members: 1,
        ..Default::default()
    };
    assert!(matches!(
        DerivedAtlasArtifact::from_json(&text, limits),
        Err(DerivedAtlasError::ParseLimit { .. })
    ));
}

#[test]
fn signed_values_have_one_spelling() {
    let text = atlases()[0].to_canonical_json();
    let determinant = "{\"kind\":\"cartan_determinant\",\"reading\":\"finished\",\"value\":[";
    assert!(text.contains(determinant));
    for (value, accepted) in [("-1", true), ("-0", false), ("- 1", false), ("-", false)] {
        let edited = text.replacen(
            &format!("{determinant}1]"),
            &format!("{determinant}{value}]"),
            1,
        );
        let result = DerivedAtlasArtifact::from_json(&edited, Default::default());
        assert_eq!(result.is_ok(), accepted, "{value}: {result:?}");
    }
}

/// Walk counters are untrusted, so no check may sum them.
#[test]
fn huge_walk_counters_are_rejected() {
    let atlas = atlases().iter().position(|a| a.walks.len() >= 2).unwrap();
    let text = resealed(
        |a| a.walks.iter_mut().for_each(|walk| walk.merges = usize::MAX),
        atlas,
    );
    assert!(matches!(rejection(&text), DerivedAtlasError::Walks));
}

#[test]
fn a_member_above_the_dimension_ceiling_stops_replay() {
    let text = atlases()[1].to_canonical_json();
    let limits = DerivedAtlasVerifyLimits {
        max_member_dimension: 3,
        ..Default::default()
    };
    assert!(matches!(
        verify_text(&text, limits),
        DerivedAtlasVerification::Stopped(ArtifactVerificationCut::DeclaredLimit {
            field: "member_dimension",
            limit: 3,
            ..
        })
    ));
}

/// The replay rebuilds the groups without a table of member pairs.
#[test]
fn replayed_groups_match_the_classification() {
    let value = verified(&atlases()[2]);
    assert_eq!(
        value.classification().groups(),
        classify(&mixed_family()).groups()
    );
    let family = connected_gentle_algebras(3, f2()).unwrap();
    let value = verified(&atlases()[1]);
    assert_eq!(value.classification().groups(), classify(&family).groups());
}
