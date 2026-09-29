//! One small portable value per kind and status, shared by the native tests
//! and the `parity_corpus` example that feeds `web/parity.mjs`.

use std::sync::Arc;

use auslander::algebra::{Algebra, commutative_square, linear_an, path_algebra};
use auslander::arquiver::IndecomposableCatalog;
use auslander::atlas::{CatalogAtlas, CatalogAtlasLimits, MultiplicityLimits};
use auslander::atlas_artifact::CatalogAtlasArtifact;
use auslander::batch_stream::{
    HomologicalBatchStreamLimits, HomologicalStreamBudget, HomologicalStreamConfig,
    HomologicalStreamPortable, HomologicalStreamStep, homological_stream_from_census,
};
use auslander::census::{Census, CensusLimits, CensusPortable, VerifiedCensus};
use auslander::control::ComputationControl;
use auslander::derived_artifact::DerivedArtifact;
use auslander::derived_classification::{ClassificationLimits, classify_derived};
use auslander::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use auslander::field::PrimeField;
use auslander::gentle::connected_gentle_algebras;
use auslander::quiver::Quiver;
use auslander::target::TargetLimits;
use auslander::theorem_artifact::SelfExtLocusArtifact;
use auslander::tilting_complex::{
    TiltingComplexLimits, TiltingComplexResult, TiltingMutationOutcome, left_tilting_mutation,
    regular_tilting_complex,
};

fn a2() -> Arc<Algebra> {
    linear_an(2, PrimeField::new(5).unwrap())
}

/// A derived artifact from one left mutation of `A_2` over `F_5`.
///
/// With `max_hom_spaces` above the verifier ceiling, verification stops at
/// the declared-limit check.
fn derived(max_hom_spaces: u64) -> String {
    let limits = TiltingComplexLimits { max_hom_spaces };
    let TiltingComplexResult::Tilting(regular) = regular_tilting_complex(&a2(), limits).unwrap()
    else {
        panic!("the regular generator certifies")
    };
    let mutation = (0..2)
        .find_map(
            |summand| match left_tilting_mutation(&regular, summand, limits).unwrap() {
                TiltingMutationOutcome::Tilting(value)
                    if value
                        .candidate()
                        .summands()
                        .iter()
                        .any(|part| part.complex().len() > 1) =>
                {
                    Some(*value)
                }
                _ => None,
            },
        )
        .expect("A2 has a multi-degree left mutation");
    let DerivedEquivalenceEdgeOutcome::Certified(edge) =
        DerivedEquivalenceEdge::recover(mutation, &TargetLimits::default()).unwrap()
    else {
        panic!("the A2 target completes")
    };
    DerivedArtifact::from_edge(&edge)
        .unwrap()
        .to_canonical_json()
}

fn census(limits: CensusLimits) -> CensusPortable {
    let outcome = Census::new(&a2(), vec![1, 1])
        .unwrap()
        .run_with(limits, None);
    CensusPortable::from_outcome(&outcome).unwrap()
}

/// A budget below 4294967295 in both fields.
const EXPLICIT: HomologicalStreamBudget = HomologicalStreamBudget {
    max_sources: 100,
    max_work_units: 100_000,
};

fn stream_config(budget: HomologicalStreamBudget) -> HomologicalStreamConfig {
    HomologicalStreamConfig {
        chunk_limits: HomologicalBatchStreamLimits {
            max_live_sources: 1,
            max_pairs: 100,
            max_ext_cells: 500,
        },
        budget,
    }
}

/// The checkpoint after `chunks` chunks, or the complete checkpoint.
fn homological(
    census: &VerifiedCensus,
    chunks: Option<usize>,
    budget: HomologicalStreamBudget,
) -> HomologicalStreamPortable {
    let mut stream =
        homological_stream_from_census(census, 2, stream_config(budget), None).unwrap();
    let mut taken = 0;
    while Some(taken) != chunks {
        match stream.next_chunk() {
            HomologicalStreamStep::Chunk(_) => taken += 1,
            HomologicalStreamStep::Complete { .. } => break,
            step => panic!("the A2 stream completes: {step:?}"),
        }
    }
    stream.checkpoint()
}

fn atlas(max_solutions: u64) -> String {
    let algebra = linear_an(3, PrimeField::new(2).unwrap());
    let catalog = Arc::new(IndecomposableCatalog::dynkin(&algebra).unwrap());
    let atlas = CatalogAtlas::compute(catalog, 2, CatalogAtlasLimits::default()).unwrap();
    let limits = MultiplicityLimits {
        max_solutions,
        ..MultiplicityLimits::default()
    };
    CatalogAtlasArtifact::from_verified(&atlas, &[1, 1, 1], limits)
        .unwrap()
        .to_canonical_json()
}

/// The limits of the classification study.
///
/// With `max_hom_spaces` above the verifier ceiling, verification stops at
/// the declared-limit check.
fn study_limits(max_hom_spaces: u64) -> ClassificationLimits {
    let mut limits = ClassificationLimits::with_walk_vertices(8);
    limits.discovery.tilting.max_hom_spaces = max_hom_spaces;
    limits
}

/// The study limits with walk ceilings above 4294967295 that no walk over
/// `gentle(2, 2)` reaches. With `bar`, the bar tuple ceiling is also above
/// 4294967295 and above its verifier ceiling, so verification stops at the
/// declared-limit check.
fn wide_limits(bar: bool) -> ClassificationLimits {
    const WIDE: u64 = 1 << 33;
    let mut limits = study_limits(TiltingComplexLimits::default().max_hom_spaces);
    limits.discovery.max_total_terms = WIDE;
    limits.discovery.max_matrix_entries = WIDE;
    if bar {
        limits.invariants.bar.max_tensor_tuples = WIDE;
    }
    limits
}

/// The derived atlas of `family` under `limits`.
fn derived_atlas(family: &[Arc<Algebra>], limits: ClassificationLimits) -> String {
    classify_derived(family, &limits, &ComputationControl::new())
        .unwrap()
        .to_artifact()
        .unwrap()
        .to_canonical_json()
}

/// The connected gentle algebras with `n` vertices over `GF(p)`.
fn gentle(n: u32, p: u64) -> Vec<Arc<Algebra>> {
    connected_gentle_algebras(n, PrimeField::new(p).unwrap()).unwrap()
}

/// The commutative square, `A_4`, the square again, and the `D_4` path
/// algebra over `F_2`. The square and `D_4` stay unresolved, so the atlas is
/// incomplete.
fn mixed() -> Vec<Arc<Algebra>> {
    let f2 = PrimeField::new(2).unwrap();
    let d4 = Quiver::new(4, &[(0, 3), (1, 3), (2, 3)]).unwrap();
    vec![
        commutative_square(f2),
        linear_an(4, f2),
        commutative_square(f2),
        path_algebra(d4, f2).unwrap(),
    ]
}

/// File names and canonical texts, one per kind and status.
pub fn corpus() -> Vec<(&'static str, String)> {
    let complete = census(CensusLimits::default());
    let cut = census(CensusLimits {
        max_candidates: 3,
        ..CensusLimits::default()
    });
    let verified = complete.verify(Default::default()).unwrap();
    let stream = homological(&verified, None, EXPLICIT);
    let unbounded = homological(&verified, None, HomologicalStreamBudget::default());
    let theorem = |stream: &HomologicalStreamPortable| {
        SelfExtLocusArtifact::from_verified_checkpoint(
            &stream.verify(Default::default()).unwrap(),
            1,
            2,
        )
        .unwrap()
        .to_canonical_json()
    };
    let ceiling = TiltingComplexLimits::default().max_hom_spaces;
    vec![
        ("derived.json", derived(ceiling)),
        ("derived-stopped.json", derived(ceiling + 1)),
        ("census.json", complete.to_canonical_json()),
        ("census-cut.json", cut.to_canonical_json()),
        ("homological.json", stream.to_canonical_json()),
        (
            "homological-active.json",
            homological(&verified, Some(1), EXPLICIT).to_canonical_json(),
        ),
        (
            "homological-default-budget.json",
            unbounded.to_canonical_json(),
        ),
        (
            "homological-default-budget-active.json",
            homological(&verified, Some(1), HomologicalStreamBudget::default()).to_canonical_json(),
        ),
        (
            "atlas.json",
            atlas(MultiplicityLimits::default().max_solutions),
        ),
        ("atlas-cut.json", atlas(1)),
        ("theorem.json", theorem(&stream)),
        ("theorem-default-budget.json", theorem(&unbounded)),
        (
            "derived-atlas-n2.json",
            derived_atlas(&gentle(2, 2), study_limits(ceiling)),
        ),
        (
            "derived-atlas-n3.json",
            derived_atlas(&gentle(3, 2), study_limits(ceiling)),
        ),
        (
            "derived-atlas-f3-n2.json",
            derived_atlas(&gentle(2, 3), study_limits(ceiling)),
        ),
        (
            "derived-atlas-incomplete.json",
            derived_atlas(&mixed(), study_limits(ceiling)),
        ),
        (
            "derived-atlas-stopped.json",
            derived_atlas(&gentle(2, 2), study_limits(ceiling + 1)),
        ),
        (
            "derived-atlas-wide.json",
            derived_atlas(&gentle(2, 2), wide_limits(false)),
        ),
        (
            "derived-atlas-wide-stopped.json",
            derived_atlas(&gentle(2, 2), wide_limits(true)),
        ),
    ]
}
