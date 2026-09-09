use auslander::census::CensusOutcome;
use auslander::iso::{IsoOutcome, is_isomorphic};
use auslander::module::{Module, direct_sum};
use auslander::theorem_artifact::{
    SelfExtLocusArtifact, SelfExtLocusVerifyLimits, verify_self_ext_locus_artifact,
};

const STARTER_ARTIFACT: &str =
    include_str!("../artifacts/research/commutative-square-f2-d1111-self-ext-1-3.json");
const FLAGSHIP_ARTIFACT: &str =
    include_str!("../artifacts/research/commutative-square-f2-d2112-self-ext-1-3.json");

#[test]
fn commutative_square_self_ext_locus_replays_and_recomputes() {
    let verified =
        verify_self_ext_locus_artifact(STARTER_ARTIFACT, SelfExtLocusVerifyLimits::default())
            .expect("the committed finite claim verifies");
    let artifact = verified.artifact();
    assert_eq!(artifact.to_canonical_json(), STARTER_ARTIFACT);
    assert_eq!(artifact.first_degree(), 1);
    assert_eq!(artifact.last_degree(), 3);
    assert_eq!(artifact.vanishing_indices(), &[9]);

    let checkpoint = verified.checkpoint().portable();
    assert_eq!(checkpoint.rows().len(), 10);
    assert_eq!(checkpoint.work().chunks, 5);
    assert_eq!(checkpoint.chunk_sizes(), &[2, 2, 2, 2, 2]);
    assert_eq!(checkpoint.work().peak_live_sources, 2);
    let CensusOutcome::Complete(census) = verified.checkpoint().census().outcome() else {
        panic!("the artifact embeds a complete census")
    };
    assert_eq!(census.domain().raw_space_size(), 16);
    assert_eq!(census.representatives().len(), 10);
    assert_eq!(census.rejected_candidates(), 6);
    assert_eq!(census.isomorphism_checks(), 45);
    assert_eq!(census.work_units(), 61);
}

#[test]
fn flagship_self_ext_locus_replays_and_recomputes() {
    let verified =
        verify_self_ext_locus_artifact(FLAGSHIP_ARTIFACT, SelfExtLocusVerifyLimits::default())
            .expect("the flagship finite claim verifies");
    let artifact = verified.artifact();
    assert_eq!(artifact.to_canonical_json(), FLAGSHIP_ARTIFACT);
    assert_eq!(artifact.first_degree(), 1);
    assert_eq!(artifact.last_degree(), 3);
    assert_eq!(artifact.vanishing_indices(), &[5, 10]);

    let degree_one =
        SelfExtLocusArtifact::from_verified_checkpoint(verified.checkpoint(), 1, 1).unwrap();
    assert_eq!(degree_one.vanishing_indices(), &[5, 10, 11]);
    degree_one
        .verify(SelfExtLocusVerifyLimits::default())
        .expect("the degree-one locus must replay and recompute");

    let checkpoint = verified.checkpoint().portable();
    assert_eq!(checkpoint.rows().len(), 12);
    assert_eq!(checkpoint.work().chunks, 6);
    assert_eq!(checkpoint.chunk_sizes(), &[2, 2, 2, 2, 2, 2]);
    assert_eq!(checkpoint.work().peak_live_sources, 2);
    assert_eq!(checkpoint.rows()[5].ext_dimensions(), &[6, 0, 0, 0]);
    assert_eq!(checkpoint.rows()[10].ext_dimensions(), &[6, 0, 0, 0]);
    assert_eq!(checkpoint.rows()[11].ext_dimensions(), &[5, 0, 1, 0]);

    let CensusOutcome::Complete(census) = verified.checkpoint().census().outcome() else {
        panic!("the artifact embeds a complete census")
    };
    assert_eq!(census.domain().dimensions(), &[2, 1, 1, 2]);
    assert_eq!(census.domain().raw_space_size(), 256);
    assert_eq!(census.representatives().len(), 12);
    assert_eq!(census.candidates(), 256);
    assert_eq!(census.accepted_modules(), 58);
    assert_eq!(census.rejected_candidates(), 198);
    assert_eq!(census.isomorphism_checks(), 439);
    assert_eq!(census.work_units(), 695);

    let representative = census.representatives()[11].module();
    let algebra = representative.algebra();
    let p0 = Module::projective(algebra, 0);
    let s0 = Module::simple(algebra, 0);
    let s3 = Module::simple(algebra, 3);
    let (decomposition, _, _) = direct_sum(&[&p0, &s0, &s3]);
    let IsoOutcome::Isomorphic(witness) = is_isomorphic(representative, &decomposition).unwrap()
    else {
        panic!("representative 11 must be isomorphic to P_0 ⊕ S_0 ⊕ S_3")
    };
    assert!(witness.is_isomorphism());
}
