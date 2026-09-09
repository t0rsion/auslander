use super::*;

// The almost complete pairs over A_2, listed by hand. The condition is
// |M| + |P| = 1, so either M is one tau-rigid indecomposable with an empty
// support, or M is zero and P is a single vertex. All three
// indecomposables are tau-rigid alone, and Hom(P_v, 0) is zero for both
// vertices, so there are 5 almost complete pairs. That is the edge count
// of the pentagon, as it must be: each edge is one almost complete pair
// with its two completions.
#[test]
fn the_a2_almost_complete_pairs_are_the_five_edges() {
    for field in fields() {
        let algebra = linear_an(2, field);
        let modules = [
            Module::simple(&algebra, 0),
            Module::simple(&algebra, 1),
            Module::projective(&algebra, 0),
        ];
        let mut found = 0;
        for m in &modules {
            let pair = AlmostCompletePair::new(basic(m), support(&algebra, &[]))
                .expect("A_2 translates")
                .expect("a tau-rigid indecomposable with no support is almost complete");
            assert_eq!(pair.summand_count(), 1);
            assert!(pair.verify());
            found += 1;
        }
        for v in [0u32, 1] {
            let pair =
                AlmostCompletePair::new(basic(&Module::zero(&algebra)), support(&algebra, &[v]))
                    .expect("the zero module needs no translate")
                    .expect("(0, P_v) is almost complete");
            assert!(pair.module().is_empty());
            assert_eq!(pair.projective().len(), 1);
            assert!(pair.verify());
            found += 1;
        }
        assert_eq!(found, 5, "over F_{}", field.modulus());
    }
}

// The two totals separate the two types: a support tau-tilting pair has
// n summands and an almost complete pair has n - 1, so neither is the
// other and the rejection names condition 4 both ways.
#[test]
fn the_two_pair_types_reject_each_other_on_the_count() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let a = regular(&algebra);
        let full = SupportTauTiltingPair::new(basic(&a), support(&algebra, &[]))
            .expect("A_3 translates")
            .expect("(A, 0) is a pair");
        assert_eq!(full.summand_count(), 3);
        let as_almost = AlmostCompletePair::classify(basic(&a), support(&algebra, &[]))
            .expect("A_3 translates");
        match as_almost {
            AlmostCompleteClassification::Rejected(PairRejection::SummandCount {
                module,
                projective,
                expected,
            }) => assert_eq!((module, projective, expected), (3, 0, 2)),
            other => panic!("expected a count rejection, got {other:?}"),
        }
        // P_0 + P_1 is tau-rigid with two summands, which is n - 1 over
        // A_3, and Hom(0, M) is zero.
        let two = sum(
            &algebra,
            &[
                &Module::projective(&algebra, 0),
                &Module::projective(&algebra, 1),
            ],
        );
        let almost = AlmostCompletePair::new(basic(&two), support(&algebra, &[]))
            .expect("A_3 translates")
            .expect("(P_0 + P_1, 0) is almost complete");
        assert_eq!(almost.summand_count(), 2);
        assert!(almost.verify());
        let as_full = SupportTauTiltingPair::classify(basic(&two), support(&algebra, &[]))
            .expect("A_3 translates");
        assert_eq!(
            expect_rejection(as_full).condition(),
            4,
            "over F_{}",
            field.modulus()
        );
    }
}

// Every accepted pair verifies, and the one tamper the type still admits
// fails. The support is derived from the module part, so there is no
// support field to tamper with and no vanishing witness to borrow: the
// tau-rigidity witness is the only stored claim left.
#[test]
fn a_tampered_pair_fails_verification() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let a = regular(&algebra);
        let pair = SupportTauTiltingPair::new(basic(&a), support(&algebra, &[]))
            .expect("A_3 translates")
            .expect("(A, 0) is a pair");
        assert!(pair.verify());
        assert!(pair.projective().is_empty(), "A is sincere");

        // A tau-rigidity witness borrowed from another pair with the same
        // summand count. S_1 + P_1 + P_0 is a pair with three summands, so
        // the length check passes and the summand identity check is what
        // fails.
        let s1 = Module::simple(&algebra, 1);
        let p1 = Module::projective(&algebra, 1);
        let mut forged = SupportTauTiltingPair::new(basic(&a), support(&algebra, &[]))
            .expect("A_3 translates")
            .expect("(A, 0) is a pair");
        let donor = SupportTauTiltingPair::new(
            basic(&sum(
                &algebra,
                &[&s1, &p1, &Module::projective(&algebra, 0)],
            )),
            support(&algebra, &[]),
        )
        .expect("A_3 translates")
        .expect("(S_1 + P_1 + P_0, 0) is a pair");
        assert!(donor.rigid().verify(), "the donor witness is honest");
        assert_eq!(
            donor.rigid().summands().len(),
            forged.rigid.summands().len()
        );
        forged.rigid = donor.rigid().clone();
        assert!(!forged.verify(), "over F_{}", field.modulus());
    }
}

// The projective part is forced, so a candidate that passes conditions 1
// to 4 with a support strictly inside the support complement cannot exist.
// Over A_3 the closest a caller gets is (S_1 + P_1, {0}), where the
// complement of the support (0, 2, 1) is exactly {0}: dropping vertex 0
// breaks the count instead of producing a second pair on the same module.
#[test]
fn the_projective_part_of_a_pair_is_the_whole_support_complement() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let m = sum(
            &algebra,
            &[
                &Module::simple(&algebra, 1),
                &Module::projective(&algebra, 1),
            ],
        );
        assert_eq!(basic(&m).module().dim_vector(), &[0, 2, 1]);
        let pair = SupportTauTiltingPair::new(basic(&m), support(&algebra, &[0]))
            .expect("A_3 translates")
            .expect("(S_1 + P_1, P_0) is a pair");
        assert_eq!(pair.projective().vertices(), [0]);
        let short = expect_rejection(
            SupportTauTiltingPair::classify(basic(&m), support(&algebra, &[]))
                .expect("A_3 translates"),
        );
        assert_eq!(short.condition(), 4, "over F_{}", field.modulus());
    }
}

// A shared cache computes one translate per catalog entry across a whole
// run. Over A_3 that is six translates for the six catalog entries, one
// miss each and no hit, because each entry is classified once and the
// cache is keyed by module identity.
#[test]
fn a_shared_cache_serves_a_whole_enumeration() {
    let field = f5();
    let algebra = linear_an(3, field);
    let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_3 is Dynkin");
    let mut cache = TauCache::new();
    for (i, entry) in catalog.entries().iter().enumerate() {
        let pair = SupportTauTiltingPair::classify_with_cache(
            basic(entry.module()),
            support(&algebra, &[]),
            &[i],
            Some(&mut cache),
        )
        .expect("A_3 translates");
        // A single indecomposable is never a pair over A_3: 1 + |P| = 3
        // needs two support vertices outside its support, and an empty
        // support leaves |M| + |P| = 1. Every entry is tau-rigid alone and
        // Hom(0, X) is zero, so the rejection is condition 4 every time.
        assert_eq!(expect_rejection(pair).condition(), 4);
    }
    assert_eq!(cache.len(), catalog.len());
    assert_eq!(cache.misses(), catalog.len() as u64);
}

#[test]
fn a_wrong_index_count_is_rejected() {
    let algebra = linear_an(3, f5());
    let error = SupportTauTiltingPair::classify_with_cache(
        basic(&regular(&algebra)),
        support(&algebra, &[]),
        &[0, 1],
        None,
    )
    .unwrap_err();
    assert!(matches!(
        error,
        SupportTauError::SummandIndexCount {
            indices: 2,
            summands: 3
        }
    ));
}
