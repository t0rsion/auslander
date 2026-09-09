use super::*;

// (A, 0) is a support tau-tilting pair over every algebra: A is basic over
// a basic algebra with one summand per vertex, tau of a projective is
// zero so A is tau-rigid, Hom(0, A) is zero, and |A| + |0| = n. The
// fixtures include kronecker(2), which has no catalog: pair verification
// is general even where enumeration is impossible.
#[test]
fn the_regular_pair_is_a_support_tau_tilting_pair() {
    for field in fields() {
        for algebra in [
            linear_an(2, field),
            linear_an(3, field),
            d4(field),
            truncated_poly(3, field).unwrap(),
            linear_nakayama(&[2, 2, 1], field).unwrap(),
            radical_square_zero_cycle(3, field),
            commutative_square(field),
            kronecker(2, field),
            semisimple(3, field),
        ] {
            let n = algebra.quiver().num_vertices() as usize;
            let pair = expect_pair(
                SupportTauTiltingPair::classify(basic(&regular(&algebra)), support(&algebra, &[]))
                    .expect("the fixture translates"),
            );
            assert_eq!(pair.module().len(), n);
            assert_eq!(pair.summand_count(), n);
            assert!(pair.is_tau_tilting(), "the projective part is empty");
            assert!(pair.projective().is_empty());
            assert!(pair.rigid().vanishing_pairs().is_empty(), "tau A is zero");
            assert!(pair.verify(), "over F_{}", field.modulus());
        }
    }
}
// (0, A) is a support tau-tilting pair: the zero module is tau-rigid with
// no summand, Hom(A, 0) is zero, and 0 + n = n. It is the pair the design
// calls a legitimate vertex with an empty module part.
#[test]
fn the_zero_module_over_the_full_support_is_a_support_tau_tilting_pair() {
    for field in fields() {
        for algebra in [
            linear_an(2, field),
            d4(field),
            truncated_poly(3, field).unwrap(),
            kronecker(2, field),
        ] {
            let n = algebra.quiver().num_vertices() as usize;
            let pair = expect_pair(
                SupportTauTiltingPair::classify(
                    basic(&Module::zero(&algebra)),
                    support(&algebra, &all_vertices(&algebra)),
                )
                .expect("the zero module needs no translate"),
            );
            assert!(pair.module().is_empty());
            assert_eq!(pair.projective().len(), n);
            assert_eq!(pair.summand_count(), n);
            assert!(!pair.is_tau_tilting(), "the projective part is all of A");
            assert!(pair.rigid().is_zero_module());
            assert!(pair.verify(), "over F_{}", field.modulus());
        }
    }
}

// One rejection per condition, over linearly oriented A_2 (arrow 0 -> 1)
// except for the algebra check. The indecomposables are S_0 = (1, 0),
// S_1 = P_1 = (0, 1), and P_0 = (1, 1), and tau S_0 = S_1 is the only
// nonzero translate.
//
// 1. Two algebra values built from the same presentation are different
//    values, so the module part and the support do not share one Arc.
// 2. (P_0, {1}): Hom(P_1, P_0) has dimension dim (P_0)_1 = 1. The other
//    three conditions hold, so this isolates condition 2.
// 3. (S_0 + S_1, {}): Hom(0, M) is zero and 2 + 0 = 2, so the first
//    failure is Hom(S_1, tau S_0) = End(S_1), of dimension 1.
// 4. (0, {}): the zero module is tau-rigid and Hom(0, 0) is zero, so the
//    first failure is 0 + 0 != 2.
#[test]
fn each_condition_has_its_own_rejection() {
    for field in fields() {
        let algebra = linear_an(2, field);
        let other = linear_an(2, field);
        let s0 = Module::simple(&algebra, 0);
        let s1 = Module::simple(&algebra, 1);
        let p0 = Module::projective(&algebra, 0);

        let mismatched = expect_rejection(
            SupportTauTiltingPair::classify(basic(&p0), support(&other, &[]))
                .expect("the algebra check runs before any Hom space"),
        );
        assert_eq!(mismatched.condition(), 1);
        assert!(matches!(mismatched, PairRejection::DifferentAlgebras));

        let hom = expect_rejection(
            SupportTauTiltingPair::classify(basic(&p0), support(&algebra, &[1]))
                .expect("A_2 translates"),
        );
        assert_eq!(hom.condition(), 2);
        assert!(matches!(
            hom,
            PairRejection::HomFromProjectiveNonzero { vertex: 1, dim: 1 }
        ));

        let rigid = expect_rejection(
            SupportTauTiltingPair::classify(
                basic(&sum(&algebra, &[&s0, &s1])),
                support(&algebra, &[]),
            )
            .expect("A_2 translates"),
        );
        assert_eq!(rigid.condition(), 3);
        match &rigid {
            PairRejection::NotTauRigid(witness) => {
                assert_eq!(witness.translate().dim_vector(), &[0, 1]);
                assert!(witness.verify());
            }
            other => panic!("expected a tau-rigidity failure, got {other}"),
        }

        let count = expect_rejection(
            SupportTauTiltingPair::classify(basic(&Module::zero(&algebra)), support(&algebra, &[]))
                .expect("the zero module needs no translate"),
        );
        assert_eq!(count.condition(), 4);
        assert!(matches!(
            count,
            PairRejection::SummandCount {
                module: 0,
                projective: 0,
                expected: 2
            }
        ));
    }
}

// Over A_2 with the arrow 0 -> 1 the candidate (P_0, {1}) has
// |M| + |P| = 2 = n and a tau-rigid module part, so only condition 2
// separates it from a pair. Under the right-module convention
// Hom(P_v, X) = X_v, so Hom(P_1, P_0) has dimension (P_0)_1 = 1 and the
// candidate is rejected. The left-module formula pairs P_1 with the other
// side and would admit it, which would turn the pentagon into a hexagon.
#[test]
fn the_a2_near_miss_is_rejected_by_the_right_module_hom_condition() {
    for field in fields() {
        let algebra = linear_an(2, field);
        let p0 = Module::projective(&algebra, 0);
        // Condition 4 holds on its own.
        assert_eq!(basic(&p0).len() + support(&algebra, &[1]).len(), 2);
        // Condition 3 holds on its own: P_0 is projective, so tau P_0 = 0.
        let alone = expect_pair(
            SupportTauTiltingPair::classify(
                basic(&sum(&algebra, &[&p0, &Module::simple(&algebra, 0)])),
                support(&algebra, &[]),
            )
            .expect("A_2 translates"),
        );
        assert!(alone.verify());
        let rejection = expect_rejection(
            SupportTauTiltingPair::classify(basic(&p0), support(&algebra, &[1]))
                .expect("A_2 translates"),
        );
        assert_eq!(rejection.condition(), 2);
        match rejection {
            PairRejection::HomFromProjectiveNonzero { vertex, dim } => {
                assert_eq!((vertex, dim), (1, 1));
                // The stored dimension is the live Hom dimension.
                assert_eq!(
                    hom_dim(&Module::projective(&algebra, vertex), &p0).unwrap(),
                    dim,
                    "over F_{}",
                    field.modulus()
                );
            }
            other => panic!("the right-module condition must fire here, got {other}"),
        }
    }
}

// The A_2 pentagon, listed by hand. The catalog is S_0 = (1, 0),
// S_1 = P_1 = (0, 1), P_0 = (1, 1), with tau S_0 = S_1 the only nonzero
// translate. A subset is tau-rigid unless it holds both S_0 and S_1, and
// Hom(P_v, M) = 0 forces the support of P to avoid the support of M, so
// P is the complement of supp M and exists only when its size is n - |M|:
//
//   |M| = 0: M = 0,            P = {0, 1}
//   |M| = 1: M = S_0,          P = {1}
//   |M| = 1: M = S_1,          P = {0}
//   |M| = 1: M = P_0,          supp M = {0, 1} leaves no room for P
//   |M| = 2: M = S_0 + P_0,    P = {}
//   |M| = 2: M = S_1 + P_0,    P = {}
//   |M| = 2: M = S_0 + S_1,    not tau-rigid
//
// Five pairs, with the histogram [1, 2, 2] by module-summand count.
#[test]
fn the_a2_pentagon_lists_five_pairs_by_dimension_vector() {
    for field in fields() {
        let algebra = linear_an(2, field);
        let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_2 is Dynkin");
        let enumeration = enumerate_over_catalog(&catalog).expect("A_2 enumerates");
        let mut listed: Vec<(Vec<Vec<usize>>, Vec<u32>)> = enumeration
            .pairs()
            .iter()
            .map(|pair| {
                (
                    pair.module().dim_vectors(),
                    pair.projective().vertices().to_vec(),
                )
            })
            .collect();
        listed.sort();
        assert_eq!(
            listed,
            vec![
                (vec![], vec![0, 1]),
                (vec![vec![0, 1]], vec![0]),
                (vec![vec![0, 1], vec![1, 1]], vec![]),
                (vec![vec![1, 0]], vec![1]),
                (vec![vec![1, 0], vec![1, 1]], vec![]),
            ],
            "over F_{}",
            field.modulus()
        );
        assert_eq!(enumeration.len(), 5);
        assert_eq!(enumeration.histogram(), vec![1, 2, 2]);
        // Two of the five have an empty projective part.
        assert_eq!(
            enumeration
                .pairs()
                .iter()
                .filter(|pair| pair.is_tau_tilting())
                .count(),
            2
        );
        assert!(enumeration.verify());
    }
}
