use super::*;

// Two separately built copies of (P_0 + P_2, P_1) over A_3. Both sides
// decompose in the order `the_decomposition_order_is_pinned` fixes, so
// the greedy scan of pair_iso matches summand i to summand i and the
// bijection is the identity.
#[test]
fn a_pair_is_isomorphic_to_a_fresh_copy_of_itself() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let first = basic(&sum(&[&p0, &p2]));
        let second = basic(&sum(&[&p0, &p2]));
        let s = support(&algebra, &[1]);
        let witness = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
        assert!(witness.verify());
        assert_eq!(witness.bijection(), &[0, 1], "over F_{}", field.modulus());
        assert_eq!(witness.forward().len(), 2);
        assert_eq!(witness.backward().len(), 2);
    }
}

// `docs/support-tau-tilting.md` section 14 requires every stored witness to be
// deterministic across processes and platforms, so the order the summands
// come out in is part of the contract. The order is not hand-derivable:
// `decompose` splits with a Fitting-lemma recursion seeded per call
// (`DECOMPOSE_SEED`), and `krull_schmidt` lists classes in the order that
// recursion first produced them. It is exact linear algebra over F_p with
// no wall-clock and no thread input, so the order is reproducible. This
// test is the snapshot that catches a change in it.
//
// On these fixtures the recursion returns the summands in the reverse of
// the assembly order: P_0 + P_2 comes out as [0, 0, 1] then [1, 1, 1],
// P_2 + P_0 comes out the other way, and the regular module
// P_0 + P_1 + P_2 comes out as [0, 0, 1], [0, 1, 1], [1, 1, 1]. That
// reversal is what the current recursion does on these inputs, not a rule
// the type promises.
#[test]
fn the_decomposition_order_is_pinned() {
    fn order(d: &BasicDecomposition) -> Vec<Vec<usize>> {
        d.summands()
            .iter()
            .map(|x| x.module().dim_vector().to_vec())
            .collect()
    }
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let p2 = Module::projective(&algebra, 2);
        let context = format!("over F_{}", field.modulus());
        assert_eq!(
            order(&basic(&sum(&[&p0, &p2]))),
            vec![vec![0, 0, 1], vec![1, 1, 1]],
            "P_0 + P_2 {context}"
        );
        assert_eq!(
            order(&basic(&sum(&[&p2, &p0]))),
            vec![vec![1, 1, 1], vec![0, 0, 1]],
            "P_2 + P_0 {context}"
        );
        assert_eq!(
            order(&basic(&sum(&[&p0, &p1, &p2]))),
            vec![vec![0, 0, 1], vec![0, 1, 1], vec![1, 1, 1]],
            "the regular module {context}"
        );
        // A second decomposition of the same module repeats the order, so
        // nothing carries over from one call to the next.
        assert_eq!(
            order(&basic(&sum(&[&p0, &p2]))),
            order(&basic(&sum(&[&p0, &p2]))),
            "two calls {context}"
        );
    }
}

// The bijection of a SupportPairIsoWitness is deterministic for the same
// reason: both decomposition orders are pinned, and pair_iso scans the
// summands of the second module in order and takes the first match.
//
// P_0 + P_2 against a fresh P_0 + P_2: both decompose as [0, 0, 1] then
// [1, 1, 1], and no summand of A_3 matches two of them, so the bijection
// is [0, 1]. P_0 + P_2 against P_2 + P_0: the second decomposes as
// [1, 1, 1] then [0, 0, 1], so summand 0 of the first, [0, 0, 1], matches
// summand 1 of the second and the bijection is [1, 0].
#[test]
fn the_pair_iso_bijection_is_pinned() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let s = support(&algebra, &[1]);
        let first = basic(&sum(&[&p0, &p2]));
        let same = basic(&sum(&[&p0, &p2]));
        let reversed = basic(&sum(&[&p2, &p0]));
        assert_eq!(first.summands()[0].module().dim_vector(), &[0, 0, 1]);
        assert_eq!(reversed.summands()[0].module().dim_vector(), &[1, 1, 1]);
        let witness = expect_witness(pair_iso(&first, &s, &same, &s).unwrap());
        assert!(witness.verify());
        assert_eq!(witness.bijection(), &[0, 1], "over F_{}", field.modulus());
        let swapped = expect_witness(pair_iso(&first, &s, &reversed, &s).unwrap());
        assert!(swapped.verify());
        assert_eq!(swapped.bijection(), &[1, 0], "over F_{}", field.modulus());
    }
}

// Reversing the summand order changes nothing: identity is isomorphism.
#[test]
fn a_pair_is_isomorphic_to_its_summands_in_the_other_order() {
    let algebra = linear_an(3, f5());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let first = basic(&sum(&[&p0, &p1]));
    let second = basic(&sum(&[&p1, &p0]));
    let s = support(&algebra, &[2]);
    let witness = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
    assert!(witness.verify());
}

#[test]
fn a_different_projective_support_is_an_obstruction() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let module = basic(&Module::projective(&algebra, 0));
        let other = basic(&Module::projective(&algebra, 0));
        let left = support(&algebra, &[1]);
        let right = support(&algebra, &[2]);
        assert_eq!(
            expect_obstruction(pair_iso(&module, &left, &other, &right).unwrap()),
            SupportPairObstruction::ProjectiveSupport {
                first: vec![1],
                second: vec![2]
            }
        );
    }
}

#[test]
fn a_different_summand_count_is_an_obstruction() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let two = basic(&sum(&[&p0, &p2]));
        let one = basic(&p0);
        let s = support(&algebra, &[1]);
        assert_eq!(
            expect_obstruction(pair_iso(&two, &s, &one, &s).unwrap()),
            SupportPairObstruction::SummandCount {
                first: 2,
                second: 1
            }
        );
    }
}

// P_0 + P_2 against P_0 + P_1: both have two summands and the same
// support, and P_2 = [0, 0, 1] matches neither P_0 nor P_1.
#[test]
fn an_unmatched_summand_is_an_obstruction() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let p2 = Module::projective(&algebra, 2);
        let left = basic(&sum(&[&p0, &p2]));
        let right = basic(&sum(&[&p0, &p1]));
        let s = support(&algebra, &[1]);
        let obstruction = expect_obstruction(pair_iso(&left, &s, &right, &s).unwrap());
        match obstruction {
            SupportPairObstruction::UnmatchedSummand { index, dim_vector } => {
                assert_eq!(left.summands()[index].module().dim_vector(), &[0, 0, 1]);
                assert_eq!(dim_vector, vec![0, 0, 1]);
            }
            other => panic!("expected an unmatched summand, got {other:?}"),
        }
    }
}

#[test]
fn a_tampered_bijection_fails_verification() {
    let algebra = linear_an(3, f5());
    let p0 = Module::projective(&algebra, 0);
    let p2 = Module::projective(&algebra, 2);
    let first = basic(&sum(&[&p0, &p2]));
    let second = basic(&sum(&[&p0, &p2]));
    let s = support(&algebra, &[1]);
    let mut witness = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
    assert!(witness.verify());
    // Two summands sent to one target is not a permutation.
    witness.bijection = vec![0, 0];
    assert!(!witness.verify());
    // A dropped map leaves fewer isomorphisms than bijection entries.
    let mut short = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
    short.forward.pop();
    assert!(!short.verify());
}

#[test]
fn a_tampered_isomorphism_fails_verification() {
    let algebra = linear_an(3, f5());
    let p0 = Module::projective(&algebra, 0);
    let first = basic(&p0);
    let second = basic(&Module::projective(&algebra, 0));
    let s = support(&algebra, &[1]);
    let mut witness = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
    // Replacing the inverse by the forward map breaks the composite,
    // since the two run in opposite directions.
    witness.backward = witness.forward.clone();
    assert!(!witness.verify());
}

#[test]
fn mismatched_algebras_are_rejected() {
    let algebra = linear_an(3, f5());
    let other = linear_an(3, f5());
    let first = basic(&Module::projective(&algebra, 0));
    let second = basic(&Module::projective(&other, 0));
    let left = support(&algebra, &[1]);
    let right = support(&other, &[1]);
    assert_eq!(
        pair_iso(&first, &left, &second, &right).unwrap_err(),
        BasicError::DifferentAlgebras
    );
    assert_eq!(
        PairFingerprint::new(&first, &right).unwrap_err(),
        BasicError::DifferentAlgebras
    );
    assert_eq!(
        AddClosureWitness::new(&first, &second).unwrap_err(),
        BasicError::DifferentAlgebras
    );
}

// D_4 pairs: the module halves agree and the projective halves differ,
// then both halves agree.
#[test]
fn pair_identity_works_over_d4() {
    for field in fields() {
        let algebra = d4(field);
        let p0 = Module::projective(&algebra, 0);
        let s1 = Module::simple(&algebra, 1);
        let first = basic(&sum(&[&p0, &s1]));
        let second = basic(&sum(&[&s1, &p0]));
        let left = support(&algebra, &[2, 3]);
        let right = support(&algebra, &[3]);
        assert_eq!(
            expect_obstruction(pair_iso(&first, &left, &second, &right).unwrap()),
            SupportPairObstruction::ProjectiveSupport {
                first: vec![2, 3],
                second: vec![3]
            }
        );
        let witness = expect_witness(pair_iso(&first, &left, &second, &left).unwrap());
        assert!(witness.verify());
        assert_eq!(
            PairFingerprint::new(&first, &left).unwrap(),
            PairFingerprint::new(&second, &left).unwrap()
        );
    }
}
