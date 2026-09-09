use super::*;

// A duplicated vertex must not pass verification, which is clause 2 of the
// closure obligations in `docs/support-tau-tilting.md` section 8. The duplicate is
// built separately through the checking constructor, so every pair in the
// list verifies on its own and only the pairwise-distinctness loop can
// catch it.
//
// The two indices are the ends of the A_2 pentagon in the walk order
// `CatalogEnumeration::pairs` documents, module subsets in lexicographic
// order over catalog positions and supports lexicographic within a subset.
// The empty subset comes first, so pair 0 is (0, {0, 1}), and the last
// subset gives pair 4, which is (S_0 + P_0, {}). Both shapes are asserted
// below. The empty module part exercises the distinctness loop where
// pair_iso has no summand to match.
#[test]
fn a_duplicated_pair_fails_verification() {
    let field = f5();
    let algebra = linear_an(2, field);
    let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_2 is Dynkin");
    for (index, dim_vectors, vertices) in [
        (0usize, Vec::new(), vec![0u32, 1]),
        (4, vec![vec![1, 0], vec![1, 1]], Vec::new()),
    ] {
        let mut enumeration = enumerate_over_catalog(&catalog).expect("A_2 enumerates");
        assert_eq!(enumeration.len(), 5);
        assert!(enumeration.verify());
        let duplicate = {
            let pair = &enumeration.pairs()[index];
            assert_eq!(pair.module().dim_vectors(), dim_vectors);
            assert_eq!(pair.projective().vertices(), vertices);
            let module = BasicDecomposition::new(pair.module().module())
                .expect("the module part of a pair is basic");
            let projective = ProjectiveSupport::new(&algebra, pair.projective().vertices())
                .expect("the support of a pair is in range");
            SupportTauTiltingPair::new(module, projective)
                .expect("A_2 translates")
                .expect("a rebuilt pair is a pair")
        };
        assert!(duplicate.verify(), "the duplicate is honest on its own");
        enumeration.pairs.push(duplicate);
        assert_eq!(enumeration.len(), 6);
        assert!(!enumeration.verify(), "a duplicate of pair {index} passed");
    }
}

// The almost complete side of `a_tampered_pair_fails_verification`, on the
// (P_0 + P_1, 0) fixture of
// `the_two_pair_types_reject_each_other_on_the_count`.
#[test]
fn a_tampered_almost_complete_pair_fails_verification() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let p2 = Module::projective(&algebra, 2);
        let two = sum(&algebra, &[&p0, &p1]);
        let almost = |m: &Module| {
            AlmostCompletePair::new(basic(m), support(&algebra, &[]))
                .expect("A_3 translates")
                .expect("a sum of two projectives is almost complete")
        };
        let pair = almost(&two);
        assert!(pair.verify());
        // P_0 + P_1 has dimension vector (1, 2, 2), so s = 3 = r + 1 and
        // the support complement is empty. P is the whole complement, and
        // no vertex is omitted.
        assert_eq!(pair.module().module().dim_vector(), &[1, 2, 2]);
        assert_eq!(pair.omitted_vertex(), None);
        assert!(pair.projective().is_empty());

        // P_1 + P_2 has dimension vector (0, 1, 2), so s = 2 = r and the
        // complement is {0}. P is the complement minus one vertex, which
        // leaves it empty and records the omission.
        let donor = almost(&sum(&algebra, &[&p1, &p2]));
        assert!(donor.verify(), "the donor is honest");
        assert_eq!(donor.module().module().dim_vector(), &[0, 1, 2]);
        assert_eq!(donor.omitted_vertex(), Some(0));
        assert!(donor.projective().is_empty());

        // An omitted vertex outside the support complement. Vertex 1 is in
        // the support of P_1 + P_2, so it is not the crate's to omit, and
        // claiming it leaves the derived support one vertex too long.
        let mut moved = almost(&sum(&algebra, &[&p1, &p2]));
        moved.omitted = Some(1);
        assert!(!moved.verify());

        // A tau-rigidity witness from the same donor. Both parts have two
        // summands, so the length check passes and the summand identity
        // check is what fails.
        let mut forged = almost(&two);
        assert_eq!(
            donor.rigid().summands().len(),
            forged.rigid.summands().len()
        );
        forged.rigid = donor.rigid().clone();
        assert!(!forged.verify(), "over F_{}", field.modulus());
    }
}
