use super::*;

// The counts three independent sources agree on: the mathematics spike by
// hand, the cost spike by brute force, and the QPA capability spike in
// GAP. `docs/support-tau-tilting.md` section 10 records them.
//
// Hand derivations for the small fixtures:
//
// Semisimple on n vertices. Every indecomposable is a simple, which is
// also projective, so tau is zero and every subset is tau-rigid. The
// support of M is the set of chosen vertices, so P is forced to be its
// complement and always has the required size n - |M|. Pairs correspond
// to subsets: 2^n, that is 4, 8, and 16 on 2, 3, and 4 vertices.
//
// truncated_poly(3) = k[x]/(x^3). The indecomposables are the uniserials
// U_1, U_2, U_3 = A, and tau U_m = U_m for m = 1, 2, with
// dim Hom(U_m, U_m) = m > 0, so U_1 and U_2 are not tau-rigid alone. The
// tau-rigid subsets are {} and {A}, giving (0, A) and (A, 0): 2 pairs.
//
// linear_an(2) is the pentagon derived in
// `the_a2_pentagon_lists_five_pairs_by_dimension_vector`.
//
// linear_an(3): the Catalan number C_4 = 14. Writing the interval module
// on vertices a to b as [a, b], the six indecomposables are [0,0], [1,1],
// [2,2], [0,1], [1,2], [0,2], with Hom([a,b],[c,d]) nonzero exactly when
// c <= a <= d <= b, and tau [a,b] = [a+1, b+1] except at b = 2, where the
// module is projective. The five forbidden co-occurrences are
// {[1,1],[0,0]}, {[1,2],[0,0]}, {[2,2],[1,1]}, {[1,2],[0,1]},
// {[2,2],[0,1]}, a 5-cycle on the five non-regular entries with [0,2]
// isolated. Counting independent sets against the room left for P gives
// 1 + 3 + 5 + 5 = 14 by module-summand count.
//
// linear_nakayama([2, 2, 1]) is kA_3/(ab), with the five intervals [0,0],
// [1,1], [2,2], [0,1], [1,2]. Here tau [0,0] = [1,1] and tau [1,1] =
// [2,2], so the forbidden co-occurrences are {[1,1],[0,0]},
// {[1,2],[0,0]}, {[2,2],[1,1]}: a path with [0,1] isolated. The counts by
// module-summand count are 1 + 3 + 5 + 3 = 12.
//
// radical_square_zero_cycle(3) has the three simples S_v and the three
// projectives P_v of dimension vector supported on {v, v+1}. It is
// self-injective with tau S_v = S_{v+1}, and Hom(X, S_w) is nonzero
// exactly when top X = S_w, so the forbidden co-occurrences are
// {S_v, S_{v+1}} and {S_v, P_{v+1}}. The counts by module-summand count
// are 1 + 3 + 6 + 4 = 14.
//
// D_4 with zero relations is the W-Catalan number 50, with the histogram
// [1, 4, 9, 16, 20]. Its own test keeps it separate.
#[test]
fn the_enumerated_counts_are_pinned() {
    let expected: Vec<(&str, usize, Vec<usize>)> = vec![
        ("semisimple(2)", 4, vec![1, 2, 1]),
        ("semisimple(3)", 8, vec![1, 3, 3, 1]),
        ("semisimple(4)", 16, vec![1, 4, 6, 4, 1]),
        ("linear_an(2)", 5, vec![1, 2, 2]),
        ("linear_an(3)", 14, vec![1, 3, 5, 5]),
        ("truncated_poly(3)", 2, vec![1, 1]),
        ("radical_square_zero_cycle(3)", 14, vec![1, 3, 6, 4]),
        ("linear_nakayama([2, 2, 1])", 12, vec![1, 3, 5, 3]),
    ];
    for field in fields() {
        let fixtures = catalog_fixtures(field);
        assert_eq!(fixtures.len(), expected.len());
        for ((name, catalog), (short, count, histogram)) in fixtures.iter().zip(&expected) {
            assert!(name.starts_with(short), "{name} is not {short}");
            let enumeration = enumerate_over_catalog(catalog).expect("the fixture enumerates");
            assert_eq!(enumeration.len(), *count, "{name}");
            assert_eq!(&enumeration.histogram(), histogram, "{name}");
            assert_eq!(enumeration.provenance(), catalog.provenance());
            assert_eq!(enumeration.catalog_len(), catalog.len());
            assert!(!enumeration.is_empty());
            assert!(enumeration.verify(), "{name}");
        }
    }
}
// The walk visits exactly the tau-rigid subsets of at most n entries,
// because tau-rigidity is inherited by subsets: every prefix of a
// tau-rigid subset in index order is tau-rigid, so the subset is reached,
// and the count bound stops the descent at n. The brute-force count is
// computed with an uncached tau and no pruning, so it shares nothing with
// the walk.
#[test]
fn the_dfs_node_count_is_the_number_of_tau_rigid_subsets() {
    let expected = [
        ("semisimple(2)", 4usize),
        ("semisimple(3)", 8),
        ("semisimple(4)", 16),
        ("linear_an(2)", 6),
        ("linear_an(3)", 22),
        ("truncated_poly(3)", 2),
        ("radical_square_zero_cycle(3)", 20),
        ("linear_nakayama([2, 2, 1])", 16),
    ];
    for field in fields() {
        for ((name, catalog), (short, nodes)) in catalog_fixtures(field).iter().zip(&expected) {
            assert!(name.starts_with(short), "{name} is not {short}");
            let enumeration = enumerate_over_catalog(catalog).expect("the fixture enumerates");
            let (count, histogram, brute_nodes) = brute_force(catalog);
            assert_eq!(enumeration.nodes_visited(), *nodes, "{name}");
            assert_eq!(enumeration.nodes_visited(), brute_nodes, "{name}");
            assert_eq!(enumeration.len(), count, "{name}");
            assert_eq!(enumeration.histogram(), histogram, "{name}");
        }
    }
}

// D_4 with zero relations: 50 pairs with the histogram [1, 4, 9, 16, 20]
// by module-summand count, from the three sources of section 10. The
// catalog has 12 entries, one per positive root of D_4. The node count is
// the number of tau-rigid subsets of at most four entries, cross-checked
// here against the brute-force walk over all 4096 subsets.
#[test]
fn the_d4_enumeration_has_fifty_pairs() {
    for field in fields() {
        let algebra = d4(field);
        let catalog = IndecomposableCatalog::dynkin(&algebra).expect("D_4 is Dynkin");
        assert_eq!(catalog.len(), 12);
        let enumeration = enumerate_over_catalog(&catalog).expect("D_4 enumerates");
        assert_eq!(enumeration.len(), 50, "over F_{}", field.modulus());
        assert_eq!(enumeration.histogram(), vec![1, 4, 9, 16, 20]);
        let (count, histogram, nodes) = brute_force(&catalog);
        assert_eq!(count, 50);
        assert_eq!(histogram, vec![1, 4, 9, 16, 20]);
        // 120 tau-rigid subsets of at most four entries, which is what the
        // walk visits. The brute-force run recounts them over all 4096
        // subsets, so the literal is pinned by two routes.
        assert_eq!(enumeration.nodes_visited(), 120);
        assert_eq!(enumeration.nodes_visited(), nodes);
        assert_eq!(enumeration.provenance(), CatalogProvenance::DynkinZeroIdeal);
        assert!(enumeration.verify(), "over F_{}", field.modulus());
    }
}

// Both catalog constructors reject the Kronecker algebra, which is
// tau-tilting infinite, so no enumeration is attempted over it. There is
// no route from an algebra to a CatalogEnumeration that skips a catalog.
#[test]
fn the_kronecker_algebra_has_no_catalog() {
    for field in fields() {
        let algebra = kronecker(2, field);
        assert_eq!(
            IndecomposableCatalog::nakayama(&algebra).unwrap_err(),
            EnumerateError::NotNakayama {
                vertex: 0,
                incoming: 0,
                outgoing: 2
            }
        );
        assert!(matches!(
            IndecomposableCatalog::dynkin(&algebra).unwrap_err(),
            DynkinError::NotDynkin { .. }
        ));
    }
}
