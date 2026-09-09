use super::*;

// Over linearly oriented A_3 write M[i, j] for the module supported on
// the interval i..=j. Then dim Hom(M[i, j], M[k, l]) is 1 when
// k <= i <= l <= j and 0 otherwise, and every nonzero map is the identity
// on the overlap. Two hand-checked consequences:
//
// - The top projection P_0 = M[0, 2] -> S_0 = M[0, 0] is the composite of
//   the two surjections M[0, 2] -> M[0, 1] -> M[0, 0], so it lies in
//   rad^2 and Irr(P_0, S_0) is zero.
// - The surjection M[0, 2] -> M[0, 1] does not factor: the only modules Z
//   with rad(M[0, 2], Z) and rad(Z, M[0, 1]) both nonzero are M[0, 1]
//   itself and M[0, 0], and both routes compose to zero, so
//   Irr(P_0, M[0, 1]) is a line.
#[test]
fn the_radical_square_on_linear_a3_matches_the_hand_checked_factorizations() {
    for field in [f2(), f5()] {
        let algebra = linear_an(3, field);
        let catalog = IndecomposableCatalog::dynkin(&algebra).unwrap();
        let p0 = indec(&Module::projective(&algebra, 0));
        let s0 = indec(&Module::simple(&algebra, 0));
        let m01 = indec(&Module::injective(&algebra, 1));
        assert_eq!(m01.module().dim_vector(), [1, 1, 0]);

        assert_eq!(category_radical(&p0, &s0).unwrap().dim(), 1);
        assert_eq!(
            radical_square_through_catalog(&catalog, &p0, &s0)
                .unwrap()
                .dim(),
            1
        );
        assert_eq!(irreducible_quotient(&catalog, &p0, &s0).unwrap().dim(), 0);

        assert_eq!(category_radical(&p0, &m01).unwrap().dim(), 1);
        assert_eq!(
            radical_square_through_catalog(&catalog, &p0, &m01)
                .unwrap()
                .dim(),
            0
        );
        assert_eq!(irreducible_quotient(&catalog, &p0, &m01).unwrap().dim(), 1);
    }
}

// Linearly oriented A_3 with the zero ideal, hand-derived from the Hom
// rule above. The six indecomposables are the interval modules, and the
// catalog lists them by root height then lexicographically:
//
//   0: (0,0,1) = S_2 = P_2   3: (0,1,1) = P_1
//   1: (0,1,0) = S_1         4: (1,1,0) = I_1
//   2: (1,0,0) = S_0 = I_0   5: (1,1,1) = P_0 = I_2
//
// Deleting from each nonzero rad(X, Y) the ones that factor leaves six
// arrows, the classical zigzag: P_2 -> P_1 -> P_0 along the projectives,
// P_1 -> S_1 -> I_1 and P_0 -> I_1 -> S_0. The meshes confirm it:
// 0 -> S_2 -> P_1 -> S_1 -> 0, 0 -> P_1 -> S_1 + P_0 -> I_1 -> 0 and
// 0 -> S_1 -> I_1 -> S_0 -> 0 are the three almost-split sequences, and
// the three projectives receive one arrow each from their radical.
#[test]
fn linear_a3_has_the_hand_derived_zigzag_ar_quiver() {
    for field in [f2(), f5()] {
        let algebra = linear_an(3, field);
        let quiver = ar_quiver(&algebra).unwrap();
        assert_eq!(
            quiver.catalog().provenance(),
            CatalogProvenance::DynkinZeroIdeal
        );
        assert_eq!(
            dim_vectors(&quiver),
            vec![
                vec![0, 0, 1],
                vec![0, 1, 0],
                vec![1, 0, 0],
                vec![0, 1, 1],
                vec![1, 1, 0],
                vec![1, 1, 1],
            ]
        );
        assert_eq!(
            flags(&quiver),
            vec![
                (true, false),
                (false, false),
                (false, true),
                (true, false),
                (false, true),
                (true, true),
            ]
        );
        assert_eq!(
            arrow_triples(&quiver),
            vec![
                (0, 3, 1),
                (1, 4, 1),
                (3, 1, 1),
                (3, 5, 1),
                (4, 2, 1),
                (5, 4, 1),
            ]
        );
    }
}

// k[x]/(x^3) is Nakayama with one vertex, so the catalog is
// M_1, M_2, M_3 by length. Hom(M_i, M_j) has dimension min(i, j), the
// radical of End(M_i) is multiplication by x, and every map M_i -> M_j
// sends 1 to an element killed by x^i. Hand-checking the four candidate
// arrows: M_1 -> M_2 and M_2 -> M_1 do not factor, M_2 -> M_3 has
// rad(M_2, M_3) of dimension 2 with a one-dimensional square, and
// M_1 -> M_3 factors through M_2, so its Irr is zero. The AR sequences
// are 0 -> M_1 -> M_2 -> M_1 -> 0 and 0 -> M_2 -> M_1 + M_3 -> M_2 -> 0,
// and M_3 is projective-injective.
#[test]
fn truncated_poly_3_has_the_ar_quiver_of_k_x_mod_x_cubed() {
    for field in [f2(), f5()] {
        let algebra = truncated_poly(3, field).unwrap();
        let quiver = ar_quiver(&algebra).unwrap();
        assert_eq!(quiver.catalog().provenance(), CatalogProvenance::Nakayama);
        assert_eq!(dim_vectors(&quiver), vec![vec![1], vec![2], vec![3]]);
        assert_eq!(
            flags(&quiver),
            vec![(false, false), (false, false), (true, true)]
        );
        assert_eq!(
            arrow_triples(&quiver),
            vec![(0, 1, 1), (1, 0, 1), (1, 2, 1), (2, 1, 1)]
        );
    }
}

// The cyclic quiver on three vertices with rad^2 = 0 is a self-injective
// Nakayama algebra of dimension 6. Every projective P_i has top S_i and
// socle S_{i+1}, so the six indecomposables are the three simples and the
// three projectives, listed by the enumerator as S_0, P_0, S_1, P_1,
// S_2, P_2. The Loewy length is 2, so the only almost-split sequences are
// 0 -> S_{i+1} -> P_i -> S_i -> 0, giving the arrows S_{i+1} -> P_i and
// P_i -> S_i, six in all: a hexagon.
#[test]
fn the_radical_square_zero_3_cycle_has_a_hexagonal_ar_quiver() {
    for field in [f2(), f5()] {
        let algebra = radical_square_zero_cycle(3, field);
        let quiver = ar_quiver(&algebra).unwrap();
        assert_eq!(quiver.catalog().provenance(), CatalogProvenance::Nakayama);
        assert_eq!(
            dim_vectors(&quiver),
            vec![
                vec![1, 0, 0],
                vec![1, 1, 0],
                vec![0, 1, 0],
                vec![0, 1, 1],
                vec![0, 0, 1],
                vec![1, 0, 1],
            ]
        );
        assert_eq!(
            flags(&quiver),
            vec![
                (false, false),
                (true, true),
                (false, false),
                (true, true),
                (false, false),
                (true, true),
            ]
        );
        assert_eq!(
            arrow_triples(&quiver),
            vec![
                (0, 5, 1),
                (1, 0, 1),
                (2, 1, 1),
                (3, 2, 1),
                (4, 3, 1),
                (5, 4, 1),
            ]
        );
    }
}

// D_4 oriented away from the branch vertex 0: arrows 0 -> 1, 0 -> 2,
// 0 -> 3. Then P_0 = (1,1,1,1) with rad P_0 = S_1 + S_2 + S_3, the
// leaves are simple projective, and the injectives are S_0 and the three
// (1, ..., 1, ...) modules. Knitting from the three simple projectives:
//
//   S_i -> P_0 (three arrows into the projective from its radical),
//   0 -> S_i -> P_0 -> (1,1,1,1) - S_i -> 0,
//   0 -> P_0 -> sum of those three -> (2,1,1,1) -> 0,
//   0 -> (1,1,1,1) - S_i -> (2,1,1,1) -> I_i -> 0,
//   0 -> (2,1,1,1) -> I_1 + I_2 + I_3 -> S_0 -> 0.
//
// That is 12 vertices and 15 arrows, with a three-arrow star in and a
// three-arrow star out at both (1,1,1,1) and (2,1,1,1).
#[test]
fn d4_oriented_away_from_the_branch_vertex_has_15_arrows_and_two_stars() {
    let algebra = d4(f2());
    let quiver = ar_quiver(&algebra).unwrap();
    assert_eq!(quiver.vertices().len(), 12);
    assert_eq!(quiver.arrows().len(), 15);
    assert_eq!(
        dim_vectors(&quiver),
        vec![
            vec![0, 0, 0, 1],
            vec![0, 0, 1, 0],
            vec![0, 1, 0, 0],
            vec![1, 0, 0, 0],
            vec![1, 0, 0, 1],
            vec![1, 0, 1, 0],
            vec![1, 1, 0, 0],
            vec![1, 0, 1, 1],
            vec![1, 1, 0, 1],
            vec![1, 1, 1, 0],
            vec![1, 1, 1, 1],
            vec![2, 1, 1, 1],
        ]
    );
    assert_eq!(
        arrow_triples(&quiver),
        vec![
            (0, 10, 1),
            (1, 10, 1),
            (2, 10, 1),
            (4, 3, 1),
            (5, 3, 1),
            (6, 3, 1),
            (7, 11, 1),
            (8, 11, 1),
            (9, 11, 1),
            (10, 7, 1),
            (10, 8, 1),
            (10, 9, 1),
            (11, 4, 1),
            (11, 5, 1),
            (11, 6, 1),
        ]
    );
    let star_in = |id: usize| -> Vec<usize> {
        quiver
            .arrows()
            .iter()
            .filter(|a| a.target() == id)
            .map(|a| a.source())
            .collect()
    };
    let star_out = |id: usize| -> Vec<usize> {
        quiver
            .arrows()
            .iter()
            .filter(|a| a.source() == id)
            .map(|a| a.target())
            .collect()
    };
    assert_eq!(star_in(10), vec![0, 1, 2]);
    assert_eq!(star_out(10), vec![7, 8, 9]);
    assert_eq!(star_in(11), vec![7, 8, 9]);
    assert_eq!(star_out(11), vec![4, 5, 6]);
    assert!(quiver.vertices()[10].projective());
    assert!(!quiver.vertices()[11].projective());
    assert!(!quiver.vertices()[11].injective());
}

fn catalog_fixtures() -> Vec<Arc<Algebra>> {
    vec![
        linear_an(3, f5()),
        linear_an(4, f2()),
        truncated_poly(3, f2()).unwrap(),
        truncated_poly(4, f5()).unwrap(),
        radical_square_zero_cycle(3, f5()),
        cyclic_nakayama(&[3, 3, 3], f2()).unwrap(),
        d4(f2()),
    ]
}

// Every indecomposable over these algebras is a brick or a uniserial
// module with endomorphism algebra local of residue degree 1, so every
// arrow valuation is plain.
#[test]
fn every_arrow_on_the_catalog_domains_is_plain() {
    for algebra in catalog_fixtures() {
        let quiver = ar_quiver(&algebra).unwrap();
        for vertex in quiver.vertices() {
            assert_eq!(
                vertex.residue_degree(),
                1,
                "vertex {} of a catalog domain",
                vertex.id()
            );
        }
        for arrow in quiver.arrows() {
            assert!(arrow.base_dim() > 0);
            assert_eq!(arrow.over_source_residue(), arrow.base_dim());
            assert_eq!(arrow.over_target_residue(), arrow.base_dim());
            assert_eq!(arrow.valuation(), ArrowValuation::Plain(arrow.base_dim()));
            assert_eq!(arrow.representatives().len(), arrow.base_dim());
        }
    }
}

#[test]
fn arrow_representatives_are_radical_maps_outside_the_radical_square() {
    for algebra in [linear_an(3, f5()), truncated_poly(3, f2()).unwrap()] {
        let quiver = ar_quiver(&algebra).unwrap();
        let catalog = quiver.catalog();
        for arrow in quiver.arrows() {
            let x = &catalog.entries()[arrow.source()];
            let y = &catalog.entries()[arrow.target()];
            let radical = category_radical(x, y).unwrap();
            let square = radical_square_through_catalog(catalog, x, y).unwrap();
            for f in arrow.representatives() {
                assert!(radical.contains(f).unwrap());
                assert!(!square.contains(f).unwrap());
            }
        }
    }
}

// A positive-dimensional algebra has one simple module per vertex, and
// both enumerations list all of them, so no catalog is ever empty.
#[test]
fn every_catalog_has_at_least_one_entry_per_vertex() {
    for algebra in catalog_fixtures() {
        let quiver = ar_quiver(&algebra).unwrap();
        let vertices = algebra.quiver().num_vertices() as usize;
        assert!(quiver.catalog().len() >= vertices);
        assert!(!quiver.catalog().is_empty());
        assert_eq!(quiver.vertices().len(), quiver.catalog().len());
        assert!(Arc::ptr_eq(quiver.catalog().algebra(), &algebra));
        for (id, vertex) in quiver.vertices().iter().enumerate() {
            assert_eq!(vertex.id(), id);
            assert!(
                vertex
                    .module()
                    .module()
                    .ptr_eq(quiver.catalog().entries()[id].module())
            );
        }
    }
}

#[test]
fn the_catalog_constructors_reject_the_other_route() {
    let nakayama = truncated_poly(3, f5()).unwrap();
    assert_eq!(
        IndecomposableCatalog::dynkin(&nakayama).unwrap_err(),
        DynkinError::NonzeroIdeal { relations: 1 }
    );
    let dynkin = d4(f5());
    assert_eq!(
        IndecomposableCatalog::nakayama(&dynkin).unwrap_err(),
        EnumerateError::NotNakayama {
            vertex: 0,
            incoming: 0,
            outgoing: 3,
        }
    );
}

// The commutative square has one relation, so Gabriel's theorem does not
// apply, and vertex 0 has two outgoing arrows, so it is not Nakayama.
#[test]
fn an_unsupported_domain_carries_both_rejections() {
    let algebra = commutative_square(f5());
    assert_eq!(
        ar_quiver(&algebra).unwrap_err(),
        ArQuiverError::UnsupportedDomain {
            dynkin: DynkinError::NonzeroIdeal { relations: 1 },
            nakayama: EnumerateError::NotNakayama {
                vertex: 0,
                incoming: 0,
                outgoing: 2,
            },
        }
    );
}

#[test]
fn the_radical_needs_one_algebra() {
    let first = linear_an(3, f5());
    let second = linear_an(3, f5());
    let x = indec(&Module::simple(&first, 0));
    let y = indec(&Module::simple(&second, 0));
    assert_eq!(
        category_radical(&x, &y).unwrap_err(),
        ArQuiverError::Hom(HomError::DifferentAlgebras)
    );
}

// The radical of a Hom space between certified indecomposables misses
// exactly the isomorphisms, so a nonzero map outside the radical is one.
#[test]
fn maps_outside_the_radical_are_isomorphisms() {
    for algebra in [linear_an(3, f5()), truncated_poly(3, f2()).unwrap()] {
        let catalog = ar_quiver(&algebra).unwrap();
        let catalog = catalog.catalog();
        for x in catalog.entries() {
            for y in catalog.entries() {
                let radical = category_radical(x, y).unwrap();
                for f in hom(x.module(), y.module()).unwrap() {
                    if !radical.contains(&f).unwrap() {
                        assert!(f.is_isomorphism());
                    }
                }
            }
        }
    }
}

#[test]
fn the_ar_quiver_is_the_same_on_a_second_run() {
    for algebra in [linear_an(3, f2()), radical_square_zero_cycle(3, f5())] {
        let first = ar_quiver(&algebra).unwrap();
        let second = ar_quiver(&algebra).unwrap();
        assert_eq!(dim_vectors(&first), dim_vectors(&second));
        assert_eq!(arrow_triples(&first), arrow_triples(&second));
        for (a, b) in first.arrows().iter().zip(second.arrows()) {
            for (f, g) in a.representatives().iter().zip(b.representatives()) {
                assert_eq!(f.map_at(0).entries_u64(), g.map_at(0).entries_u64());
            }
        }
    }
}
