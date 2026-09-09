use super::*;

// Dropping a summand keeps the certified values: the kept summands are the
// same module values, not rebuilt ones, which is what a TauCache keyed by
// module identity needs.
#[test]
fn without_keeps_the_stored_summand_values() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let parts: Vec<Module> = (0..3).map(|v| Module::projective(&algebra, v)).collect();
        let refs: Vec<&Module> = parts.iter().collect();
        let whole = basic(&sum(&refs));
        assert!(whole.without(3).is_none(), "there is no slot 3");
        for slot in 0..3 {
            let kept = whole.without(slot).expect("the slot is a summand");
            assert_eq!(kept.len(), 2);
            let mut expected: Vec<&IndecomposableModule> = Vec::new();
            for (i, x) in whole.summands().iter().enumerate() {
                if i != slot {
                    expected.push(x);
                }
            }
            for (a, b) in kept.summands().iter().zip(expected) {
                assert!(a.module().ptr_eq(b.module()));
            }
            assert_eq!(
                kept.module().dim_vector(),
                BasicDecomposition::new(kept.module())
                    .expect("a sum of two projectives is basic")
                    .module()
                    .dim_vector()
            );
        }
    }
}

#[test]
fn with_new_summand_appends_and_rejects_a_repeat() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let one = basic(&p0);
        let other = IndecomposableModule::new(&p1).expect("P_1 is indecomposable");
        let two = one
            .with_new_summand(&other)
            .expect("P_0 and P_1 are not isomorphic");
        assert_eq!(two.len(), 2);
        assert!(two.summands()[0].module().ptr_eq(&p0));
        assert!(two.summands()[1].module().ptr_eq(&p1));
        assert_eq!(two.module().dim_vector(), sum(&[&p0, &p1]).dim_vector());
        let repeat = IndecomposableModule::new(&Module::projective(&algebra, 0))
            .expect("P_0 is indecomposable");
        assert_eq!(
            two.with_new_summand(&repeat).err(),
            Some(BasicError::NotBasic {
                first: 0,
                second: 2
            })
        );
        let elsewhere = linear_an(3, field);
        let outside = IndecomposableModule::new(&Module::simple(&elsewhere, 0))
            .expect("a simple is indecomposable");
        assert_eq!(
            two.with_new_summand(&outside).err(),
            Some(BasicError::DifferentAlgebras)
        );
    }
}

// The catalog constructor skips Krull-Schmidt, so its answer has to agree
// with the general one on the same subset, summand for summand.
#[test]
fn from_catalog_agrees_with_the_general_constructor() {
    for field in fields() {
        let algebra = d4(field);
        let catalog = IndecomposableCatalog::dynkin(&algebra).expect("D_4 is Dynkin");
        for chosen in [vec![], vec![0], vec![2, 5], vec![1, 3, 7]] {
            let from_catalog = BasicDecomposition::from_catalog(&catalog, &chosen)
                .expect("distinct catalog entries are pairwise non-isomorphic");
            assert_eq!(from_catalog.len(), chosen.len());
            for (x, &i) in from_catalog.summands().iter().zip(&chosen) {
                assert!(x.module().ptr_eq(catalog.entries()[i].module()));
            }
            let parts: Vec<&Module> = chosen
                .iter()
                .map(|&i| catalog.entries()[i].module())
                .collect();
            let assembled = if parts.is_empty() {
                Module::zero(&algebra)
            } else {
                sum(&parts)
            };
            let general = basic(&assembled);
            assert_eq!(general.dim_vectors(), from_catalog.dim_vectors());
            assert_eq!(
                general.module().dim_vector(),
                from_catalog.module().dim_vector()
            );
        }
        assert_eq!(
            BasicDecomposition::from_catalog(&catalog, &[4, 4]).err(),
            Some(BasicError::NotBasic {
                first: 0,
                second: 1
            })
        );
    }
}

// P_v is indecomposable, so its basic decomposition has one summand whose
// dimension vector is the row v of the Cartan matrix.
#[test]
fn each_projective_gives_one_summand() {
    for field in fields() {
        for algebra in [
            linear_an(3, field),
            d4(field),
            truncated_poly(3, field).unwrap(),
            commutative_square(field),
            kronecker(2, field),
        ] {
            for v in 0..algebra.quiver().num_vertices() {
                let p = Module::projective(&algebra, v);
                let decomposition = basic(&p);
                assert_eq!(decomposition.len(), 1, "P_{v} over F_{}", field.modulus());
                assert!(!decomposition.is_empty());
                assert!(decomposition.module().ptr_eq(&p));
                assert_eq!(decomposition.dim_vectors(), vec![p.dim_vector().to_vec()]);
            }
        }
    }
}

// Linearly oriented A_3: P_0 = [1, 1, 1], P_1 = [0, 1, 1], P_2 = [0, 0, 1].
// The three are pairwise non-isomorphic, so the sum is basic and the
// sorted dimension vectors are [0, 0, 1] < [0, 1, 1] < [1, 1, 1].
#[test]
fn the_sum_of_the_a3_projectives_is_basic() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let parts: Vec<Module> = (0..3).map(|v| Module::projective(&algebra, v)).collect();
        let total = sum(&[&parts[0], &parts[1], &parts[2]]);
        let decomposition = basic(&total);
        assert_eq!(decomposition.len(), 3);
        assert_eq!(
            decomposition.dim_vectors(),
            vec![vec![0, 0, 1], vec![0, 1, 1], vec![1, 1, 1]],
            "over F_{}",
            field.modulus()
        );
    }
}

// D_4 with every arrow leaving the center: P_0 = [1, 1, 1, 1] and
// P_1 = P_2 = P_3 are the simples at the three leaves.
#[test]
fn the_sum_of_the_d4_projectives_is_basic() {
    for field in fields() {
        let algebra = d4(field);
        let parts: Vec<Module> = (0..4).map(|v| Module::projective(&algebra, v)).collect();
        let total = sum(&[&parts[0], &parts[1], &parts[2], &parts[3]]);
        let decomposition = basic(&total);
        assert_eq!(decomposition.len(), 4);
        assert_eq!(
            decomposition.dim_vectors(),
            vec![
                vec![0, 0, 0, 1],
                vec![0, 0, 1, 0],
                vec![0, 1, 0, 0],
                vec![1, 1, 1, 1],
            ],
            "over F_{}",
            field.modulus()
        );
    }
}

// k[x]/(x^3) has one vertex and three indecomposables, of dimension 1, 2,
// and 3. The regular module is the one of dimension 3.
#[test]
fn truncated_poly_three_gives_summands_of_dimension_one_and_three() {
    for field in fields() {
        let algebra = truncated_poly(3, field).unwrap();
        let regular = Module::projective(&algebra, 0);
        let simple = Module::simple(&algebra, 0);
        let decomposition = basic(&sum(&[&regular, &simple]));
        assert_eq!(decomposition.len(), 2);
        assert_eq!(
            decomposition.dim_vectors(),
            vec![vec![1], vec![3]],
            "over F_{}",
            field.modulus()
        );
    }
}

// The commutative square: P_0 = [1, 1, 1, 1] (e_0, a, c, ab = cd),
// P_1 = [0, 1, 0, 1], P_2 = [0, 0, 1, 1], P_3 = [0, 0, 0, 1].
#[test]
fn the_commutative_square_projectives_have_the_expected_dim_vectors() {
    for field in fields() {
        let algebra = commutative_square(field);
        let expected = [
            vec![1, 1, 1, 1],
            vec![0, 1, 0, 1],
            vec![0, 0, 1, 1],
            vec![0, 0, 0, 1],
        ];
        for (v, want) in expected.iter().enumerate() {
            let p = Module::projective(&algebra, v as u32);
            assert_eq!(basic(&p).dim_vectors(), vec![want.clone()]);
        }
    }
}

#[test]
fn the_zero_module_has_no_summands() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let zero = Module::zero(&algebra);
        let decomposition = basic(&zero);
        assert_eq!(decomposition.len(), 0);
        assert!(decomposition.is_empty());
        assert!(decomposition.dim_vectors().is_empty());
        assert!(decomposition.module().ptr_eq(&zero));
    }
}

// P_0 + P_0 has one isomorphism class of multiplicity 2, so the repeat
// sits at index 1 of the summand list.
#[test]
fn a_repeated_summand_is_rejected() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let doubled = sum(&[&p0, &p0]);
        assert_eq!(
            BasicDecomposition::new(&doubled).unwrap_err(),
            BasicError::NotBasic {
                first: 0,
                second: 1
            },
            "P_0 + P_0 over F_{}",
            field.modulus()
        );
    }
}

// A repeat of a separately built copy is still a repeat: identity is
// isomorphism, not module identity.
#[test]
fn a_repeated_summand_from_a_fresh_copy_is_rejected() {
    let algebra = linear_an(3, f5());
    let first = Module::projective(&algebra, 1);
    let second = Module::projective(&algebra, 1);
    assert!(matches!(
        BasicDecomposition::new(&sum(&[&first, &second])).unwrap_err(),
        BasicError::NotBasic { .. }
    ));
}
