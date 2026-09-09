use super::*;

#[test]
fn the_radical_between_distinct_simples_is_the_whole_hom_space() {
    for field in [f2(), f5()] {
        let algebra = linear_an(3, field);
        let simples: Vec<IndecomposableModule> = (0..3)
            .map(|v| indec(&Module::simple(&algebra, v)))
            .collect();
        for x in &simples {
            for y in &simples {
                let space = HomSpace::new(x.module(), y.module()).unwrap();
                let radical = category_radical(x, y).unwrap();
                if x.module().ptr_eq(y.module()) {
                    // End(S) = k, so rad End(S) = 0 while Hom is a line.
                    assert_eq!(space.dim(), 1);
                    assert_eq!(radical.dim(), 0);
                } else {
                    // Distinct simples over linearly oriented A_3 admit no
                    // nonzero map, so Hom and its radical are both zero.
                    assert_eq!(space.dim(), 0);
                    assert_eq!(radical, space.full_subspace());
                }
            }
        }
    }
}

// Over linearly oriented A_3 the projective P_0 has dimension vector
// (1, 1, 1) and S_0 is its top, so Hom(P_0, S_0) is the line spanned by
// the top projection. The two modules are not isomorphic, so the whole
// line is radical.
#[test]
fn the_radical_from_a_projective_onto_its_top_is_the_whole_hom_line() {
    for field in [f2(), f5()] {
        let algebra = linear_an(3, field);
        let p0 = indec(&Module::projective(&algebra, 0));
        let s0 = indec(&Module::simple(&algebra, 0));
        let space = HomSpace::new(p0.module(), s0.module()).unwrap();
        assert_eq!(space.dim(), 1);
        let radical = category_radical(&p0, &s0).unwrap();
        assert_eq!(radical.dim(), 1);
        assert_eq!(radical, space.full_subspace());
        assert!(radical.contains(&space.basis()[0]).unwrap());
    }
}

// The isomorphic case, on two separately built copies of the projective
// of k[x]/(x^3): the catalog entry P/rad^3 is a cokernel, the projective
// is built directly, and the two are isomorphic. A second isomorphism is
// the first composed with the automorphism 1 + n for n a radical basis
// element of End(X); 1 + n is a unit because n is nilpotent.
#[test]
fn the_radical_does_not_depend_on_the_chosen_isomorphism() {
    for field in [f2(), f5()] {
        let algebra = truncated_poly(3, field).unwrap();
        let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
        let x = indec(&Module::projective(&algebra, 0));
        let y = &catalog.entries()[2];
        assert_eq!(y.module().total_dim(), 3);
        assert!(!x.module().ptr_eq(y.module()));
        let space = HomSpace::new(x.module(), y.module()).unwrap();
        assert_eq!(space.dim(), 3);

        let first = inverse_morphism(
            &indecomposable_iso(x.module(), y.module(), x.endo())
                .expect("the two copies are isomorphic"),
        )
        .unwrap();
        let endo = x.endo();
        assert_eq!(endo.radical_dim(), 2);
        let mut automorphism = endo.one().to_vec();
        for (c, entry) in automorphism.iter_mut().enumerate() {
            *entry = field.add(*entry, endo.radical_basis().get(0, c));
        }
        let second = first.then(&endo.morphism(&automorphism)).unwrap();
        assert!(second.is_isomorphism());
        assert_ne!(first, second);

        let by_first = radical_against_iso(&space, endo, &first).unwrap();
        let by_second = radical_against_iso(&space, endo, &second).unwrap();
        assert_eq!(by_first.dim(), 2);
        assert_eq!(by_first, by_second);
        assert_eq!(by_first, category_radical(&x, y).unwrap());
    }
}
