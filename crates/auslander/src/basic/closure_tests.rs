use super::*;

// T = P_0 + P_2 over A_3. P_2 is a summand of T, so it lies in add(T).
#[test]
fn a_summand_of_t_lies_in_add_t() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let t = basic(&sum(&[&p0, &p2]));
        let m = basic(&Module::projective(&algebra, 2));
        let witness = AddClosureWitness::new(&m, &t)
            .unwrap()
            .expect("P_2 is a summand of T");
        assert!(witness.verify());
        assert_eq!(witness.matches().len(), 1);
        let target = witness.matches()[0].target_index();
        assert_eq!(
            witness.target_summands()[target].dim_vector(),
            &[0, 0, 1],
            "over F_{}",
            field.modulus()
        );
        assert_eq!(witness.summands().len(), 1);
        assert!(witness.target().ptr_eq(t.module()));
    }
}

// S_1 = [0, 1, 0] over A_3 is not isomorphic to P_0 = [1, 1, 1] or to
// P_2 = [0, 0, 1], so it lies outside add(P_0 + P_2).
#[test]
fn a_non_summand_is_outside_add_t() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let t = basic(&sum(&[&p0, &p2]));
        let m = basic(&Module::simple(&algebra, 1));
        assert!(AddClosureWitness::new(&m, &t).unwrap().is_none());
    }
}

// T + T is in add(T) and is not basic, so only from_module accepts it.
// Its four summands match the two summands of T twice each.
#[test]
fn t_plus_t_lies_in_add_t_through_from_module() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let t_module = sum(&[&p0, &p2]);
        let t = basic(&t_module);
        let doubled = sum(&[&t_module, &t_module]);
        assert!(matches!(
            BasicDecomposition::new(&doubled).unwrap_err(),
            BasicError::NotBasic { .. }
        ));
        let witness = AddClosureWitness::from_module(&doubled, &t)
            .unwrap()
            .expect("T + T lies in add(T)");
        assert!(witness.verify());
        assert_eq!(witness.matches().len(), 4);
        let mut hits = [0usize; 2];
        for entry in witness.matches() {
            hits[entry.target_index()] += 1;
        }
        assert_eq!(hits, [2, 2], "over F_{}", field.modulus());
        assert!(witness.module().ptr_eq(&doubled));
        let split = witness.split();
        assert!(split.verify());
        assert!(split.total().ptr_eq(&doubled));
        assert_eq!(split.summands().len(), witness.summands().len());
        for ((summand, inclusion), projection) in split
            .summands()
            .iter()
            .zip(split.inclusions())
            .zip(split.projections())
        {
            assert_eq!(
                inclusion.then(projection).expect("split endpoints agree"),
                crate::hom::identity(summand)
            );
        }
    }
}

#[test]
fn the_zero_module_lies_in_add_t() {
    let algebra = linear_an(3, f5());
    let t = basic(&Module::projective(&algebra, 0));
    let zero = Module::zero(&algebra);
    let witness = AddClosureWitness::from_module(&zero, &t)
        .unwrap()
        .expect("the zero module lies in add(T)");
    assert!(witness.verify());
    assert!(witness.matches().is_empty());
    let basic_zero = basic(&zero);
    let from_basic = AddClosureWitness::new(&basic_zero, &t)
        .unwrap()
        .expect("the zero module lies in add(T)");
    assert!(from_basic.verify());
}

#[test]
fn a_tampered_add_closure_match_fails_verification() {
    let algebra = linear_an(3, f5());
    let p0 = Module::projective(&algebra, 0);
    let p2 = Module::projective(&algebra, 2);
    let t = basic(&sum(&[&p0, &p2]));
    let m = basic(&Module::projective(&algebra, 2));
    let mut witness = AddClosureWitness::new(&m, &t)
        .unwrap()
        .expect("P_2 is a summand of T");
    assert!(witness.verify());
    // Pointing the match at the other summand of T leaves the stored
    // isomorphism with the wrong endpoints.
    witness.matches[0].target_index = 1 - witness.matches[0].target_index;
    assert!(!witness.verify());
}

// Over the commutative square, add(P_0 + P_3) contains P_3 but not P_1.
#[test]
fn add_closure_holds_over_the_commutative_square() {
    for field in fields() {
        let algebra = commutative_square(field);
        let p0 = Module::projective(&algebra, 0);
        let p3 = Module::projective(&algebra, 3);
        let t = basic(&sum(&[&p0, &p3]));
        let inside = basic(&Module::projective(&algebra, 3));
        let outside = basic(&Module::projective(&algebra, 1));
        assert!(AddClosureWitness::new(&inside, &t).unwrap().is_some());
        assert!(AddClosureWitness::new(&outside, &t).unwrap().is_none());
    }
}

// Over k[x]/(x^3), add(k[x]/(x^3)) contains the regular module twice over
// but not the simple k[x]/(x).
#[test]
fn add_closure_holds_over_truncated_poly_three() {
    for field in fields() {
        let algebra = truncated_poly(3, field).unwrap();
        let regular = Module::projective(&algebra, 0);
        let t = basic(&regular);
        let doubled = sum(&[&regular, &regular]);
        let witness = AddClosureWitness::from_module(&doubled, &t)
            .unwrap()
            .expect("the regular module doubled lies in add(T)");
        assert!(witness.verify());
        assert_eq!(witness.matches().len(), 2);
        let simple = basic(&Module::simple(&algebra, 0));
        assert!(AddClosureWitness::new(&simple, &t).unwrap().is_none());
    }
}
