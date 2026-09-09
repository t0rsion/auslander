use super::*;

// The complement is the greedy independent set of unit vectors, not the
// free columns of the radical: for rad = span{e_0 + e_1} it picks e_0 while
// column 1 is the free one.
#[test]
fn the_complement_search_takes_the_first_independent_unit_vector() {
    let field = f5();
    let mut reducer = RowReducer::new(3);
    reducer.push(&[field.one(), field.one(), field.zero()], &field);
    assert!(reducer.push(&unit(3, 0, &field), &field));
    assert!(!reducer.push(&unit(3, 1, &field), &field));
    assert!(reducer.push(&unit(3, 2, &field), &field));
}

#[test]
fn the_endomorphism_algebra_is_sync() {
    fn assert_sync<T: Sync + Send>() {}
    assert_sync::<EndoAlgebra>();
}

// End(M ⊕ M) ≅ M_2(F_4): one Wedderburn factor but noncommutative, so not
// local, and split_idempotent must return None (it needs two factors);
// only the Fitting fallback can split this sum.
#[test]
fn m2_of_f4_has_one_factor_but_is_not_local_and_yields_no_idempotent() {
    let m = kronecker_f4_module();
    let (sum, _, _) = direct_sum(&[&m, &m]);
    let e = EndoAlgebra::new(&sum);
    assert_eq!(e.dim(), 8);
    assert_eq!(e.radical_dim(), 0);
    assert_eq!(e.semisimple_factor_count(), 1);
    assert!(!e.quotient_is_commutative());
    assert!(!e.is_local());
    assert_eq!(e.split_idempotent(&mut SplitMix64(7)), None);
}
