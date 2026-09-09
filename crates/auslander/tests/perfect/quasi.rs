use auslander::algebra::linear_an;
use auslander::homotopy::{BoundedComplex, ChainMap};
use auslander::module::Module;
use auslander::perfect::{
    PerfectReplacement, ProjectiveComplex, QuasiIsomorphism, QuasiIsomorphismError,
};

#[test]
fn an_identity_map_is_a_checked_replacement() {
    let algebra = linear_an(3, super::f5());
    let projective = Module::projective(&algebra, 0);
    let complex = BoundedComplex::new(2, vec![projective], vec![]).unwrap();
    let projective = ProjectiveComplex::new(complex).unwrap();
    let replacement = PerfectReplacement::identity(projective);
    assert!(replacement.verify());
    assert!(replacement.quasi_isomorphism().exact_cone().verify());
}

#[test]
fn a_zero_map_on_nonzero_homology_is_not_a_quasi_isomorphism() {
    let algebra = linear_an(3, super::f5());
    let simple = Module::simple(&algebra, 0);
    let complex = BoundedComplex::new(0, vec![simple], vec![]).unwrap();
    let zero = ChainMap::zero(&complex, &complex).unwrap();
    assert!(matches!(
        QuasiIsomorphism::new(zero),
        Err(QuasiIsomorphismError::NotExact(_))
    ));
}
