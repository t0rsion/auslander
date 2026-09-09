use auslander::algebra::linear_an;
use auslander::module::{Module, direct_sum};
use auslander::perfect::{ProjectiveTermError, ProjectiveTermWitness};

#[test]
fn canonical_projective_terms_include_zero_and_multiplicity() {
    let algebra = linear_an(3, super::f5());
    let zero = Module::zero(&algebra);
    let zero_witness = ProjectiveTermWitness::new(&zero).unwrap();
    assert!(zero_witness.verify());
    assert!(zero_witness.vertices().is_empty());

    let p = Module::projective(&algebra, 1);
    let (twice, _, _) = direct_sum(&[&p, &p]);
    let witness = ProjectiveTermWitness::new(&twice).unwrap();
    assert!(witness.verify());
    assert_eq!(witness.vertices(), &[1, 1]);
    assert_eq!(witness.split().summands().len(), 2);
}

#[test]
fn a_nonprojective_simple_is_rejected() {
    let algebra = linear_an(3, super::f5());
    let simple = Module::simple(&algebra, 0);
    assert!(matches!(
        ProjectiveTermWitness::new(&simple),
        Err(ProjectiveTermError::NotProjective)
    ));
}
