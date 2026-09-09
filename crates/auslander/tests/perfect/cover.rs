use auslander::algebra::linear_an;
use auslander::hom::{cokernel, zero_morphism};
use auslander::homotopy::BoundedComplex;
use auslander::module::Module;
use auslander::perfect::projective_complex_cover;

#[test]
fn the_complex_projective_cover_is_degreewise_surjective() {
    let algebra = linear_an(3, super::f5());
    let s0 = Module::simple(&algebra, 0);
    let s1 = Module::simple(&algebra, 1);
    let zero = zero_morphism(&s1, &s0).unwrap();
    let complex = BoundedComplex::new(-1, vec![s0, s1], vec![zero]).unwrap();
    let cover = projective_complex_cover(&complex).unwrap();
    assert!(cover.verify());
    assert_eq!(cover.augmentation().source().range(), complex.range());
    assert!(
        cover
            .augmentation()
            .components()
            .iter()
            .all(|component| cokernel(component).0.is_zero())
    );
}
