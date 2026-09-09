use super::approximation::approximation_matrix;
use super::*;
use crate::algebra::linear_an;
use crate::field::PrimeField;
use crate::module::direct_sum;

#[test]
fn absent_approximation_components_keep_each_part_width() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let part = Module::simple(&algebra, 0);
    let target = direct_sum(&[&part, &part]).0;
    let complex = BoundedComplex::new(0, vec![part.clone()], Vec::new()).unwrap();
    let representative = ChainMap::identity(&complex);
    let matrix = approximation_matrix(
        &part,
        &target,
        &[part.clone(), part.clone()],
        &[representative.clone(), representative],
        1,
        0,
        ApproximationDirection::Left,
    )
    .unwrap();
    assert_eq!(matrix, DenseMat::zero(1, 2));
}

fn regular_for_test(algebra: &Arc<Algebra>) -> CertifiedTiltingComplex {
    match regular_tilting_complex(algebra, TiltingComplexLimits::default()).unwrap() {
        TiltingComplexResult::Tilting(value) => *value,
        outcome => panic!("regular generator did not certify: {outcome:?}"),
    }
}

fn quotient_data_agrees(left: &HomotopyHomQuotient, right: &HomotopyHomQuotient) -> bool {
    left.degree() == right.degree()
        && left.source().agrees_with(right.source())
        && left.target().agrees_with(right.target())
        && left.hom().basis_rows() == right.hom().basis_rows()
        && left.null_homotopic_basis() == right.null_homotopic_basis()
        && left.complement_basis() == right.complement_basis()
}

#[test]
fn mutation_reuses_exact_unchanged_homotopy_blocks() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let regular = regular_for_test(&algebra);
    let cold = match tilting_mutation_with_cache(
        &regular,
        1,
        TiltingComplexLimits::default(),
        ApproximationDirection::Left,
        false,
    )
    .unwrap()
    {
        TiltingMutationOutcome::Tilting(value) => *value,
        outcome => panic!("cold mutation did not certify: {outcome:?}"),
    };
    let incremental = match tilting_mutation_with_cache(
        &regular,
        1,
        TiltingComplexLimits::default(),
        ApproximationDirection::Left,
        true,
    )
    .unwrap()
    {
        TiltingMutationOutcome::Tilting(value) => *value,
        outcome => panic!("incremental mutation did not certify: {outcome:?}"),
    };

    assert_eq!(cold.candidate().len(), incremental.candidate().len());
    assert!(
        cold.candidate()
            .summands()
            .iter()
            .zip(incremental.candidate().summands())
            .all(|(left, right)| left.complex().agrees_with(right.complex()))
    );
    assert_eq!(
        cold.degree_zero_endomorphisms().len(),
        incremental.degree_zero_endomorphisms().len()
    );
    assert!(
        cold.degree_zero_endomorphisms()
            .iter()
            .zip(incremental.degree_zero_endomorphisms())
            .all(|(left, right)| quotient_data_agrees(left, right))
    );
    assert_eq!(
        cold.zero_shifted_homs().len(),
        incremental.zero_shifted_homs().len()
    );
    assert!(
        cold.zero_shifted_homs()
            .iter()
            .zip(incremental.zero_shifted_homs())
            .all(|(left, right)| {
                left.source() == right.source()
                    && left.target() == right.target()
                    && left.degree() == right.degree()
                    && quotient_data_agrees(left.quotient(), right.quotient())
            })
    );
    assert!(incremental.work().hom_spaces_reused() > 0);
    assert!(incremental.work().hom_spaces_built() < cold.work().hom_spaces_built());
}

#[test]
fn block_cache_uses_representation_data_and_excludes_changed_endpoints() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let regular = regular_for_test(&algebra);
    let fresh = TiltingComplexCandidate::regular(&algebra);
    let mut blocks = HomotopyBlockBuilder::with_inherited(regular.block_cache());
    assert!(blocks.cached(&fresh, 0, 1, 0));
    blocks.set_changed(0);
    assert!(!blocks.cached(&fresh, 0, 1, 0));
    blocks.get(&fresh, 0, 1, 0).unwrap();
    assert_eq!(blocks.work.hom_spaces_built(), 1);
    assert_eq!(blocks.work.hom_spaces_reused(), 0);
}
