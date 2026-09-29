use super::approximation::{approximation_map, approximation_matrix};
use super::mutation::tilting_mutation_with_cache;
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
        (ApproximationDirection::Left, OrthogonalityGoal::Tilting),
        false,
        &mut WorkMeter::default(),
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
        (ApproximationDirection::Left, OrthogonalityGoal::Tilting),
        true,
        &mut WorkMeter::default(),
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
    let mut meter = WorkMeter::default();
    let mut blocks = HomotopyBlockBuilder::with_inherited(regular.block_cache(), &mut meter);
    assert!(blocks.cached(&fresh, 0, 1, 0));
    blocks.set_changed(0);
    assert!(!blocks.cached(&fresh, 0, 1, 0));
    blocks.get(&fresh, 0, 1, 0).unwrap();
    assert_eq!(blocks.work.hom_spaces_built(), 1);
    assert_eq!(blocks.work.hom_spaces_reused(), 0);
}

fn two_cycle_with_one_relation(field: PrimeField) -> Arc<Algebra> {
    let quiver = crate::quiver::Quiver::new(2, &[(0, 1), (1, 0)]).unwrap();
    let words = vec![vec![crate::quiver::ArrowId(0), crate::quiver::ArrowId(1)]];
    let ideal = crate::monomial::MonomialIdeal::new(quiver, words).unwrap();
    crate::algebra::monomial_algebra(&ideal, field).unwrap()
}

#[test]
fn local_endomorphism_rings_certify_with_their_radicals() {
    for modulus in [2, 5] {
        let field = PrimeField::new(modulus).unwrap();
        let tilting = regular_for_test(&crate::algebra::dual_numbers(field));
        assert_eq!(tilting.degree_zero_endomorphisms()[0].dim(), 2);
        let endo = crate::complex_target::HomotopyEndomorphismAlgebra::new(&tilting).unwrap();
        assert_eq!(endo.radical_basis().rows(), 1);
        // The composite P_1 → P_0 → P_1 is the nonzero radical element, so
        // the two summands stay distinct.
        let tilting = regular_for_test(&two_cycle_with_one_relation(field));
        let dims: Vec<usize> = tilting
            .degree_zero_endomorphisms()
            .iter()
            .map(HomotopyHomQuotient::dim)
            .collect();
        assert_eq!(dims, [1, 2]);
    }
}

#[test]
fn decomposable_and_repeated_summands_stay_blocked() {
    let algebra = crate::algebra::dual_numbers(PrimeField::new(5).unwrap());
    let projective = Module::projective(&algebra, 0);
    let stalk = |module: Module| {
        ProjectiveComplex::new(BoundedComplex::new(0, vec![module], Vec::new()).unwrap()).unwrap()
    };
    let classify = |summands| {
        let candidate = TiltingComplexCandidate::new(summands).unwrap();
        classify_tilting_complex(candidate, None, TiltingComplexLimits::default()).unwrap()
    };
    let doubled = direct_sum(&[&projective, &projective]).0;
    assert!(matches!(
        classify(vec![stalk(doubled)]),
        TiltingComplexResult::Undetermined(TiltingComplexBlocker::EndomorphismLocality {
            summand: 0,
            dimension: 8
        })
    ));
    assert!(matches!(
        classify(vec![stalk(projective.clone()), stalk(projective)]),
        TiltingComplexResult::Undetermined(TiltingComplexBlocker::RepeatedSummand {
            first: 0,
            second: 1
        })
    ));
}

/// In `A_3`, the map `P_2 → P_0` is the composite through `P_1`, a map between
/// distinct summands. In the genus-1 gentle algebra, `abc: P_1 → P_0` is `c`
/// followed by the radical endomorphism `ab` of `P_0`. Both are dropped.
#[test]
fn minimal_approximations_drop_maps_through_radical_maps() {
    let field = PrimeField::new(3).unwrap();
    let linear = regular_for_test(&linear_an(3, field));
    let (_, indices) = approximation_map(&linear, 2, ApproximationDirection::Left).unwrap();
    assert_eq!(indices, [1]);
    let quiver = crate::quiver::Quiver::new(2, &[(0, 1), (1, 0), (0, 1)]).unwrap();
    let words = [[2, 1], [1, 0]]
        .iter()
        .map(|word| {
            word.iter()
                .map(|&arrow| crate::quiver::ArrowId(arrow))
                .collect()
        })
        .collect();
    let ideal = crate::monomial::MonomialIdeal::new(quiver, words).unwrap();
    let genus_one = regular_for_test(&crate::algebra::monomial_algebra(&ideal, field).unwrap());
    assert_eq!(genus_one.degree_zero_endomorphisms()[1].dim(), 2);
    let (_, indices) = approximation_map(&genus_one, 1, ApproximationDirection::Left).unwrap();
    assert_eq!(indices, [0, 0]);
    assert!(matches!(
        left_tilting_mutation(&genus_one, 1, TiltingComplexLimits::default()).unwrap(),
        TiltingMutationOutcome::Tilting(_)
    ));
}

impl CertifiedSiltingComplex {
    /// A copy with summands and their endomorphism data in `order`.
    ///
    /// The copy fails `verify`. It tests order independence of vertex
    /// identity.
    pub(crate) fn with_summand_order(&self, order: &[usize]) -> CertifiedSiltingComplex {
        let mut copy = self.clone();
        copy.candidate.summands = order
            .iter()
            .map(|&index| self.candidate.summands[index].clone())
            .collect();
        copy.degree_zero_endomorphisms = order
            .iter()
            .map(|&index| self.degree_zero_endomorphisms[index].clone())
            .collect();
        copy.degree_zero_residues = order
            .iter()
            .map(|&index| self.degree_zero_residues[index].clone())
            .collect();
        copy
    }
}
