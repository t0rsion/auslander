use super::algorithm::{DECOMPOSE_SEED, deterministic_split};
use super::{
    Certificate, Decomposition, IsoClass, KrullSchmidtOutcome, Split, SplitError, decompose,
    krull_schmidt,
};
use crate::algebra::{dual_numbers, kronecker, linear_an, truncated_poly};
use crate::endo::{EndoAlgebra, SplitMix64};
use crate::field::PrimeField;
use crate::hom::zero_morphism;
use crate::iso::{IsoOutcome, is_isomorphic};
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};

fn fields() -> [PrimeField; 2] {
    [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
}

fn sorted_dims(summands: &[Module]) -> Vec<Vec<usize>> {
    let mut dims: Vec<Vec<usize>> = summands.iter().map(|s| s.dim_vector().to_vec()).collect();
    dims.sort();
    dims
}

#[test]
fn split_new_accepts_direct_sum_data_and_rejects_swapped_projections() {
    let field = PrimeField::new(5).unwrap();
    let a = linear_an(3, field);
    let p0 = Module::projective(&a, 0);
    let p0_copy = Module::projective(&a, 0);
    let (sum, inclusions, projections) = direct_sum(&[&p0, &p0_copy]);
    let summands = vec![p0.clone(), p0_copy.clone()];
    assert!(
        Split::new(
            &sum,
            summands.clone(),
            inclusions.clone(),
            projections.clone()
        )
        .is_ok()
    );
    let swapped_endpoints = Split::new(
        &sum,
        vec![p0_copy.clone(), p0.clone()],
        inclusions.clone(),
        projections.clone(),
    );
    assert_eq!(
        swapped_endpoints.unwrap_err(),
        SplitError::EndpointMismatch { index: 0 }
    );
    assert_eq!(
        Split::new(&sum, summands.clone(), inclusions.clone(), Vec::new()).unwrap_err(),
        SplitError::CountMismatch
    );
    // π_1 in slot 0 has the wrong target module, caught as endpoints.
    let reordered = vec![projections[1].clone(), projections[0].clone()];
    assert_eq!(
        Split::new(&sum, summands, inclusions, reordered).unwrap_err(),
        SplitError::EndpointMismatch { index: 0 }
    );
}

#[test]
fn split_new_rejects_a_projection_that_does_not_split_its_inclusion() {
    let field = PrimeField::new(5).unwrap();
    let a = linear_an(3, field);
    let p0 = Module::projective(&a, 0);
    let (sum, inclusions, projections) = direct_sum(&[&p0]);
    let zero = zero_morphism(&sum, &p0).unwrap();
    assert_eq!(
        Split::new(
            &sum,
            vec![p0.clone()],
            inclusions.clone(),
            vec![zero.clone()]
        )
        .unwrap_err(),
        SplitError::NotIdentityOnSummand { index: 0 }
    );
    let zero_incl = zero_morphism(&p0, &sum).unwrap();
    assert_eq!(
        Split::new(&sum, vec![p0.clone()], vec![zero_incl], projections).unwrap_err(),
        SplitError::NotIdentityOnSummand { index: 0 }
    );
    assert_eq!(
        Split::new(&sum, vec![p0.clone()], inclusions, vec![zero]).unwrap_err(),
        SplitError::NotIdentityOnSummand { index: 0 }
    );
}

#[test]
fn split_new_rejects_a_partial_family_of_summands() {
    let field = PrimeField::new(5).unwrap();
    let a = linear_an(3, field);
    let p0 = Module::projective(&a, 0);
    let s2 = Module::simple(&a, 2);
    let (sum, inclusions, projections) = direct_sum(&[&p0, &s2]);
    // Dropping the second summand leaves Σ π ι ≠ id on the total.
    assert_eq!(
        Split::new(
            &sum,
            vec![p0.clone()],
            vec![inclusions[0].clone()],
            vec![projections[0].clone()]
        )
        .unwrap_err(),
        SplitError::SumNotIdentity
    );
}

// End(M ⊕ M) ≅ M_2(F_4) has one Wedderburn factor, so the deterministic
// idempotent route finds nothing and only the seeded Fitting fallback can
// split; both summands must come back certified and isomorphic to M.
#[test]
fn decompose_splits_the_f4_kronecker_double_via_the_fitting_fallback() {
    let field = PrimeField::new(2).unwrap();
    let a = kronecker(2, field);
    let id = DenseMat::from_rows(&[
        vec![field.one(), field.zero()],
        vec![field.zero(), field.one()],
    ]);
    // Companion matrix of x² + x + 1, irreducible over F_2.
    let c = DenseMat::from_rows(&[
        vec![field.zero(), field.one()],
        vec![field.one(), field.one()],
    ]);
    let m = Module::new(a, vec![2, 2], vec![id, c]).unwrap();
    let (sum, _, _) = direct_sum(&[&m, &m]);
    let d = decompose(&sum);
    assert_eq!(d.summands().len(), 2);
    assert_eq!(
        d.certificates(),
        &[Certificate::Indecomposable, Certificate::Indecomposable]
    );
    for s in d.summands() {
        assert!(matches!(
            is_isomorphic(s, &m).unwrap(),
            IsoOutcome::Isomorphic(_)
        ));
    }
}

#[test]
fn decompose_of_the_zero_module_has_no_summands() {
    let a = linear_an(3, PrimeField::new(5).unwrap());
    let d = decompose(&Module::zero(&a));
    assert!(d.summands().is_empty());
    assert!(d.certificates().is_empty());
}

#[test]
fn decompose_of_indecomposables_is_a_single_certified_summand() {
    for field in fields() {
        let a3 = linear_an(3, field);
        let dn = dual_numbers(field);
        for m in [
            Module::projective(&a3, 0),
            Module::simple(&a3, 1),
            Module::projective(&dn, 0),
        ] {
            let d = decompose(&m);
            assert_eq!(d.summands().len(), 1);
            assert_eq!(d.certificates(), &[Certificate::Indecomposable]);
            assert_eq!(d.summands()[0].dim_vector(), m.dim_vector());
        }
    }
}

#[test]
fn decompose_of_p0_plus_s2_finds_both_certified_summands() {
    for field in fields() {
        let a = linear_an(3, field);
        let p0 = Module::projective(&a, 0);
        let s2 = Module::simple(&a, 2);
        let (sum, _, _) = direct_sum(&[&p0, &s2]);
        let d = decompose(&sum);
        assert_eq!(d.summands().len(), 2);
        assert!(
            d.certificates()
                .iter()
                .all(|c| *c == Certificate::Indecomposable)
        );
        assert_eq!(
            sorted_dims(d.summands()),
            vec![vec![0, 0, 1], vec![1, 1, 1]]
        );
    }
}

// End(S ⊕ S) ≅ M_2(F_p) has one Wedderburn factor, so the deterministic
// route finds nothing and only seeded Fitting elements can split.
#[test]
fn decompose_of_two_isomorphic_simples_splits_via_the_fitting_fallback() {
    for field in fields() {
        let a = linear_an(3, field);
        let s = Module::simple(&a, 0);
        let (sum, _, _) = direct_sum(&[&s, &s]);
        let endo = EndoAlgebra::new(&sum);
        assert!(
            deterministic_split(&sum, &endo, &mut SplitMix64(DECOMPOSE_SEED)).is_none(),
            "the central route cannot split a matrix algebra"
        );
        let d = decompose(&sum);
        assert_eq!(d.summands().len(), 2);
        assert!(
            d.certificates()
                .iter()
                .all(|c| *c == Certificate::Indecomposable)
        );
        assert_eq!(
            sorted_dims(d.summands()),
            vec![vec![1, 0, 0], vec![1, 0, 0]]
        );
    }
}

#[test]
fn decompose_of_the_truncated_polynomial_square_finds_two_local_summands() {
    for field in fields() {
        let a = truncated_poly(3, field).unwrap();
        let p = Module::projective(&a, 0);
        let (sum, _, _) = direct_sum(&[&p, &p]);
        let d = decompose(&sum);
        assert_eq!(d.summands().len(), 2);
        assert_eq!(sorted_dims(d.summands()), vec![vec![3], vec![3]]);
        assert!(
            d.certificates()
                .iter()
                .all(|c| *c == Certificate::Indecomposable)
        );
    }
}

fn classes_of(m: &Module) -> Vec<IsoClass> {
    match krull_schmidt(m) {
        KrullSchmidtOutcome::Classes(classes) => classes,
        KrullSchmidtOutcome::Unknown { reason } => panic!("unexpected Unknown: {reason}"),
    }
}

fn class_dims(classes: &[IsoClass]) -> Vec<(Vec<usize>, usize)> {
    let mut dims: Vec<(Vec<usize>, usize)> = classes
        .iter()
        .map(|c| (c.representative.dim_vector().to_vec(), c.multiplicity))
        .collect();
    dims.sort();
    dims
}

#[test]
fn krull_schmidt_of_p_plus_s_plus_p_has_multiplicities_2_and_1() {
    for field in fields() {
        let a = linear_an(3, field);
        let p0 = Module::projective(&a, 0);
        let s2 = Module::simple(&a, 2);
        let (sum, _, _) = direct_sum(&[&p0, &s2, &p0]);
        let classes = classes_of(&sum);
        assert_eq!(
            class_dims(&classes),
            vec![(vec![0, 0, 1], 1), (vec![1, 1, 1], 2)]
        );
    }
}

#[test]
fn krull_schmidt_is_invariant_under_permutation_of_summands() {
    for field in fields() {
        let a = linear_an(3, field);
        let s0 = Module::simple(&a, 0);
        let p1 = Module::projective(&a, 1);
        let (shuffled, _, _) = direct_sum(&[&s0, &p1, &s0, &p1]);
        let (reordered, _, _) = direct_sum(&[&p1, &s0, &p1, &s0]);
        let left = classes_of(&shuffled);
        let right = classes_of(&reordered);
        assert_eq!(class_dims(&left), class_dims(&right));
        assert_eq!(
            class_dims(&left),
            vec![(vec![0, 1, 1], 2), (vec![1, 0, 0], 2)]
        );
        for class in &left {
            let partner = right
                .iter()
                .find(|c| c.representative.dim_vector() == class.representative.dim_vector())
                .expect("matching class exists");
            assert!(matches!(
                crate::iso::is_isomorphic(&class.representative, &partner.representative).unwrap(),
                crate::iso::IsoOutcome::Isomorphic(_)
            ));
        }
    }
}

#[test]
fn krull_schmidt_of_an_indecomposable_is_a_single_class() {
    let field = PrimeField::new(5).unwrap();
    let a = dual_numbers(field);
    let p = Module::projective(&a, 0);
    let classes = classes_of(&p);
    assert_eq!(classes.len(), 1);
    assert_eq!(classes[0].multiplicity, 1);
    assert_eq!(classes[0].representative.dim_vector(), &[2]);
}

#[test]
fn krull_schmidt_of_the_zero_module_has_no_classes() {
    let a = linear_an(3, PrimeField::new(2).unwrap());
    let z = Module::zero(&a);
    assert!(classes_of(&z).is_empty());
}

// The corner-ring inheritance must land on the same matrix the radical
// chain lands on, entry for entry: every consumer of radical coordinates
// compares them for equality.
#[test]
fn inherited_radicals_are_the_freshly_computed_ones() {
    for field in [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()] {
        let a3 = linear_an(3, field);
        let dn = dual_numbers(field);
        let tp = truncated_poly(3, field).unwrap();
        let p0 = Module::projective(&a3, 0);
        let s0 = Module::simple(&a3, 0);
        let s2 = Module::simple(&a3, 2);
        let dual = Module::projective(&dn, 0);
        let trunc = Module::projective(&tp, 0);
        let (a, _, _) = direct_sum(&[&p0, &s0, &s2, &p0]);
        let (b, _, _) = direct_sum(&[&dual, &dual, &Module::simple(&dn, 0)]);
        let (c, _, _) = direct_sum(&[&trunc, &trunc, &trunc]);
        for m in [a, b, c] {
            let d = decompose(&m);
            assert_eq!(d.endos().len(), d.summands().len());
            for (k, summand) in d.summands().iter().enumerate() {
                let fresh = EndoAlgebra::new(summand);
                let inherited = &d.endos()[k];
                assert_eq!(inherited.dim(), fresh.dim(), "summand {k}");
                assert_eq!(
                    inherited.radical_basis(),
                    fresh.radical_basis(),
                    "summand {k} over F_{}",
                    field.modulus()
                );
                assert_eq!(inherited.quotient_dim(), fresh.quotient_dim());
                assert_eq!(inherited.is_local(), fresh.is_local());
                assert_eq!(
                    inherited.semisimple_factor_count(),
                    fresh.semisimple_factor_count()
                );
                assert!(inherited.module().ptr_eq(summand), "summand {k}");
            }
        }
    }
}

#[test]
fn iso_classes_carry_the_endomorphism_algebra_of_their_representative() {
    let field = PrimeField::new(5).unwrap();
    let a = linear_an(3, field);
    let p0 = Module::projective(&a, 0);
    let s2 = Module::simple(&a, 2);
    let (sum, _, _) = direct_sum(&[&p0, &s2, &p0]);
    for class in classes_of(&sum) {
        assert!(class.endo.module().ptr_eq(&class.representative));
        assert!(class.endo.is_local());
        assert_eq!(
            class.endo.radical_basis(),
            EndoAlgebra::new(&class.representative).radical_basis()
        );
    }
}

#[test]
fn decompose_is_deterministic_across_calls() {
    let field = PrimeField::new(2).unwrap();
    let a = linear_an(3, field);
    let s = Module::simple(&a, 0);
    let p1 = Module::projective(&a, 1);
    let (sum, _, _) = direct_sum(&[&s, &p1, &s]);
    let first = decompose(&sum);
    let second = decompose(&sum);
    let dims = |d: &Decomposition| -> Vec<Vec<usize>> {
        d.summands()
            .iter()
            .map(|s| s.dim_vector().to_vec())
            .collect()
    };
    assert_eq!(dims(&first), dims(&second));
    assert_eq!(first.certificates(), second.certificates());
    for (a, b) in first
        .split()
        .inclusions()
        .iter()
        .zip(second.split().inclusions())
    {
        for v in 0..3 {
            assert_eq!(a.map_at(v), b.map_at(v));
        }
    }
}
