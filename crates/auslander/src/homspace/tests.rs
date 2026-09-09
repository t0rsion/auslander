use super::core::morphism_from_flat;
use super::*;
use crate::algebra::{commutative_square, dual_numbers, linear_an};
use crate::decompose::add_morphisms;
use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, zero_morphism};
use crate::module::{Module, direct_sum};

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn fixture_endpoints() -> Vec<(Module, Module)> {
    let field = f5();
    let mut endpoints = Vec::new();
    for algebra in [
        linear_an(3, field),
        dual_numbers(field),
        commutative_square(field),
    ] {
        let last = algebra.quiver().num_vertices() - 1;
        let p = Module::projective(&algebra, 0);
        let s = Module::simple(&algebra, last);
        let (sum, _, _) = direct_sum(&[&p, &s, &p]);
        endpoints.push((sum.clone(), sum));
        endpoints.push((p, direct_sum(&[&s, &s]).0));
    }
    endpoints
}

fn fixture_spaces() -> Vec<HomSpace> {
    fixture_endpoints()
        .iter()
        .map(|(m, n)| HomSpace::new(m, n).unwrap())
        .collect()
}

fn unit(dim: usize, k: usize, field: &PrimeField) -> Vec<Fp> {
    let mut v = vec![field.zero(); dim];
    v[k] = field.one();
    v
}

#[test]
fn basis_round_trip_recovers_coordinates() {
    for space in fixture_spaces() {
        let field = space.source().field();
        for k in 0..space.dim() {
            let coords = unit(space.dim(), k, &field);
            let f = space.morphism(&coords);
            assert_eq!(f, space.basis()[k], "unit {k} rebuilds basis element {k}");
            assert_eq!(space.coords(&f).unwrap(), coords);
        }
        let mixed: Vec<Fp> = (0..space.dim() as i64).map(|i| field.elem(i + 1)).collect();
        assert_eq!(space.coords(&space.morphism(&mixed)).unwrap(), mixed);
    }
}

#[test]
fn flat_rows_stack_the_vertex_matrices_row_major() {
    let algebra = linear_an(3, f5());
    let p0 = Module::projective(&algebra, 0);
    let space = HomSpace::new(&p0, &p0).unwrap();
    assert_eq!(space.flat.cols(), 3);
    assert_eq!(space.dim(), 1);
    let expected = flat_row(&space.basis()[0]);
    assert_eq!(space.flat.row(0), expected.as_slice());
}

#[test]
fn recomputed_compatible_spaces_have_identical_bases() {
    for (m, n) in fixture_endpoints() {
        let first = HomSpace::new(&m, &n).unwrap();
        let second = HomSpace::new(&m, &n).unwrap();
        assert!(first.is_compatible(&second));
        assert_eq!(first.flat.entries_u64(), second.flat.entries_u64());
        for (f, g) in first.basis().iter().zip(second.basis()) {
            assert_eq!(f, g);
        }
    }
}

#[test]
fn coords_rejects_wrong_endpoints_with_typed_errors() {
    let algebra = linear_an(3, f5());
    let p0 = Module::projective(&algebra, 0);
    let s0 = Module::simple(&algebra, 0);
    let space = HomSpace::new(&p0, &s0).unwrap();
    let p0_copy = Module::projective(&algebra, 0);
    let s0_copy = Module::simple(&algebra, 0);
    let wrong_source = HomSpace::new(&p0_copy, &s0).unwrap().basis_morphism(0);
    assert_eq!(
        space.coords(&wrong_source).unwrap_err(),
        HomSpaceError::SourceMismatch
    );
    let wrong_target = HomSpace::new(&p0, &s0_copy).unwrap().basis_morphism(0);
    assert_eq!(
        space.coords(&wrong_target).unwrap_err(),
        HomSpaceError::TargetMismatch
    );
    assert_eq!(
        space
            .subspace(std::slice::from_ref(&wrong_target))
            .unwrap_err(),
        HomSpaceError::TargetMismatch
    );
    let full = space.full_subspace();
    assert_eq!(
        full.contains(&wrong_source).unwrap_err(),
        HomSpaceError::SourceMismatch
    );
    let quotient = full.quotient_by(&space.subspace(&[]).unwrap()).unwrap();
    assert_eq!(
        quotient.reduce(&wrong_source).unwrap_err(),
        HomSpaceError::SourceMismatch
    );
}

#[test]
fn hom_space_new_rejects_modules_over_different_algebras() {
    let a = linear_an(3, f5());
    let b = linear_an(3, f5());
    let m = Module::simple(&a, 0);
    let n = Module::simple(&b, 0);
    assert_eq!(
        HomSpace::new(&m, &n).unwrap_err(),
        crate::hom::HomError::DifferentAlgebras
    );
}

#[test]
fn subspace_rref_is_invariant_under_permuted_and_rescaled_spanning_sets() {
    for space in fixture_spaces() {
        if space.dim() < 2 {
            continue;
        }
        let field = space.source().field();
        let f = space.morphism(&unit(space.dim(), 0, &field));
        let g = space.morphism(&unit(space.dim(), 1, &field));
        let mut mixed = unit(space.dim(), 0, &field);
        mixed[1] = field.elem(2);
        let h = space.morphism(&mixed);
        let scaled_coords: Vec<Fp> = unit(space.dim(), 1, &field)
            .iter()
            .map(|&c| field.mul(c, field.elem(3)))
            .collect();
        let g_scaled = space.morphism(&scaled_coords);
        let first = space.subspace(&[f.clone(), g.clone(), h.clone()]).unwrap();
        let second = space.subspace(&[h, g_scaled, f]).unwrap();
        assert_eq!(first, second);
        assert_eq!(
            first.rref_basis().entries_u64(),
            second.rref_basis().entries_u64()
        );
        assert_eq!(first.dim(), 2);
    }
}

#[test]
fn empty_spanning_set_gives_the_zero_subspace() {
    for space in fixture_spaces() {
        let sub = space.subspace(&[]).unwrap();
        assert_eq!(sub.dim(), 0);
        let zero = zero_morphism(space.source(), space.target()).unwrap();
        assert_eq!(sub.witness_contains(&zero).unwrap(), Some(Vec::new()));
        if space.dim() > 0 {
            assert!(!sub.contains(&space.basis()[0]).unwrap());
        }
    }
}

#[test]
fn witness_contains_returns_solving_coordinates() {
    for space in fixture_spaces() {
        if space.dim() < 2 {
            continue;
        }
        let field = space.source().field();
        let sub = space
            .subspace(&[space.basis()[0].clone(), space.basis()[1].clone()])
            .unwrap();
        let mut coords = unit(space.dim(), 0, &field);
        coords[1] = field.elem(4);
        let f = space.morphism(&coords);
        let witness = sub.witness_contains(&f).unwrap().expect("f spans inside");
        let rebuilt = morphism_from_flat(
            space.source(),
            space.target(),
            &row_times(&witness, sub.rref_basis(), &field),
        );
        assert_eq!(rebuilt, f, "witness coordinates rebuild the morphism");
        if space.dim() > 2 {
            let outside = space.morphism(&unit(space.dim(), 2, &field));
            assert_eq!(sub.witness_contains(&outside).unwrap(), None);
        }
    }
}

#[test]
fn complement_rule_is_deterministic_across_recomputation() {
    for (m, n) in fixture_endpoints() {
        let build = |space: &HomSpace| {
            let z = space.full_subspace();
            let sub = space.subspace(&space.basis()[..1]).unwrap();
            z.quotient_by(&sub).unwrap()
        };
        let first_space = HomSpace::new(&m, &n).unwrap();
        let second_space = HomSpace::new(&m, &n).unwrap();
        if first_space.dim() == 0 {
            continue;
        }
        let first = build(&first_space);
        let second = build(&second_space);
        assert_eq!(
            first.complement_basis().entries_u64(),
            second.complement_basis().entries_u64()
        );
        assert_eq!(
            first.subspace().rref_basis().entries_u64(),
            second.subspace().rref_basis().entries_u64()
        );
    }
}

#[test]
fn complement_rows_come_from_the_ambient_rref_in_scan_order() {
    for space in fixture_spaces() {
        let z = space.full_subspace();
        let sub = space.subspace(&[]).unwrap();
        let quotient = z.quotient_by(&sub).unwrap();
        assert_eq!(
            quotient.complement_basis().entries_u64(),
            z.rref_basis().entries_u64(),
            "the complement of the zero subspace keeps every ambient row"
        );
    }
}

#[test]
fn quotient_reduce_returns_complement_coordinates_plus_a_subspace_member() {
    for space in fixture_spaces() {
        let field = space.source().field();
        let z = space.full_subspace();
        for sub_size in 0..=space.dim().min(2) {
            let sub = space.subspace(&space.basis()[..sub_size]).unwrap();
            let quotient = z.quotient_by(&sub).unwrap();
            assert_eq!(quotient.dim() + sub.dim(), z.dim());
            let mut probes: Vec<Morphism> = space.basis().to_vec();
            if space.dim() > 0 {
                let mixed: Vec<Fp> = (0..space.dim() as i64).map(|i| field.elem(i + 2)).collect();
                probes.push(space.morphism(&mixed));
            }
            for f in &probes {
                let (coords, member) = quotient.reduce(f).unwrap();
                assert_eq!(coords.len(), quotient.dim());
                assert!(sub.contains(&member).unwrap());
                let rebuilt = add_morphisms(&quotient.representative(&coords), &member);
                assert_eq!(rebuilt, *f, "representative + member = original");
            }
        }
    }
}

#[test]
fn reduce_rejects_an_element_outside_the_ambient_subspace() {
    for space in fixture_spaces() {
        if space.dim() < 2 {
            continue;
        }
        let z = space.subspace(&space.basis()[..1]).unwrap();
        let sub = space.subspace(&[]).unwrap();
        let quotient = z.quotient_by(&sub).unwrap();
        assert_eq!(
            quotient.reduce(&space.basis()[1]).unwrap_err(),
            HomSpaceError::OutsideSubspace
        );
    }
}

#[test]
fn quotient_by_rejects_incompatible_and_uncontained_subspaces() {
    let algebra = linear_an(3, f5());
    let p0 = Module::projective(&algebra, 0);
    let s0 = Module::simple(&algebra, 0);
    let space = HomSpace::new(&p0, &s0).unwrap();
    assert!(space.dim() >= 1);
    let small = space.subspace(&[]).unwrap();
    let full = space.full_subspace();
    assert_eq!(
        small.quotient_by(&full).unwrap_err(),
        HomSpaceError::NotContained
    );
    let p0_copy = Module::projective(&algebra, 0);
    let other_space = HomSpace::new(&p0_copy, &s0).unwrap();
    assert_eq!(
        full.quotient_by(&other_space.full_subspace()).unwrap_err(),
        HomSpaceError::IncompatibleSubspaces
    );
}
