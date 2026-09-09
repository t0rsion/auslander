use super::*;
use crate::algebra::{dual_numbers, linear_an};
use crate::ext::ExtClass;
use crate::field::PrimeField;
use crate::module::Module;
use crate::resolution::ResolutionEnd;

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn dual_number_simple() -> Module {
    let algebra = dual_numbers(f5());
    Module::simple(&algebra, 0)
}

#[test]
fn a_finite_resolution_gives_a_complete_algebra_through_the_requested_bound() {
    let algebra = linear_an(3, f5());
    let source = Module::simple(&algebra, 0);
    let ExtAlgebraOutcome::Complete(ext) = ExtAlgebraOutcome::compute(&source, 3).unwrap() else {
        panic!("S_0 over linear A_3 has finite projective dimension");
    };
    assert_eq!(ext.bound(), 3);
    assert_eq!(ext.spaces().len(), 4);
    assert!(matches!(ext.resolution_end(), ResolutionEnd::Finite));
    assert!(ext.verify());
}

#[test]
fn a_cut_keeps_all_requested_exact_degrees_and_names_the_first_omitted_degree() {
    let source = dual_number_simple();
    let ExtAlgebraOutcome::Cut(cut) = ExtAlgebraOutcome::compute(&source, 3).unwrap() else {
        panic!("the dual-number simple has an unbounded minimal resolution");
    };
    assert_eq!(cut.algebra().spaces().len(), 4);
    assert_eq!(cut.first_omitted_degree(), 4);
    assert!(matches!(
        cut.algebra().resolution_end(),
        ResolutionEnd::Cut { at: 3 }
    ));
    assert!(cut.verify());
}

#[test]
fn tensors_use_the_same_order_as_then_with_witness() {
    let source = dual_number_simple();
    let ExtAlgebraOutcome::Cut(ext) = ExtAlgebraOutcome::compute(&source, 3).unwrap() else {
        panic!("the dual-number simple has an unbounded minimal resolution");
    };
    let ext = ext.algebra();
    let alpha = &ext.basis(1).unwrap()[0];
    let beta = &ext.basis(2).unwrap()[0];
    let (direct, witness) = alpha.then_with_witness(beta).unwrap();
    let tensor = ext.multiplication(1, 2).unwrap();
    let stored = ext.multiply(alpha, beta).unwrap();
    assert!(direct.equals(&stored).unwrap());
    assert!(witness.verify(alpha, beta, &direct));
    assert_eq!(
        tensor.basis_product(0, 0),
        Some(stored.coordinates()),
        "the degree (1, 2) tensor uses alpha.then(beta)"
    );
    assert!(ext.verify());
}

#[test]
fn repeated_builds_keep_bases_and_tensors_in_the_same_order() {
    let source = dual_number_simple();
    let ExtAlgebraOutcome::Cut(left) = ExtAlgebraOutcome::compute(&source, 3).unwrap() else {
        panic!("the dual-number simple has an unbounded minimal resolution");
    };
    let ExtAlgebraOutcome::Cut(right) = ExtAlgebraOutcome::compute(&source, 3).unwrap() else {
        panic!("the dual-number simple has an unbounded minimal resolution");
    };
    let (left, right) = (left.algebra(), right.algebra());
    for degree in 0..=left.bound() {
        assert!(
            left.space(degree)
                .unwrap()
                .matches(right.space(degree).unwrap())
        );
        assert_eq!(
            left.basis(degree)
                .unwrap()
                .iter()
                .map(ExtClass::coordinates)
                .collect::<Vec<_>>(),
            right
                .basis(degree)
                .unwrap()
                .iter()
                .map(ExtClass::coordinates)
                .collect::<Vec<_>>(),
            "basis degree {degree}"
        );
    }
    for left_degree in 0..=left.bound() {
        for right_degree in 0..=left.bound() - left_degree {
            assert_eq!(
                left.multiplication(left_degree, right_degree)
                    .unwrap()
                    .coefficients(),
                right
                    .multiplication(left_degree, right_degree)
                    .unwrap()
                    .coefficients(),
                "tensor degree ({left_degree}, {right_degree})"
            );
        }
    }
    let order: Vec<(usize, usize, usize, usize)> = left
        .product_records()
        .map(|record| {
            (
                record.left_degree(),
                record.left_basis(),
                record.right_degree(),
                record.right_basis(),
            )
        })
        .collect();
    assert!(order.windows(2).all(|pair| pair[0] <= pair[1]));
    let expected_records: usize = (0..=left.bound())
        .flat_map(|left_degree| {
            (0..=left.bound() - left_degree).map(move |right_degree| {
                left.basis(left_degree).unwrap().len() * left.basis(right_degree).unwrap().len()
            })
        })
        .sum();
    assert_eq!(order.len(), expected_records);
}

#[test]
fn verifier_rejects_a_changed_tensor_coefficient_and_a_changed_unit() {
    let source = dual_number_simple();
    let ExtAlgebraOutcome::Cut(cut) = ExtAlgebraOutcome::compute(&source, 3).unwrap() else {
        panic!("the dual-number simple has an unbounded minimal resolution");
    };
    let ext = cut.algebra();
    let field = ext.module().field();
    let mut wrong_tensor = ext.clone();
    let coefficient = wrong_tensor.products[1][1]
        .coefficients
        .first_mut()
        .expect("the degree (1, 1) tensor has one coefficient");
    *coefficient = field.add(*coefficient, field.one());
    assert!(!wrong_tensor.verify());

    let mut wrong_unit = ext.clone();
    wrong_unit.unit = wrong_unit.spaces[0].zero_class();
    assert!(!wrong_unit.verify());
}
