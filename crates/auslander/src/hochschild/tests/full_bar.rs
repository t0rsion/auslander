use std::sync::Arc;

use crate::algebra::{Algebra, BasisIdx};
use crate::completion::CompletionLimits;
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;
use crate::quiver::{ArrowId, Quiver};
use crate::relation::{Presentation, Relation};

fn add_entry(matrix: &mut DenseMat, row: usize, column: usize, value: Fp, field: &PrimeField) {
    matrix.set(row, column, field.add(matrix.get(row, column), value));
}

fn full_signed(value: Fp, negative: bool, field: &PrimeField) -> Fp {
    if negative { field.neg(value) } else { value }
}

fn full_tuples(dimension: usize, degree: usize) -> Vec<Vec<BasisIdx>> {
    let mut tuples = vec![Vec::new()];
    for _ in 0..degree {
        let mut next = Vec::with_capacity(tuples.len() * dimension);
        for tuple in tuples {
            for basis in 0..dimension {
                let mut extended = tuple.clone();
                extended.push(basis);
                next.push(extended);
            }
        }
        tuples = next;
    }
    tuples
}

fn full_rank(tuple: &[BasisIdx], dimension: usize) -> usize {
    tuple
        .iter()
        .fold(0, |rank, &basis| rank * dimension + basis)
}

fn add_full_product(
    matrix: &mut DenseMat,
    row: usize,
    target_rank: usize,
    dimension: usize,
    product: &[(BasisIdx, Fp)],
    negative: bool,
    field: &PrimeField,
) {
    for &(output, coefficient) in product {
        add_entry(
            matrix,
            row,
            target_rank * dimension + output,
            full_signed(coefficient, negative, field),
            field,
        );
    }
}

fn full_differential(algebra: &Algebra, degree: usize) -> DenseMat {
    let field = algebra.field();
    let dimension = algebra.dim();
    let source = full_tuples(dimension, degree);
    let target = full_tuples(dimension, degree + 1);
    let mut differential = DenseMat::zero(source.len() * dimension, target.len() * dimension);
    for (target_rank, tuple) in target.iter().enumerate() {
        for output in 0..dimension {
            if degree == 0 {
                add_full_product(
                    &mut differential,
                    output,
                    target_rank,
                    dimension,
                    &algebra.mul_basis(tuple[0], output),
                    false,
                    &field,
                );
                add_full_product(
                    &mut differential,
                    output,
                    target_rank,
                    dimension,
                    &algebra.mul_basis(output, tuple[0]),
                    true,
                    &field,
                );
                continue;
            }
            let first = full_rank(&tuple[1..], dimension) * dimension + output;
            add_full_product(
                &mut differential,
                first,
                target_rank,
                dimension,
                &algebra.mul_basis(tuple[0], output),
                false,
                &field,
            );
            for i in 1..=degree {
                let mut shortened = Vec::with_capacity(degree);
                shortened.extend_from_slice(&tuple[..i - 1]);
                for &(middle, coefficient) in &algebra.mul_basis(tuple[i - 1], tuple[i]) {
                    shortened.push(middle);
                    shortened.extend_from_slice(&tuple[i + 1..]);
                    let row = full_rank(&shortened, dimension) * dimension + output;
                    add_entry(
                        &mut differential,
                        row,
                        target_rank * dimension + output,
                        full_signed(coefficient, i % 2 == 1, &field),
                        &field,
                    );
                    shortened.truncate(i - 1);
                }
            }
            let last = full_rank(&tuple[..degree], dimension) * dimension + output;
            add_full_product(
                &mut differential,
                last,
                target_rank,
                dimension,
                &algebra.mul_basis(output, tuple[degree]),
                (degree + 1) % 2 == 1,
                &field,
            );
        }
    }
    differential
}

pub(super) fn full_bar_dimensions(algebra: &Algebra, max_degree: usize) -> Vec<usize> {
    let field = algebra.field();
    let mut dimensions = Vec::with_capacity(max_degree + 1);
    let mut previous: Option<DenseMat> = None;
    for degree in 0..=max_degree {
        let differential = full_differential(algebra, degree);
        if let Some(previous) = &previous {
            assert!(
                previous
                    .mul(&differential, &field)
                    .entries_u64()
                    .iter()
                    .flatten()
                    .all(|&x| x == 0)
            );
        }
        let cocycles = differential.left_kernel_basis(&field);
        let coboundaries =
            previous.map_or(0, |matrix: DenseMat| matrix.row_space_basis(&field).rows());
        dimensions.push(cocycles.rows() - coboundaries);
        previous = Some(differential);
    }
    dimensions
}

pub(super) fn center_dimension(algebra: &Algebra) -> usize {
    let field = algebra.field();
    let dimension = algebra.dim();
    let mut equations = DenseMat::zero(dimension, dimension * dimension);
    for central in 0..dimension {
        for basis in 0..dimension {
            for &(output, coefficient) in &algebra.mul_basis(central, basis) {
                add_entry(
                    &mut equations,
                    central,
                    basis * dimension + output,
                    coefficient,
                    &field,
                );
            }
            for &(output, coefficient) in &algebra.mul_basis(basis, central) {
                add_entry(
                    &mut equations,
                    central,
                    basis * dimension + output,
                    field.neg(coefficient),
                    &field,
                );
            }
        }
    }
    equations.left_kernel_basis(&field).rows()
}

fn add_outer_product_pair(
    equations: &mut DenseMat,
    algebra: &Algebra,
    field: &PrimeField,
    dimension: usize,
    left: usize,
    right: usize,
) {
    for &(middle, coefficient) in &algebra.mul_basis(left, right) {
        for output in 0..dimension {
            add_entry(
                equations,
                middle * dimension + output,
                (left * dimension + right) * dimension + output,
                coefficient,
                field,
            );
        }
    }
}

fn add_outer_action_pair(
    equations: &mut DenseMat,
    algebra: &Algebra,
    field: &PrimeField,
    dimension: usize,
    left: usize,
    right: usize,
) {
    for output in 0..dimension {
        for &(product, coefficient) in &algebra.mul_basis(output, right) {
            add_entry(
                equations,
                left * dimension + output,
                (left * dimension + right) * dimension + product,
                field.neg(coefficient),
                field,
            );
        }
        for &(product, coefficient) in &algebra.mul_basis(left, output) {
            add_entry(
                equations,
                right * dimension + output,
                (left * dimension + right) * dimension + product,
                field.neg(coefficient),
                field,
            );
        }
    }
}

fn outer_equations(algebra: &Algebra, field: &PrimeField, dimension: usize) -> DenseMat {
    let mut equations = DenseMat::zero(dimension * dimension, dimension * dimension * dimension);
    for left in 0..dimension {
        for right in 0..dimension {
            add_outer_product_pair(&mut equations, algebra, field, dimension, left, right);
            add_outer_action_pair(&mut equations, algebra, field, dimension, left, right);
        }
    }
    equations
}

fn add_inner_pair(
    inner: &mut DenseMat,
    algebra: &Algebra,
    field: &PrimeField,
    dimension: usize,
    generator: usize,
    input: usize,
) {
    for &(output, coefficient) in &algebra.mul_basis(input, generator) {
        add_entry(
            inner,
            generator,
            input * dimension + output,
            coefficient,
            field,
        );
    }
    for &(output, coefficient) in &algebra.mul_basis(generator, input) {
        add_entry(
            inner,
            generator,
            input * dimension + output,
            field.neg(coefficient),
            field,
        );
    }
}

fn inner_equations(algebra: &Algebra, field: &PrimeField, dimension: usize) -> DenseMat {
    let mut inner = DenseMat::zero(dimension, dimension * dimension);
    for generator in 0..dimension {
        for input in 0..dimension {
            add_inner_pair(&mut inner, algebra, field, dimension, generator, input);
        }
    }
    inner
}

pub(super) fn outer_derivation_dimension(algebra: &Algebra) -> usize {
    let field = algebra.field();
    let dimension = algebra.dim();
    let equations = outer_equations(algebra, &field, dimension);
    let derivations = equations.left_kernel_basis(&field);
    let inner = inner_equations(algebra, &field, dimension).row_space_basis(&field);
    assert!(
        inner
            .mul(&equations, &field)
            .entries_u64()
            .iter()
            .flatten()
            .all(|&value| value == 0)
    );
    assert!(inner.rows() <= derivations.rows());
    derivations.rows() - inner.rows()
}

pub(super) fn inhomogeneous_dual_numbers(field: PrimeField) -> Arc<Algebra> {
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let relation = Relation::new(
        &quiver,
        field,
        vec![
            (field.one(), vec![ArrowId(0), ArrowId(0)]),
            (field.one(), vec![ArrowId(0), ArrowId(0), ArrowId(0)]),
        ],
    )
    .unwrap();
    let nilpotence = Relation::new(
        &quiver,
        field,
        vec![(
            field.one(),
            vec![ArrowId(0), ArrowId(0), ArrowId(0), ArrowId(0)],
        )],
    )
    .unwrap();
    Algebra::new(
        Presentation::new(quiver, field, vec![relation, nilpotence]).unwrap(),
        &CompletionLimits::default(),
    )
    .unwrap()
}
