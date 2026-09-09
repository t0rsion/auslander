use crate::ext::{ExtClass, ExtSpace};

use super::errors::ExtAlgebraError;
use super::tensor::MultiplicationTensor;

pub(super) fn basis_classes(space: &ExtSpace) -> Vec<ExtClass> {
    let field = space.source().field();
    (0..space.dim())
        .map(|index| {
            let mut coordinates = vec![field.zero(); space.dim()];
            coordinates[index] = field.one();
            space
                .class_from_coordinates(&coordinates)
                .expect("a standard coordinate vector belongs to its Ext space")
        })
        .collect()
}

pub(super) fn basis_matches(space: &ExtSpace, basis: &[ExtClass]) -> bool {
    basis.len() == space.dim()
        && basis.iter().enumerate().all(|(index, class)| {
            let field = space.source().field();
            class.space().matches(space)
                && class.coordinates().len() == space.dim()
                && class
                    .coordinates()
                    .iter()
                    .enumerate()
                    .all(|(coordinate, &value)| {
                        value
                            == if coordinate == index {
                                field.one()
                            } else {
                                field.zero()
                            }
                    })
        })
}

pub(super) fn build_products(
    spaces: &[ExtSpace],
    bases: &[Vec<ExtClass>],
) -> Result<Vec<Vec<MultiplicationTensor>>, ExtAlgebraError> {
    let bound = spaces
        .len()
        .checked_sub(1)
        .expect("an Ext algebra stores degree zero");
    (0..=bound)
        .map(|left_degree| build_product_row(spaces, bases, bound, left_degree))
        .collect()
}

fn build_product_row(
    spaces: &[ExtSpace],
    bases: &[Vec<ExtClass>],
    bound: usize,
    left_degree: usize,
) -> Result<Vec<MultiplicationTensor>, ExtAlgebraError> {
    (0..=bound - left_degree)
        .map(|right_degree| build_tensor(spaces, bases, left_degree, right_degree))
        .collect()
}

fn build_tensor(
    spaces: &[ExtSpace],
    bases: &[Vec<ExtClass>],
    left_degree: usize,
    right_degree: usize,
) -> Result<MultiplicationTensor, ExtAlgebraError> {
    let output_degree = left_degree + right_degree;
    let left_dim = bases[left_degree].len();
    let right_dim = bases[right_degree].len();
    let output_dim = bases[output_degree].len();
    let (entries, pairs) =
        tensor_sizes(left_dim, right_dim, output_dim, left_degree, right_degree)?;
    let mut coefficients = Vec::with_capacity(entries);
    let mut products = Vec::with_capacity(pairs);
    let mut witnesses = Vec::with_capacity(pairs);
    for left in &bases[left_degree] {
        for right in &bases[right_degree] {
            let (product, witness) =
                left.then_with_witness(right)
                    .map_err(|error| ExtAlgebraError::Product {
                        left_degree,
                        right_degree,
                        error,
                    })?;
            if !product.space().matches(&spaces[output_degree]) {
                return Err(ExtAlgebraError::ProductSpaceDisagreement {
                    left_degree,
                    right_degree,
                });
            }
            coefficients.extend_from_slice(product.coordinates());
            products.push(product);
            witnesses.push(witness);
        }
    }
    debug_assert_eq!(coefficients.len(), entries);
    debug_assert_eq!(products.len(), pairs);
    debug_assert_eq!(witnesses.len(), pairs);
    Ok(MultiplicationTensor {
        left_degree,
        right_degree,
        left_dim,
        right_dim,
        output_dim,
        coefficients,
        products,
        witnesses,
    })
}

fn tensor_sizes(
    left_dim: usize,
    right_dim: usize,
    output_dim: usize,
    left_degree: usize,
    right_degree: usize,
) -> Result<(usize, usize), ExtAlgebraError> {
    let pairs = left_dim
        .checked_mul(right_dim)
        .ok_or(ExtAlgebraError::TensorSizeOverflow {
            left_degree,
            right_degree,
        })?;
    let entries = pairs
        .checked_mul(output_dim)
        .ok_or(ExtAlgebraError::TensorSizeOverflow {
            left_degree,
            right_degree,
        })?;
    Ok((entries, pairs))
}
