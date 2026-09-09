use crate::ext::ExtSpace;
use crate::field::Fp;
use crate::resolution::{ResolutionEnd, resolve};

use super::algebra::{ExtAlgebra, ExtAlgebraCut, ExtAlgebraOutcome};
use super::product::basis_matches;

struct BilinearityZeros<'a> {
    left: &'a [Fp],
    right: &'a [Fp],
    output: &'a [Fp],
    field: crate::field::PrimeField,
}

impl ExtAlgebra {
    /// Rebuilds every stored Ext space, tensor, witness, unit, and algebra law.
    pub fn verify(&self) -> bool {
        if !self.verify_shape() {
            return false;
        }
        let Some(fresh_spaces) = self.fresh_spaces() else {
            return false;
        };
        self.stored_spaces_match(&fresh_spaces)
            && self.verify_tensors(&fresh_spaces)
            && self.verify_unit()
            && self.verify_bilinearity()
            && self.verify_associativity()
    }

    fn verify_shape(&self) -> bool {
        verify_guard!(
            self.bound != usize::MAX
                && self.spaces.len() == self.bound + 1
                && self.bases.len() == self.bound + 1
                && self.products.len() == self.bound + 1
                && resolve(&self.module, self.bound).end == self.resolution_end
        );
        true
    }

    fn fresh_spaces(&self) -> Option<Vec<ExtSpace>> {
        let mut fresh_spaces = Vec::with_capacity(self.spaces.len());
        for degree in 0..self.spaces.len() {
            let Ok(space) = ExtSpace::new(&self.module, &self.module, degree) else {
                return None;
            };
            fresh_spaces.push(space);
        }
        Some(fresh_spaces)
    }

    fn stored_spaces_match(&self, fresh_spaces: &[ExtSpace]) -> bool {
        self.spaces
            .iter()
            .zip(fresh_spaces)
            .enumerate()
            .all(|(degree, (stored, fresh))| stored.degree() == degree && stored.matches(fresh))
            && self
                .bases
                .iter()
                .zip(&self.spaces)
                .all(|(basis, space)| basis_matches(space, basis))
            && self.unit.space().matches(&self.spaces[0])
            && self.spaces[0]
                .identity_class()
                .is_ok_and(|identity| identity.equals(&self.unit) == Ok(true))
    }

    fn verify_tensors(&self, fresh_spaces: &[ExtSpace]) -> bool {
        self.products
            .iter()
            .enumerate()
            .all(|(left_degree, row)| self.verify_tensor_row(fresh_spaces, left_degree, row))
    }

    fn verify_tensor_row(
        &self,
        fresh_spaces: &[ExtSpace],
        left_degree: usize,
        row: &[super::tensor::MultiplicationTensor],
    ) -> bool {
        row.len() == self.bound - left_degree + 1
            && row.iter().enumerate().all(|(right_degree, tensor)| {
                self.verify_tensor(fresh_spaces, left_degree, right_degree, tensor)
            })
    }

    fn verify_tensor(
        &self,
        fresh_spaces: &[ExtSpace],
        left_degree: usize,
        right_degree: usize,
        tensor: &super::tensor::MultiplicationTensor,
    ) -> bool {
        let output_degree = left_degree + right_degree;
        self.tensor_shape(left_degree, right_degree, output_degree, tensor)
            && self.bases[left_degree]
                .iter()
                .enumerate()
                .all(|(left_index, left)| {
                    self.bases[right_degree]
                        .iter()
                        .enumerate()
                        .all(|(right_index, right)| {
                            self.verify_product_pair(
                                output_degree,
                                fresh_spaces,
                                tensor,
                                (left_index, right_index),
                                (left, right),
                            )
                        })
                })
    }

    fn tensor_shape(
        &self,
        left_degree: usize,
        right_degree: usize,
        output_degree: usize,
        tensor: &super::tensor::MultiplicationTensor,
    ) -> bool {
        let field = self.module.field();
        tensor.left_degree == left_degree
            && tensor.right_degree == right_degree
            && tensor.left_dim == self.bases[left_degree].len()
            && tensor.right_dim == self.bases[right_degree].len()
            && tensor.output_dim == self.bases[output_degree].len()
            && tensor
                .left_dim
                .checked_mul(tensor.right_dim)
                .is_some_and(|pairs| pairs == tensor.witnesses.len())
            && tensor
                .left_dim
                .checked_mul(tensor.right_dim)
                .is_some_and(|pairs| pairs == tensor.products.len())
            && tensor
                .left_dim
                .checked_mul(tensor.right_dim)
                .and_then(|pairs| pairs.checked_mul(tensor.output_dim))
                .is_some_and(|entries| entries == tensor.coefficients.len())
            && tensor
                .coefficients
                .iter()
                .all(|coefficient| coefficient.raw() < field.modulus())
    }

    fn verify_product_pair(
        &self,
        output_degree: usize,
        fresh_spaces: &[ExtSpace],
        tensor: &super::tensor::MultiplicationTensor,
        indices: (usize, usize),
        classes: (&crate::ext::ExtClass, &crate::ext::ExtClass),
    ) -> bool {
        let (left_index, right_index) = indices;
        let (left, right) = classes;
        let_or_false!(Some(coordinates) = tensor.basis_product(left_index, right_index));
        let_or_false!(Some(witness) = tensor.witness(left_index, right_index));
        let_or_false!(Some(product) = tensor.product(left_index, right_index));
        product.space().matches(&self.spaces[output_degree])
            && product.coordinates() == coordinates
            && product.coordinates().len() == self.spaces[output_degree].dim()
            && product
                .coordinates()
                .iter()
                .all(|coordinate| coordinate.raw() < self.module.field().modulus())
            && witness.verify_against(left, right, product, &fresh_spaces[output_degree])
    }

    fn verify_unit(&self) -> bool {
        let field = self.module.field();
        self.bases.iter().enumerate().all(|(degree, basis)| {
            let_or_false!(Some(left_tensor) = self.multiplication(0, degree));
            let_or_false!(Some(right_tensor) = self.multiplication(degree, 0));
            basis.iter().all(|class| {
                left_tensor
                    .apply(self.unit.coordinates(), class.coordinates(), field)
                    .is_some_and(|coordinates| coordinates == class.coordinates())
                    && right_tensor
                        .apply(class.coordinates(), self.unit.coordinates(), field)
                        .is_some_and(|coordinates| coordinates == class.coordinates())
            })
        })
    }

    fn verify_bilinearity(&self) -> bool {
        self.products.iter().all(|row| {
            row.iter()
                .all(|tensor| self.verify_tensor_bilinearity(tensor))
        })
    }

    fn verify_tensor_bilinearity(&self, tensor: &super::tensor::MultiplicationTensor) -> bool {
        let field = self.module.field();
        let left_zero = vec![field.zero(); tensor.left_dim];
        let right_zero = vec![field.zero(); tensor.right_dim];
        let output_zero = vec![field.zero(); tensor.output_dim];
        let zeros = BilinearityZeros {
            left: &left_zero,
            right: &right_zero,
            output: &output_zero,
            field,
        };
        tensor.apply(&left_zero, &right_zero, field) == Some(output_zero.clone())
            && self.bases[tensor.left_degree]
                .iter()
                .enumerate()
                .all(|(left_index, left)| {
                    self.verify_basis_bilinearity(tensor, left_index, left, &zeros)
                })
    }

    fn verify_basis_bilinearity(
        &self,
        tensor: &super::tensor::MultiplicationTensor,
        left_index: usize,
        left: &crate::ext::ExtClass,
        zeros: &BilinearityZeros<'_>,
    ) -> bool {
        self.bases[tensor.right_degree]
            .iter()
            .enumerate()
            .all(|(right_index, right)| {
                let left_twice = left.add(left).expect("one basis space");
                let right_twice = right.add(right).expect("one basis space");
                let product = tensor
                    .basis_product(left_index, right_index)
                    .expect("a tensor has every basis pair");
                let twice_product: Vec<Fp> = product
                    .iter()
                    .map(|&coordinate| zeros.field.add(coordinate, coordinate))
                    .collect();
                tensor.apply(left.coordinates(), zeros.right, zeros.field)
                    == Some(zeros.output.to_vec())
                    && tensor.apply(zeros.left, right.coordinates(), zeros.field)
                        == Some(zeros.output.to_vec())
                    && tensor.apply(left_twice.coordinates(), right.coordinates(), zeros.field)
                        == Some(twice_product.clone())
                    && tensor.apply(left.coordinates(), right_twice.coordinates(), zeros.field)
                        == Some(twice_product)
            })
    }

    fn verify_associativity(&self) -> bool {
        let field = self.module.field();
        for left_degree in 0..=self.bound {
            for middle_degree in 0..=self.bound - left_degree {
                for right_degree in 0..=self.bound - left_degree - middle_degree {
                    let left_middle = self
                        .multiplication(left_degree, middle_degree)
                        .expect("a bounded degree pair has a tensor");
                    let middle_right = self
                        .multiplication(middle_degree, right_degree)
                        .expect("a bounded degree pair has a tensor");
                    let left_then_right = self
                        .multiplication(left_degree + middle_degree, right_degree)
                        .expect("a bounded degree pair has a tensor");
                    let left_then_middle = self
                        .multiplication(left_degree, middle_degree + right_degree)
                        .expect("a bounded degree pair has a tensor");
                    for left in &self.bases[left_degree] {
                        for middle in &self.bases[middle_degree] {
                            for right in &self.bases[right_degree] {
                                let left_middle_coordinates = left_middle
                                    .apply(left.coordinates(), middle.coordinates(), field)
                                    .expect("basis coordinates fit their tensor");
                                let middle_right_coordinates = middle_right
                                    .apply(middle.coordinates(), right.coordinates(), field)
                                    .expect("basis coordinates fit their tensor");
                                let left_associated = left_then_right
                                    .apply(&left_middle_coordinates, right.coordinates(), field)
                                    .expect("product coordinates fit their tensor");
                                let right_associated = left_then_middle
                                    .apply(left.coordinates(), &middle_right_coordinates, field)
                                    .expect("product coordinates fit their tensor");
                                if left_associated != right_associated {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
        }
        true
    }
}

impl ExtAlgebraCut {
    /// Rebuilds the layer and rechecks its typed cut.
    pub fn verify(&self) -> bool {
        self.algebra.verify()
            && self.first_omitted_degree == self.algebra.bound + 1
            && matches!(
                self.algebra.resolution_end,
                ResolutionEnd::Cut { at } if at == self.algebra.bound
            )
    }
}

impl ExtAlgebraOutcome {
    /// Rechecks the complete algebra or the exact layer and its cut.
    pub fn verify(&self) -> bool {
        match self {
            Self::Complete(algebra) => {
                algebra.verify() && matches!(algebra.resolution_end, ResolutionEnd::Finite)
            }
            Self::Cut(cut) => cut.verify(),
        }
    }
}
