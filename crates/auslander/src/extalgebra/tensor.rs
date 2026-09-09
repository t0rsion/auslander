use crate::ext::{ExtClass, ProductWitness};
use crate::field::{Fp, PrimeField};

/// One deterministic tensor for a bounded Yoneda product.
///
/// For basis classes `e_i` and `f_j`, `basis_product(i, j)` holds the
/// coordinates of `e_i.then(f_j)` in the output complement basis. The tensor
/// also keeps that product class and its chain-lift witness.
#[derive(Clone, Debug)]
pub struct MultiplicationTensor {
    pub(super) left_degree: usize,
    pub(super) right_degree: usize,
    pub(super) left_dim: usize,
    pub(super) right_dim: usize,
    pub(super) output_dim: usize,
    // Entries are grouped by (left basis index, right basis index), then by
    // output coordinate. Product classes and witnesses use the same first two
    // indices.
    pub(super) coefficients: Vec<Fp>,
    pub(super) products: Vec<ExtClass>,
    pub(super) witnesses: Vec<ProductWitness>,
}

impl MultiplicationTensor {
    accessor_methods! {
        /// Degree of the left factor.
        pub left_degree() -> usize = |this| this.left_degree;
        /// Degree of the right factor.
        pub right_degree() -> usize = |this| this.right_degree;
        /// Degree of the output.
        pub output_degree() -> usize = |this| this.left_degree + this.right_degree;
        /// Dimension of the left input space.
        pub left_dim() -> usize = |this| this.left_dim;
        /// Dimension of the right input space.
        pub right_dim() -> usize = |this| this.right_dim;
        /// Dimension of the output space.
        pub output_dim() -> usize = |this| this.output_dim;
        /// Tensor entries in `(left basis, right basis, output coordinate)` order.
        pub coefficients() -> &[Fp] = |this| &this.coefficients;
        /// Product classes in `(left basis, right basis)` order.
        pub classes() -> &[ExtClass] = |this| &this.products;
        /// Chain-lift witnesses in `(left basis, right basis)` order.
        pub witnesses() -> &[ProductWitness] = |this| &this.witnesses;
    }

    fn pair_offset(&self, left: usize, right: usize) -> Option<usize> {
        (left < self.left_dim && right < self.right_dim)
            .then(|| {
                left.checked_mul(self.right_dim)?
                    .checked_add(right)?
                    .checked_mul(self.output_dim)
            })
            .flatten()
    }

    /// Coordinates of the product of two basis classes.
    pub fn basis_product(&self, left: usize, right: usize) -> Option<&[Fp]> {
        let offset = self.pair_offset(left, right)?;
        self.coefficients.get(offset..offset + self.output_dim)
    }

    /// The witness for the product of two basis classes.
    pub fn witness(&self, left: usize, right: usize) -> Option<&ProductWitness> {
        let index = left.checked_mul(self.right_dim)?.checked_add(right)?;
        self.witnesses.get(index)
    }

    /// The stored class for the product of two basis classes.
    pub fn product(&self, left: usize, right: usize) -> Option<&ExtClass> {
        let index = left.checked_mul(self.right_dim)?.checked_add(right)?;
        self.products.get(index)
    }

    pub(super) fn apply(&self, left: &[Fp], right: &[Fp], field: PrimeField) -> Option<Vec<Fp>> {
        if left.len() != self.left_dim || right.len() != self.right_dim {
            return None;
        }
        let mut output = vec![field.zero(); self.output_dim];
        for (left_index, &left_value) in left.iter().enumerate() {
            if left_value.is_zero() {
                continue;
            }
            for (right_index, &right_value) in right.iter().enumerate() {
                if right_value.is_zero() {
                    continue;
                }
                let factor = field.mul(left_value, right_value);
                let coordinates = self
                    .basis_product(left_index, right_index)
                    .expect("a tensor has one coordinate block per basis pair");
                for (output_value, &coefficient) in output.iter_mut().zip(coordinates) {
                    *output_value = field.add(*output_value, field.mul(factor, coefficient));
                }
            }
        }
        Some(output)
    }
}

/// One basis-pair Yoneda product in canonical graded order.
///
/// [`crate::extalgebra::ExtAlgebra::product_records`] orders these records by
/// left degree, left basis index, right degree, then right basis index.
#[derive(Clone, Debug)]
pub struct ProductRecord<'a> {
    pub(super) left_degree: usize,
    pub(super) left_basis: usize,
    pub(super) right_degree: usize,
    pub(super) right_basis: usize,
    pub(super) coordinates: &'a [Fp],
    pub(super) class: &'a ExtClass,
    pub(super) witness: &'a ProductWitness,
}

impl ProductRecord<'_> {
    accessor_methods! {
        /// Degree of the left factor.
        pub left_degree() -> usize = |this| this.left_degree;
        /// Basis index of the left factor.
        pub left_basis() -> usize = |this| this.left_basis;
        /// Degree of the right factor.
        pub right_degree() -> usize = |this| this.right_degree;
        /// Basis index of the right factor.
        pub right_basis() -> usize = |this| this.right_basis;
        /// Product coordinates in the output complement basis.
        pub coordinates() -> &[Fp] = |this| this.coordinates;
        /// The stored product class.
        pub class() -> &ExtClass = |this| this.class;
        /// The stored chain-lift witness.
        pub witness() -> &ProductWitness = |this| this.witness;
    }
}

pub(super) struct ProductRecords<'a> {
    pub(super) algebra: &'a super::algebra::ExtAlgebra,
    pub(super) left_degree: usize,
    pub(super) left_basis: usize,
    pub(super) right_degree: usize,
    pub(super) right_basis: usize,
}

impl<'a> Iterator for ProductRecords<'a> {
    type Item = ProductRecord<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.left_degree <= self.algebra.bound {
            let left_basis_dim = self.algebra.bases[self.left_degree].len();
            if self.left_basis == left_basis_dim {
                self.left_degree += 1;
                self.left_basis = 0;
                self.right_degree = 0;
                self.right_basis = 0;
                continue;
            }
            if self.right_degree > self.algebra.bound - self.left_degree {
                self.left_basis += 1;
                self.right_degree = 0;
                self.right_basis = 0;
                continue;
            }
            let right_basis_dim = self.algebra.bases[self.right_degree].len();
            if self.right_basis == right_basis_dim {
                self.right_degree += 1;
                self.right_basis = 0;
                continue;
            }
            let left_degree = self.left_degree;
            let left_basis = self.left_basis;
            let right_degree = self.right_degree;
            let right_basis = self.right_basis;
            self.right_basis += 1;
            let tensor = self
                .algebra
                .multiplication(left_degree, right_degree)
                .expect("every degree pair through the bound has a tensor");
            return Some(ProductRecord {
                left_degree,
                left_basis,
                right_degree,
                right_basis,
                coordinates: tensor
                    .basis_product(left_basis, right_basis)
                    .expect("a tensor has every basis pair"),
                class: tensor
                    .product(left_basis, right_basis)
                    .expect("a tensor has every product class"),
                witness: tensor
                    .witness(left_basis, right_basis)
                    .expect("a tensor has every product witness"),
            });
        }
        None
    }
}
