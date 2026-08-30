//! Bounded self-Ext algebras with deterministic bases and Yoneda tensors.
//!
//! [`ExtAlgebraOutcome::compute`] computes `Ext^d(M, M)` for every `d` through a caller
//! bound. It returns [`ExtAlgebraOutcome::Complete`] when the minimal
//! resolution of `M` ends within that bound. Otherwise it returns
//! [`ExtAlgebraOutcome::Cut`], which proves the next syzygy is nonzero.
//! Every stored grade and product tensor remains exact in either outcome.
//!
//! Products follow the right-module convention of [`ExtClass::then`]: an
//! entry in degree `(m, n)` is `Ext^m(M, M) x Ext^n(M, M) -> Ext^{m+n}(M, M)`.
//! The left factor acts first.

use crate::ext::{ExtClass, ExtClassError, ExtError, ExtSpace, ProductWitness};
use crate::field::Fp;
use crate::module::Module;
use crate::resolution::{ResolutionEnd, resolve};

/// A failure while building a bounded self-Ext algebra.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtAlgebraError {
    /// The requested bound cannot name its first omitted degree.
    DegreeOverflow,
    /// An Ext space could not be built.
    Ext(ExtError),
    /// A Yoneda product of two basis classes failed.
    Product {
        /// Degree of the left factor.
        left_degree: usize,
        /// Degree of the right factor.
        right_degree: usize,
        /// The rejected product.
        error: ExtClassError,
    },
    /// One product tensor would not fit in memory address space.
    TensorSizeOverflow {
        /// Degree of the left factor.
        left_degree: usize,
        /// Degree of the right factor.
        right_degree: usize,
    },
    /// A product space disagreed with the stored deterministic grade.
    ProductSpaceDisagreement {
        /// Degree of the left factor.
        left_degree: usize,
        /// Degree of the right factor.
        right_degree: usize,
    },
}

display_error! { ExtAlgebraError {
    Self::DegreeOverflow => "the requested Ext degree has no first omitted degree";
    Self::Ext(error) => "Ext layer: {error}";
    Self::Product { left_degree, right_degree, error } => "Yoneda product in degrees ({left_degree}, {right_degree}): {error}";
    Self::TensorSizeOverflow { left_degree, right_degree } => "the product tensor in degrees ({left_degree}, {right_degree}) overflows usize";
    Self::ProductSpaceDisagreement { left_degree, right_degree } => "Yoneda product in degrees ({left_degree}, {right_degree}) disagrees with its deterministic Ext space";
} }

error_source! { ExtAlgebraError {
    Self::Ext(error) => Some(error),
    Self::Product { error, .. } => Some(error),
    Self::DegreeOverflow | Self::TensorSizeOverflow { .. } | Self::ProductSpaceDisagreement { .. } => None,
} }

/// A class does not belong to this bounded self-Ext algebra.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtAlgebraProductError {
    /// The class is not an endomorphism self-Ext class of this module.
    OutsideAlgebra,
    /// The class degree lies above the stored bound.
    DegreeOutsideBound {
        /// Degree of the rejected class.
        degree: usize,
        /// Last stored degree.
        bound: usize,
    },
    /// A class has compatible endpoints but a different Ext-space basis.
    IncompatibleBasis {
        /// Degree of the rejected class.
        degree: usize,
    },
    /// The two input degrees do not fit inside the stored bound.
    DegreeSumOutsideBound {
        /// Degree of the left factor.
        left_degree: usize,
        /// Degree of the right factor.
        right_degree: usize,
        /// Last stored degree.
        bound: usize,
    },
}

display_error! { error ExtAlgebraProductError {
    Self::OutsideAlgebra => "the class is not a self-Ext class of this algebra's module";
    Self::DegreeOutsideBound { degree, bound } => "class degree {degree} is outside 0..={bound}";
    Self::IncompatibleBasis { degree } => "class degree {degree} uses a different Ext-space basis";
    Self::DegreeSumOutsideBound { left_degree, right_degree, bound } => "degree sum {left_degree} + {right_degree} is outside 0..={bound}";
} }

/// One deterministic tensor for a bounded Yoneda product.
///
/// For basis classes `e_i` and `f_j`, `basis_product(i, j)` holds the
/// coordinates of `e_i.then(f_j)` in the output complement basis. The tensor
/// also keeps that product class and its chain-lift witness.
#[derive(Clone, Debug)]
pub struct MultiplicationTensor {
    left_degree: usize,
    right_degree: usize,
    left_dim: usize,
    right_dim: usize,
    output_dim: usize,
    // Entries are grouped by (left basis index, right basis index), then by
    // output coordinate. Product classes and witnesses use the same first two
    // indices.
    coefficients: Vec<Fp>,
    products: Vec<ExtClass>,
    witnesses: Vec<ProductWitness>,
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

    fn apply(&self, left: &[Fp], right: &[Fp], field: crate::field::PrimeField) -> Option<Vec<Fp>> {
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
/// [`ExtAlgebra::product_records`] orders these records by left degree, left
/// basis index, right degree, then right basis index.
#[derive(Clone, Debug)]
pub struct ProductRecord<'a> {
    left_degree: usize,
    left_basis: usize,
    right_degree: usize,
    right_basis: usize,
    coordinates: &'a [Fp],
    class: &'a ExtClass,
    witness: &'a ProductWitness,
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

struct ProductRecords<'a> {
    algebra: &'a ExtAlgebra,
    left_degree: usize,
    left_basis: usize,
    right_degree: usize,
    right_basis: usize,
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

/// The exact self-Ext spaces and Yoneda tensors through one degree bound.
#[derive(Clone, Debug)]
pub struct ExtAlgebra {
    module: Module,
    bound: usize,
    resolution_end: ResolutionEnd,
    spaces: Vec<ExtSpace>,
    bases: Vec<Vec<ExtClass>>,
    unit: ExtClass,
    // Row p holds tensors with left degree p and right degrees 0 through
    // bound - p, in order.
    products: Vec<Vec<MultiplicationTensor>>,
}

impl ExtAlgebra {
    /// Builds the self-Ext algebra through `bound`.
    ///
    /// Every grade through `bound` and every product with output degree at
    /// most `bound` is exact. A finite resolution gives a complete algebra.
    /// A cut proves that degree `bound + 1` has a nonzero syzygy, but makes no
    /// claim about higher degrees.
    fn build(module: &Module, bound: usize) -> Result<ExtAlgebraOutcome, ExtAlgebraError> {
        let first_omitted_degree = bound
            .checked_add(1)
            .ok_or(ExtAlgebraError::DegreeOverflow)?;
        let resolution_end = resolve(module, bound).end;
        let spaces = (0..=bound)
            .map(|degree| ExtSpace::new(module, module, degree).map_err(ExtAlgebraError::Ext))
            .collect::<Result<Vec<_>, _>>()?;
        let bases: Vec<Vec<ExtClass>> = spaces.iter().map(basis_classes).collect();
        let unit = spaces[0]
            .identity_class()
            .expect("the degree-zero self-Ext space has its identity class");
        let products = build_products(&spaces, &bases)?;
        let algebra = ExtAlgebra {
            module: module.clone(),
            bound,
            resolution_end,
            spaces,
            bases,
            unit,
            products,
        };
        Ok(match resolution_end {
            ResolutionEnd::Finite => ExtAlgebraOutcome::Complete(algebra),
            ResolutionEnd::Cut { at } => {
                debug_assert_eq!(at, bound);
                ExtAlgebraOutcome::Cut(ExtAlgebraCut {
                    algebra,
                    first_omitted_degree,
                })
            }
        })
    }

    accessor_methods! {
        /// The module whose self-Ext algebra is stored.
        pub module() -> &Module = |this| &this.module;
        /// Last cohomological degree stored in this layer.
        pub bound() -> usize = |this| this.bound;
        /// How the minimal resolution ended at the requested bound.
        pub resolution_end() -> ResolutionEnd = |this| this.resolution_end;
        /// The deterministic self-Ext spaces, in degree order.
        pub spaces() -> &[ExtSpace] = |this| &this.spaces;
        /// The checked degree-zero Yoneda unit.
        pub unit() -> &ExtClass = |this| &this.unit;
    }

    /// The deterministic self-Ext space in `degree`.
    pub fn space(&self, degree: usize) -> Option<&ExtSpace> {
        self.spaces.get(degree)
    }

    /// The standard class basis in `degree`, in complement-row order.
    pub fn basis(&self, degree: usize) -> Option<&[ExtClass]> {
        self.bases.get(degree).map(Vec::as_slice)
    }

    /// The tensor for the ordered degrees `(left_degree, right_degree)`.
    ///
    /// Returns `None` when their sum lies above the caller bound.
    pub fn multiplication(
        &self,
        left_degree: usize,
        right_degree: usize,
    ) -> Option<&MultiplicationTensor> {
        self.products
            .get(left_degree)
            .and_then(|row| row.get(right_degree))
    }

    /// The basis-pair products in canonical graded order.
    pub fn product_records(&self) -> impl Iterator<Item = ProductRecord<'_>> {
        ProductRecords {
            algebra: self,
            left_degree: 0,
            left_basis: 0,
            right_degree: 0,
            right_basis: 0,
        }
    }

    /// Multiplies two classes with a stored tensor.
    ///
    /// Both classes must use the stored deterministic bases. The output is in
    /// the stored space of the summed degree.
    pub fn multiply(
        &self,
        left: &ExtClass,
        right: &ExtClass,
    ) -> Result<ExtClass, ExtAlgebraProductError> {
        let left_degree = self.check_class(left)?;
        let right_degree = self.check_class(right)?;
        let output_degree = left_degree.checked_add(right_degree).ok_or(
            ExtAlgebraProductError::DegreeSumOutsideBound {
                left_degree,
                right_degree,
                bound: self.bound,
            },
        )?;
        if output_degree > self.bound {
            return Err(ExtAlgebraProductError::DegreeSumOutsideBound {
                left_degree,
                right_degree,
                bound: self.bound,
            });
        }
        let field = self.module.field();
        let tensor = self
            .multiplication(left_degree, right_degree)
            .expect("every degree pair through the bound has a tensor");
        let coordinates = tensor
            .apply(left.coordinates(), right.coordinates(), field)
            .expect("checked classes have the tensor input dimensions");
        Ok(self.spaces[output_degree]
            .class_from_coordinates(&coordinates)
            .expect("a tensor product has canonical coordinates of the output dimension"))
    }

    /// Rebuilds every stored Ext space, tensor, witness, unit, and algebra law.
    pub fn verify(&self) -> bool {
        verify_guard!(
            self.bound != usize::MAX
                && self.spaces.len() == self.bound + 1
                && self.bases.len() == self.bound + 1
                && self.products.len() == self.bound + 1
                && resolve(&self.module, self.bound).end == self.resolution_end
        );
        let mut fresh_spaces = Vec::with_capacity(self.spaces.len());
        for degree in 0..self.spaces.len() {
            let_or_false!(Ok(space) = ExtSpace::new(&self.module, &self.module, degree));
            fresh_spaces.push(space);
        }
        verify_guard!(
            self.spaces
                .iter()
                .zip(&fresh_spaces)
                .enumerate()
                .all(|(degree, (stored, fresh))| {
                    stored.degree() == degree && stored.matches(fresh)
                })
                && self
                    .bases
                    .iter()
                    .zip(&self.spaces)
                    .all(|(basis, space)| { basis_matches(space, basis) })
                && self.unit.space().matches(&self.spaces[0])
                && self.spaces[0]
                    .identity_class()
                    .is_ok_and(|identity| identity.equals(&self.unit) == Ok(true))
        );
        self.verify_tensors(&fresh_spaces)
            && self.verify_unit()
            && self.verify_bilinearity()
            && self.verify_associativity()
    }

    fn check_class(&self, class: &ExtClass) -> Result<usize, ExtAlgebraProductError> {
        if !class.space().source().ptr_eq(&self.module)
            || !class.space().target().ptr_eq(&self.module)
        {
            return Err(ExtAlgebraProductError::OutsideAlgebra);
        }
        let degree = class.space().degree();
        if degree > self.bound {
            return Err(ExtAlgebraProductError::DegreeOutsideBound {
                degree,
                bound: self.bound,
            });
        }
        if !class.space().matches(&self.spaces[degree]) {
            return Err(ExtAlgebraProductError::IncompatibleBasis { degree });
        }
        Ok(degree)
    }

    fn verify_tensors(&self, fresh_spaces: &[ExtSpace]) -> bool {
        let field = self.module.field();
        self.products.iter().enumerate().all(|(left_degree, row)| {
            row.len() == self.bound - left_degree + 1
                && row.iter().enumerate().all(|(right_degree, tensor)| {
                    let output_degree = left_degree + right_degree;
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
                        && self.bases[left_degree]
                            .iter()
                            .enumerate()
                            .all(|(left_index, left)| {
                                self.bases[right_degree].iter().enumerate().all(
                                    |(right_index, right)| {
                                        let_or_false!(
                                            Some(coordinates) =
                                                tensor.basis_product(left_index, right_index)
                                        );
                                        let_or_false!(
                                            Some(witness) = tensor.witness(left_index, right_index)
                                        );
                                        let_or_false!(
                                            Some(product) = tensor.product(left_index, right_index)
                                        );
                                        product.space().matches(&self.spaces[output_degree])
                                            && product.coordinates() == coordinates
                                            && product.coordinates().len()
                                                == self.spaces[output_degree].dim()
                                            && product.coordinates().iter().all(|coordinate| {
                                                coordinate.raw() < field.modulus()
                                            })
                                            && witness.verify_against(
                                                left,
                                                right,
                                                product,
                                                &fresh_spaces[output_degree],
                                            )
                                    },
                                )
                            })
                })
        })
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
        let field = self.module.field();
        self.products.iter().all(|row| {
            row.iter().all(|tensor| {
                let left_zero = vec![field.zero(); tensor.left_dim];
                let right_zero = vec![field.zero(); tensor.right_dim];
                let output_zero = vec![field.zero(); tensor.output_dim];
                tensor.apply(&left_zero, &right_zero, field) == Some(output_zero.clone())
                    && self.bases[tensor.left_degree].iter().enumerate().all(
                        |(left_index, left)| {
                            self.bases[tensor.right_degree].iter().enumerate().all(
                                |(right_index, right)| {
                                    let left_twice = left.add(left).expect("one basis space");
                                    let right_twice = right.add(right).expect("one basis space");
                                    let product = tensor
                                        .basis_product(left_index, right_index)
                                        .expect("a tensor has every basis pair");
                                    let twice_product: Vec<Fp> = product
                                        .iter()
                                        .map(|&coordinate| field.add(coordinate, coordinate))
                                        .collect();
                                    tensor.apply(left.coordinates(), &right_zero, field)
                                        == Some(output_zero.clone())
                                        && tensor.apply(&left_zero, right.coordinates(), field)
                                            == Some(output_zero.clone())
                                        && tensor.apply(
                                            left_twice.coordinates(),
                                            right.coordinates(),
                                            field,
                                        ) == Some(twice_product.clone())
                                        && tensor.apply(
                                            left.coordinates(),
                                            right_twice.coordinates(),
                                            field,
                                        ) == Some(twice_product)
                                },
                            )
                        },
                    )
            })
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

/// A bounded Ext algebra whose next syzygy is known to be nonzero.
#[derive(Clone, Debug)]
pub struct ExtAlgebraCut {
    algebra: ExtAlgebra,
    first_omitted_degree: usize,
}

impl ExtAlgebraCut {
    accessor_methods! {
        /// The exact algebra layer through the requested bound.
        pub algebra() -> &ExtAlgebra = |this| &this.algebra;
        /// The first degree outside the exact stored layer.
        pub first_omitted_degree() -> usize = |this| this.first_omitted_degree;
    }

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

/// A complete self-Ext algebra or an exact layer with a typed cut.
#[derive(Clone, Debug)]
pub enum ExtAlgebraOutcome {
    /// The minimal resolution ended within the caller bound.
    Complete(ExtAlgebra),
    /// The minimal resolution still has a nonzero next syzygy.
    Cut(ExtAlgebraCut),
}

impl ExtAlgebraOutcome {
    /// Computes the bounded self-Ext algebra of `module` through `bound`.
    pub fn compute(module: &Module, bound: usize) -> Result<ExtAlgebraOutcome, ExtAlgebraError> {
        ExtAlgebra::build(module, bound)
    }

    binary_outcome_accessors!(
        Complete,
        Cut,
        complete -> ExtAlgebra = |value| value,
        cut -> ExtAlgebraCut = |value| value,
        is_complete,
        into_complete -> ExtAlgebra = |value| value;
        flag = "Whether the minimal resolution ended within the bound.";
        positive = "The complete Ext algebra, or `None` when the resolution was cut.";
        negative = "The cut Ext algebra, or `None` when the resolution ended.";
        into = "The complete Ext algebra by value, or `None` when the resolution was cut.";
    );

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

fn basis_classes(space: &ExtSpace) -> Vec<ExtClass> {
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

fn basis_matches(space: &ExtSpace, basis: &[ExtClass]) -> bool {
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

fn build_products(
    spaces: &[ExtSpace],
    bases: &[Vec<ExtClass>],
) -> Result<Vec<Vec<MultiplicationTensor>>, ExtAlgebraError> {
    let bound = spaces
        .len()
        .checked_sub(1)
        .expect("an Ext algebra stores degree zero");
    let mut products = Vec::with_capacity(spaces.len());
    for left_degree in 0..=bound {
        let mut row = Vec::with_capacity(bound - left_degree + 1);
        for right_degree in 0..=bound - left_degree {
            let output_degree = left_degree + right_degree;
            let left_dim = bases[left_degree].len();
            let right_dim = bases[right_degree].len();
            let output_dim = bases[output_degree].len();
            let entries = left_dim
                .checked_mul(right_dim)
                .and_then(|pairs| pairs.checked_mul(output_dim))
                .ok_or(ExtAlgebraError::TensorSizeOverflow {
                    left_degree,
                    right_degree,
                })?;
            let witnesses_len =
                left_dim
                    .checked_mul(right_dim)
                    .ok_or(ExtAlgebraError::TensorSizeOverflow {
                        left_degree,
                        right_degree,
                    })?;
            let mut coefficients = Vec::with_capacity(entries);
            let mut products = Vec::with_capacity(witnesses_len);
            let mut witnesses = Vec::with_capacity(witnesses_len);
            for left in &bases[left_degree] {
                for right in &bases[right_degree] {
                    let (product, witness) = left.then_with_witness(right).map_err(|error| {
                        ExtAlgebraError::Product {
                            left_degree,
                            right_degree,
                            error,
                        }
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
            debug_assert_eq!(products.len(), witnesses_len);
            debug_assert_eq!(witnesses.len(), witnesses_len);
            row.push(MultiplicationTensor {
                left_degree,
                right_degree,
                left_dim,
                right_dim,
                output_dim,
                coefficients,
                products,
                witnesses,
            });
        }
        products.push(row);
    }
    Ok(products)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{dual_numbers, linear_an};
    use crate::field::PrimeField;

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
        let ExtAlgebraOutcome::Complete(ext) = ExtAlgebraOutcome::compute(&source, 3).unwrap()
        else {
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
}
