use crate::ext::{ExtClass, ExtSpace};
use crate::module::Module;
use crate::resolution::{ResolutionEnd, resolve};

use super::errors::{ExtAlgebraError, ExtAlgebraProductError};
use super::product::{basis_classes, build_products};
use super::tensor::{MultiplicationTensor, ProductRecord, ProductRecords};

/// The exact self-Ext spaces and Yoneda tensors through one degree bound.
#[derive(Clone, Debug)]
pub struct ExtAlgebra {
    pub(super) module: Module,
    pub(super) bound: usize,
    pub(super) resolution_end: ResolutionEnd,
    pub(super) spaces: Vec<ExtSpace>,
    pub(super) bases: Vec<Vec<ExtClass>>,
    pub(super) unit: ExtClass,
    // Row p holds tensors with left degree p and right degrees 0 through
    // bound - p, in order.
    pub(super) products: Vec<Vec<MultiplicationTensor>>,
}

impl ExtAlgebra {
    /// Builds the self-Ext algebra through `bound`.
    ///
    /// Every grade through `bound` and every product with output degree at
    /// most `bound` is exact. A finite resolution gives a complete algebra.
    /// A cut proves that degree `bound + 1` has a nonzero syzygy, but makes no
    /// claim about higher degrees.
    pub(super) fn build(
        module: &Module,
        bound: usize,
    ) -> Result<ExtAlgebraOutcome, ExtAlgebraError> {
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
}

/// A bounded Ext algebra whose next syzygy is known to be nonzero.
#[derive(Clone, Debug)]
pub struct ExtAlgebraCut {
    pub(super) algebra: ExtAlgebra,
    pub(super) first_omitted_degree: usize,
}

impl ExtAlgebraCut {
    accessor_methods! {
        /// The exact algebra layer through the requested bound.
        pub algebra() -> &ExtAlgebra = |this| &this.algebra;
        /// The first degree outside the exact stored layer.
        pub first_omitted_degree() -> usize = |this| this.first_omitted_degree;
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
}
