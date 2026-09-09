use crate::ext::{ExtClassError, ExtError};

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
