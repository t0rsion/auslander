use crate::algebra::AlgebraBuildError;
use crate::dynkin::DynkinError;
use crate::enumerate::EnumerateError;
use crate::hom::HomError;
use crate::homspace::HomSpaceError;

/// Rejected input, or a failed internal cross-check, of the AR-quiver layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArQuiverError {
    /// Two modules do not share one algebra, or a composite was formed from
    /// mismatched endpoints.
    Hom(HomError),
    /// A morphism or subspace did not match the endpoints of its Hom space.
    Space(HomSpaceError),
    /// Deciding injectivity needs the opposite algebra, and building it
    /// failed.
    Injective(AlgebraBuildError),
    /// The algebra is neither a path algebra of Dynkin type nor a Nakayama
    /// algebra, so no complete enumeration of its indecomposables exists in
    /// this release. Both rejections are carried.
    UnsupportedDomain {
        /// Why the Dynkin route rejected the algebra.
        dynkin: DynkinError,
        /// Why the Nakayama route rejected the algebra.
        nakayama: EnumerateError,
    },
    /// `rad^2(X, Y)` came out with a member outside `rad(X, Y)`. The radical
    /// is an ideal, so this is a crate defect. The dimension vectors of `X`
    /// and `Y` are carried.
    RadicalSquareNotContained {
        /// Dimension vector of `X`.
        source: Vec<usize>,
        /// Dimension vector of `Y`.
        target: Vec<usize>,
    },
    /// A residue degree does not divide the base dimension of an arrow.
    /// `Irr(X, Y)` is a vector space over each residue field, so this is a
    /// crate defect. The dimension vector of the module whose residue degree
    /// failed is carried.
    ResidueDegreeDoesNotDivide {
        /// Dimension vector of the module whose residue degree failed.
        dim_vector: Vec<usize>,
        /// `dim_Fp Irr(X, Y)`.
        base_dim: usize,
        /// The residue degree that does not divide it.
        residue_degree: usize,
    },
}

display_error! { error ArQuiverError {
    Self::Hom(error) => "morphism rejected: {error}";
    Self::Space(error) => "hom space rejected the input: {error}";
    Self::Injective(error) => "the opposite algebra could not be built: {error}";
    Self::UnsupportedDomain { dynkin, nakayama } => "no complete enumeration applies: the Dynkin route reports {dynkin}, the Nakayama route reports {nakayama}";
    Self::RadicalSquareNotContained { source, target } => "the radical square of ({source:?}, {target:?}) left the radical; crate defect";
    Self::ResidueDegreeDoesNotDivide { dim_vector, base_dim, residue_degree } => "residue degree {residue_degree} of {dim_vector:?} does not divide the base dimension {base_dim}; crate defect";
} }

from_variants! { ArQuiverError {
    HomError => Hom,
    HomSpaceError => Space,
} }
