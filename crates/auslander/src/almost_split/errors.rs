use crate::ar::TauError;
use crate::arquiver::ArQuiverError;
use crate::ext::ExtClassError;
use crate::hom::HomError;
use crate::homspace::HomSpaceError;
use crate::indec::IndecError;
use crate::sequence::SequenceError;

/// A failed internal cross-check of the almost-split layer. Every variant
/// signals a crate defect: the construction checked a consequence of a
/// theorem whose hypotheses hold, and the check failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefectKind {
    /// `dim Ext^1(M, tau M)` differs from `dim stable End(M)`.
    DualityDimensionMismatch {
        /// `dim_Fp Ext^1(M, tau M)`.
        ext_dim: usize,
        /// `dim_Fp stable End(M)`.
        stable_end_dim: usize,
    },
    /// The dimension of the Ext socle differs from the residue degree of
    /// `M`.
    SocleDimensionMismatch {
        /// `dim_Fp` of the socle kernel.
        socle_dim: usize,
        /// The residue degree of `End(M)`.
        residue_degree: usize,
    },
    /// The minimal-resolution projectivity test and the AR translate
    /// disagree on whether `M` is projective.
    ProjectivityDisagreement {
        /// What the minimal resolution says.
        resolution_projective: bool,
        /// Whether `tau` returned zero.
        tau_zero: bool,
    },
    /// The sequence built from a nonzero chosen class came out split.
    NonzeroClassSplit,
    /// `im(Hom(X, E) -> Hom(X, M))` differs from `rad(X, M)` at this
    /// catalog entry.
    RightFactorizationMismatch {
        /// The catalog index of `X`.
        entry: usize,
    },
    /// `im(Hom(E, X) -> Hom(tau M, X))` differs from `rad(tau M, X)` at
    /// this catalog entry.
    LeftFactorizationMismatch {
        /// The catalog index of `X`.
        entry: usize,
    },
}

display_error! { DefectKind {
    Self::DualityDimensionMismatch { ext_dim, stable_end_dim } => "Ext^1(M, tau M) has dimension {ext_dim}, stable End(M) has dimension {stable_end_dim}; crate defect";
    Self::SocleDimensionMismatch { socle_dim, residue_degree } => "the Ext socle has dimension {socle_dim}, the residue degree is {residue_degree}; crate defect";
    Self::ProjectivityDisagreement { resolution_projective, tau_zero } => "the resolution route reports projective = {resolution_projective}, tau reports zero = {tau_zero}; crate defect";
    Self::NonzeroClassSplit => "the sequence of a nonzero chosen class splits; crate defect";
    Self::RightFactorizationMismatch { entry } => "the image of Hom(X, E) in Hom(X, M) differs from rad(X, M) at catalog entry {entry}; crate defect";
    Self::LeftFactorizationMismatch { entry } => "the image of Hom(E, X) in Hom(tau M, X) differs from rad(tau M, X) at catalog entry {entry}; crate defect";
} }

/// Rejected input, a failed dependency, or a failed internal cross-check of
/// the almost-split layer.
#[derive(Clone, Debug)]
pub enum AlmostSplitError {
    /// The AR translate could not be computed or cross-checked.
    Tau(TauError),
    /// The translate failed the indecomposability gate. The theorem makes
    /// this a defect; the variant keeps the gate's own report.
    TauIndecomposability(IndecError),
    /// Two modules do not share one algebra, or a composite was formed from
    /// mismatched endpoints.
    Hom(HomError),
    /// A morphism or subspace did not match the endpoints of its Hom space.
    Space(HomSpaceError),
    /// An Ext class operation rejected its input.
    Ext(ExtClassError),
    /// Building or reading a short exact sequence failed.
    Sequence(SequenceError),
    /// The category radical rejected its input.
    Radical(ArQuiverError),
    /// A failed internal cross-check; see [`DefectKind`].
    Defect(DefectKind),
}

display_error! { error AlmostSplitError {
    Self::Tau(error) => "the AR translate failed: {error}";
    Self::TauIndecomposability(error) => "the translate failed the indecomposability gate: {error}";
    Self::Hom(error) => "morphism rejected: {error}";
    Self::Space(error) => "hom space rejected the input: {error}";
    Self::Ext(error) => "Ext class rejected the input: {error}";
    Self::Sequence(error) => "short exact sequence rejected: {error}";
    Self::Radical(error) => "category radical failed: {error}";
    Self::Defect(kind) => "internal cross-check failed: {kind}";
} }

from_variants!(AlmostSplitError {
    TauError => Tau,
    IndecError => TauIndecomposability,
    HomError => Hom,
    HomSpaceError => Space,
    ExtClassError => Ext,
    SequenceError => Sequence,
    ArQuiverError => Radical,
});

pub(in crate::almost_split) fn defect(kind: DefectKind) -> AlmostSplitError {
    AlmostSplitError::Defect(kind)
}
