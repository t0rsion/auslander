use crate::hom::HomError;
use crate::homspace::HomSpaceError;
use crate::indec::IndecError;

/// A failed internal cross-check of the approximation layer. Every variant
/// signals a crate defect: the construction checked a consequence of a theorem
/// whose hypotheses hold, and the check failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ApproxDefect {
    /// Accepting one generator for `summand` moved the `F_p` dimension of the
    /// generated span by `growth` instead of by the residue degree. The
    /// generator lies outside the span and the span already holds
    /// `generator . rad End(N_i)`, so the step must add exactly one `D_i` line.
    GeneratorGrowth {
        /// Index of the add-generator in the given list.
        summand: usize,
        /// The observed rise in `F_p` dimension.
        growth: usize,
        /// The residue degree of the add-generator.
        residue_degree: usize,
    },
    /// A basis map of `Hom(X, N_i)` does not factor through the built map, so
    /// the generators failed to generate.
    FactorizationMissing {
        /// Index of the add-generator in the given list.
        summand: usize,
        /// Position of the map in the [`crate::homspace::HomSpace`] basis.
        basis_index: usize,
    },
    /// A basis row of `K_f` lies outside `rad End(B)`, so the built map is not
    /// minimal. The generator loop returns a projective cover, so this cannot
    /// happen.
    KernelOutsideRadical {
        /// Position of the row in the RREF basis of `K_f`.
        row: usize,
        /// `dim_k K_f`.
        kernel_dim: usize,
        /// `dim_k rad End(B)`.
        radical_dim: usize,
    },
}

display_error! { error ApproxDefect {
    Self::GeneratorGrowth { summand, growth, residue_degree } => "a generator for summand {summand} raised the span by {growth}, not by the \
                                                                  residue degree {residue_degree}; crate defect";
    Self::FactorizationMissing { summand, basis_index } => "basis map {basis_index} for summand {summand} does not factor through the \
                                                            built map; crate defect";
    Self::KernelOutsideRadical { row, kernel_dim, radical_dim } => "row {row} of the {kernel_dim}-dimensional kernel lies outside the \
                                                                   {radical_dim}-dimensional radical; crate defect";
} }

/// Rejected approximation input, or a failed internal cross-check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ApproxError {
    /// An add-generator failed the indecomposability gate.
    SummandNotIndecomposable {
        /// Position in the given list.
        index: usize,
        /// Why the gate rejected it.
        reason: IndecError,
    },
    /// Two add-generators are isomorphic. The list holds one module per
    /// isomorphism class, because `rad(N_j, N_i)` for `j != i` is all of
    /// `Hom(N_j, N_i)` only when the two are not isomorphic.
    RepeatedSummand {
        /// Position of the earlier module.
        first: usize,
        /// Position of the later module.
        second: usize,
    },
    /// A Hom computation rejected its input, usually two different algebras.
    Hom(HomError),
    /// A Hom-space coordinate call rejected its input.
    HomSpace(HomSpaceError),
    /// An internal cross-check failed.
    Defect(ApproxDefect),
}

display_error! { ApproxError {
    Self::SummandNotIndecomposable { index, reason } => "add-generator {index} is not indecomposable: {reason}";
    Self::RepeatedSummand { first, second } => "add-generators {first} and {second} are isomorphic; give one module per class";
    Self::Hom(error) => "hom: {error}";
    Self::HomSpace(error) => "hom space: {error}";
    Self::Defect(defect) => "{defect}";
} }

error_source!(ApproxError {
    Self::SummandNotIndecomposable { reason, .. } => Some(reason),
    Self::Hom(error) => Some(error),
    Self::HomSpace(error) => Some(error),
    Self::Defect(defect) => Some(defect),
    Self::RepeatedSummand { .. } => None,
});
