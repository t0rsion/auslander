use crate::ar::TauError;
use crate::arquiver::CatalogError;
use crate::basic::BasicError;
use crate::hom::HomError;
use crate::taurigid::{NonTauRigidWitness, TauRigidError, TauRigidModule};

/// Rejected input, a blocked certification, or a failed internal cross-check
/// of the support tau-tilting layer.
///
/// None of these is an answer about a pair. A pair that fails a condition is
/// a [`PairRejection`], never an error.
#[derive(Clone, Debug)]
pub enum SupportTauError {
    /// No complete indecomposable catalog applies to the algebra.
    Catalog(CatalogError),
    /// The basic layer rejected an input or could not certify a summand.
    Basic(BasicError),
    /// A tau-rigidity decision could not be reached.
    TauRigid(TauRigidError),
    /// A Hom space could not be built.
    Hom(HomError),
    /// The supplied summand indices do not match the module's summands one
    /// for one.
    SummandIndexCount {
        /// Number of indices supplied.
        indices: usize,
        /// Number of summands of the module part.
        summands: usize,
    },
    /// A failed internal cross-check: the tables and the certified route
    /// disagree, or a decomposition produced a summand outside the subset it
    /// was assembled from.
    Defect {
        /// What contradicted the check.
        reason: String,
    },
}

display_error! { error SupportTauError {
    Self::Catalog(error) => "the catalog route rejected the algebra: {error}";
    Self::Basic(error) => "the basic layer rejected an input: {error}";
    Self::TauRigid(error) => "tau-rigidity stayed undecided: {error}";
    Self::Hom(error) => "a Hom space failed: {error}";
    Self::SummandIndexCount { indices, summands } => "{indices} summand indices for {summands} summands; one index per summand";
    Self::Defect { reason } => "internal cross-check failed: {reason}";
} }

from_variants!(SupportTauError {
    CatalogError => Catalog,
    BasicError => Basic,
    TauRigidError => TauRigid,
});

impl From<TauError> for SupportTauError {
    fn from(error: TauError) -> SupportTauError {
        SupportTauError::TauRigid(TauRigidError::Tau(error))
    }
}

from_variants!(SupportTauError { HomError => Hom });

/// The condition a candidate pair failed, with the witness for that failure.
///
/// The conditions are numbered as in `docs/support-tau-tilting.md` section 6 and are
/// checked in that order, so the rejection names the first one that failed.
#[derive(Clone, Debug)]
pub enum PairRejection {
    /// Condition 1: the module part and the projective part do not share one
    /// algebra value (the same [`std::sync::Arc`]).
    ///
    /// The rest of condition 1, that both parts are basic and certified, is
    /// carried by the argument types: [`crate::basic::BasicDecomposition`] and
    /// [`crate::basic::ProjectiveSupport`] have no other constructor.
    DifferentAlgebras,
    /// Condition 2: `Hom(P, M)` is not zero, at a support vertex of `P` where
    /// `M` does not vanish.
    ///
    /// `Hom(P_v, M) = M_v` for right modules, so the vertex and the dimension
    /// are the whole proof. No morphism is needed.
    HomFromProjectiveNonzero {
        /// A vertex in the support of `P` where `M` is nonzero.
        vertex: u32,
        /// `dim M_v`, which is `dim Hom(P_v, M)`.
        dim: usize,
    },
    /// Condition 3: `M` is not tau-rigid, with one nonzero morphism
    /// `X_i -> tau X_j`.
    NotTauRigid(NonTauRigidWitness),
    /// Condition 4: the summand counts do not add up to the expected total,
    /// which is `n` for a support tau-tilting pair and `n - 1` for an almost
    /// complete pair.
    SummandCount {
        /// `|M|`, the number of indecomposable summands of the module part.
        module: usize,
        /// `|P|`, the number of support vertices.
        projective: usize,
        /// The total the pair type requires.
        expected: usize,
    },
}

impl PairRejection {
    accessor_methods! {
        /// The number of the failed condition in `docs/support-tau-tilting.md` section 6,
        /// from 1 to 4.
        pub condition() -> u32 = |this| match this {
            Self::DifferentAlgebras => 1,
            Self::HomFromProjectiveNonzero { .. } => 2,
            Self::NotTauRigid(_) => 3,
            Self::SummandCount { .. } => 4,
        };
    }
}

display_error! { PairRejection {
    Self::DifferentAlgebras => "the two parts do not share one algebra";
    Self::HomFromProjectiveNonzero { vertex, dim } => "Hom(P, M) is not zero: dim Hom(P_{vertex}, M) = dim M_{vertex} = {dim}";
    Self::NotTauRigid(_) => "M is not tau-rigid";
    Self::SummandCount { module, projective, expected } => "|M| + |P| = {module} + {projective}, and the pair needs {expected}";
} }

/// The result of [`check_conditions`]: the tau-rigidity witness both pair
/// types keep, or the first condition that failed.
pub(super) enum Checked {
    Accepted(TauRigidModule),
    Rejected(PairRejection),
}
