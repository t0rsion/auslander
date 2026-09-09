use std::sync::Arc;

use crate::algebra::{Algebra, AlgebraBuildError};
use crate::basic::BasicError;
use crate::certificate::Certificate;
use crate::completion::{CompletionLimits, TruncationDiagnostics};
use crate::decompose::Split;
use crate::endo::EndoAlgebra;
use crate::field::Fp;
use crate::homspace::row_times;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::relation::RelationError;
use crate::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};

use super::{present_target, verify_target};

/// Independent limits for one target-presentation run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetLimits {
    /// Maximum dimension of `End_A(T)` before its multiplication table is built.
    pub max_endo_dimension: usize,
    /// Maximum calls to [`EndoAlgebra::multiply`] while building radical
    /// powers and their idempotent corners.
    pub max_radical_products: usize,
    /// Maximum enumerated paths of lengths `2..=lambda`.
    pub max_paths: usize,
    /// Maximum nonzero coefficients copied into the relation list.
    pub max_relation_terms: usize,
    /// Limits for the final bound quiver completion.
    pub completion: CompletionLimits,
}

impl Default for TargetLimits {
    fn default() -> TargetLimits {
        TargetLimits {
            max_endo_dimension: 4096,
            max_radical_products: 1_000_000,
            max_paths: 1_000_000,
            max_relation_terms: 1_000_000,
            completion: CompletionLimits::default(),
        }
    }
}

/// The stage at which a target budget rejected its next reservation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TargetCutStage {
    /// The endomorphism algebra exceeds `max_endo_dimension`.
    EndoDimension,
    /// Multiplication from `J^power` by `J` while building `J^(power + 1)`.
    RadicalPower { power: usize },
    /// Projection of `J^power` into the corner for a target arrow pair.
    RadicalCorner {
        source: u32,
        target: u32,
        power: usize,
    },
    /// Enumeration of paths at the named length.
    Paths { length: usize },
    /// Copying a kernel row into a relation for one endpoint pair.
    Relations { source: u32, target: u32 },
}

/// One rejected reservation against a target budget.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetBudgetCut {
    pub stage: TargetCutStage,
    /// Units already reserved before the rejection.
    pub used: usize,
    /// Units requested by the rejected reservation.
    pub requested: usize,
    /// The corresponding limit.
    pub limit: usize,
}

/// Why a target construction stopped at a caller limit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TargetCutReason {
    /// A radical-product, path, or relation-term budget stopped the run.
    Budget(TargetBudgetCut),
    /// The existing completion engine stopped the run.
    Completion(TruncationDiagnostics),
}

/// A self-verifying target cut with its complete input and limits.
#[derive(Clone, Debug)]
pub struct TargetPresentationCut {
    pub(crate) source: Module,
    pub(crate) tilting_limits: TiltingLimits,
    pub(crate) limits: TargetLimits,
    pub(crate) reason: TargetCutReason,
}

impl TargetPresentationCut {
    accessor_methods! {
        /// The source tilting module.
        pub source() -> &Module = |this| &this.source;
        /// The tilting limits carried by the successful source classification.
        pub tilting_limits() -> TiltingLimits = |this| this.tilting_limits;
        /// The target limits that stopped recovery.
        pub limits() -> &TargetLimits = |this| &this.limits;
        /// The first rejected reservation or completion cut.
        pub reason() -> &TargetCutReason = |this| &this.reason;
    }

    /// Repeats target recovery and requires the same cut reason.
    pub fn verify(&self) -> bool {
        let Ok(ClassicalTiltingResult::Tilting(tilting)) =
            ClassicalTiltingModule::classify(&self.source, self.tilting_limits)
        else {
            return false;
        };
        if !tilting.verify() {
            return false;
        }
        matches!(
            present_target(&tilting, &self.limits),
            Ok(TargetPresentationOutcome::Cut(cut)) if cut.reason == self.reason
        )
    }
}

/// Exact work completed by a successful target recovery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TargetWork {
    /// Dimension of `End_A(T)` before its multiplication table is built.
    pub endo_dimension: usize,
    /// Radical-power and corner products.
    pub radical_products: usize,
    /// Enumerated paths of lengths `2..=lambda`.
    pub paths: usize,
    /// Nonzero coefficients in the input relation list.
    pub relation_terms: usize,
}

/// Exact evidence that the tilting target is not split over the base field.
#[derive(Clone, Debug)]
pub struct NonSplitTarget {
    pub(crate) module: Module,
    pub(crate) tilting_limits: TiltingLimits,
    pub(crate) limits: TargetLimits,
    pub(crate) summand: usize,
    pub(crate) residue_degree: usize,
}

impl NonSplitTarget {
    accessor_methods! {
        /// The tilting module whose target is not split.
        pub module() -> &Module = |this| &this.module;
        /// The target limits used to find the non-split summand.
        pub limits() -> &TargetLimits = |this| &this.limits;
        /// The first non-split summand in deterministic decomposition order.
        pub summand() -> usize = |this| this.summand;
        /// The exact degree of that summand's residue field over the base field.
        pub residue_degree() -> usize = |this| this.residue_degree;
    }

    /// Recomputes the tilting classification and the first non-split summand.
    pub fn verify(&self) -> bool {
        let Ok(ClassicalTiltingResult::Tilting(tilting)) =
            ClassicalTiltingModule::classify(&self.module, self.tilting_limits)
        else {
            return false;
        };
        tilting.verify()
            && matches!(
                present_target(&tilting, &self.limits),
                Ok(TargetPresentationOutcome::Unsupported(value))
                    if value.summand == self.summand
                        && value.residue_degree == self.residue_degree
            )
    }
}

/// Rejected target input or a failed internal cross-check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TargetError {
    /// The basic decomposition could not be certified.
    Basic(BasicError),
    /// A recovered relation was rejected.
    Relation(RelationError),
    /// The final algebra constructor failed for a reason other than a cut.
    Algebra(AlgebraBuildError),
    /// A checked size calculation overflowed before allocation.
    SizeOverflow { stage: TargetCutStage },
    /// An invariant implied by the construction failed.
    Defect { reason: String },
}

display_error! { TargetError {
    Self::Basic(error) => "basic layer: {error}";
    Self::Relation(error) => "relation rejected: {error}";
    Self::Algebra(error) => "target algebra rejected: {error}";
    Self::SizeOverflow { stage } => "target size overflowed at {stage:?}";
    Self::Defect { reason } => "internal cross-check failed: {reason}";
} }

error_source! { TargetError {
    Self::Basic(error) => Some(error),
    Self::Relation(error) => Some(error),
    Self::Algebra(error) => Some(error),
    _ => None,
} }

from_variants! { TargetError {
    BasicError => Basic,
    RelationError => Relation,
} }

/// A verified presentation of `End_A(T)^op` and its map into `End_A(T)`.
#[derive(Clone)]
pub struct VerifiedTargetPresentation {
    pub(crate) source: Module,
    pub(crate) tilting_limits: TiltingLimits,
    pub(crate) limits: TargetLimits,
    pub(crate) target: Arc<Algebra>,
    pub(crate) endo: EndoAlgebra,
    pub(crate) split: Split,
    pub(crate) completion: Certificate,
    pub(crate) idempotent_images: DenseMat,
    pub(crate) arrow_images: DenseMat,
    pub(crate) normal_word_images: DenseMat,
    pub(crate) normal_word_preimages: DenseMat,
    pub(crate) radical_nilpotency_index: usize,
    pub(crate) work: TargetWork,
}

debug_fields!(VerifiedTargetPresentation |this| {
    "source_dim_vector" => this.source.dim_vector();
    "target_dim" => this.target.dim();
    "arrows" => this.target.quiver().num_arrows();
    "radical_nilpotency_index" => this.radical_nilpotency_index;
});

impl VerifiedTargetPresentation {
    accessor_methods! {
        /// The source tilting module `T`.
        pub source() -> &Module = |this| &this.source;
        /// The checked target algebra `End_A(T)^op`.
        pub target() -> &Arc<Algebra> = |this| &this.target;
        /// `End_A(T)` in the coordinates used by every stored image row.
        pub endo() -> &EndoAlgebra = |this| &this.endo;
        /// The verified decomposition that fixes target vertex order.
        pub split() -> &Split = |this| &this.split;
        /// Primitive idempotent images in `End_A(T)`, one row per target vertex.
        pub idempotent_images() -> &DenseMat = |this| &this.idempotent_images;
        /// Arrow images in `End_A(T)`, one row per target arrow.
        pub arrow_images() -> &DenseMat = |this| &this.arrow_images;
        /// Target normal-word images in `End_A(T)`, one row per target basis word.
        pub normal_word_images() -> &DenseMat = |this| &this.normal_word_images;
        /// The inverse normal-word image matrix, from `End_A(T)` to target coordinates.
        pub normal_word_preimages() -> &DenseMat = |this| &this.normal_word_preimages;
        /// The independently verified completion certificate for the target.
        pub completion_certificate() -> &Certificate = |this| &this.completion;
        /// The least `lambda` with `rad(End_A(T))^lambda = 0`.
        pub radical_nilpotency_index() -> usize = |this| this.radical_nilpotency_index;
        /// The limits used to build this value.
        pub limits() -> &TargetLimits = |this| &this.limits;
        /// Exact work used before successful completion.
        pub work() -> TargetWork = |this| this.work;
    }

    /// Maps target algebra coordinates to coordinates in `End_A(T)^op`.
    ///
    /// The underlying vector space is `End_A(T)`, so the returned row uses
    /// [`VerifiedTargetPresentation::endo`] coordinates.
    ///
    /// # Panics
    /// Panics unless `coordinates` has length [`Algebra::dim`] for the target.
    pub fn map_coordinates(&self, coordinates: &[Fp]) -> Vec<Fp> {
        assert_eq!(
            coordinates.len(),
            self.target.dim(),
            "map_coordinates: target coordinate count"
        );
        row_times(coordinates, &self.normal_word_images, &self.target.field())
    }

    /// Maps `End_A(T)` coordinates back to target algebra coordinates.
    ///
    /// # Panics
    /// Panics unless `coordinates` has length [`EndoAlgebra::dim`].
    pub fn preimage_coordinates(&self, coordinates: &[Fp]) -> Vec<Fp> {
        assert_eq!(
            coordinates.len(),
            self.endo.dim(),
            "preimage_coordinates: endomorphism coordinate count"
        );
        row_times(
            coordinates,
            &self.normal_word_preimages,
            &self.target.field(),
        )
    }

    /// Recomputes the source classification, target certificate, and algebra map.
    pub fn verify(&self) -> bool {
        verify_target(self)
    }
}

/// The three exact outcomes of target-presentation recovery.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum TargetPresentationOutcome {
    Presented(VerifiedTargetPresentation),
    Unsupported(NonSplitTarget),
    Cut(TargetPresentationCut),
}

impl TargetPresentationOutcome {
    optional_accessors! {
        /// The verified target, if recovery completed.
        pub presented() -> &VerifiedTargetPresentation = Self::Presented(value) => value;
        /// The non-split witness, if the target is unsupported.
        pub unsupported() -> &NonSplitTarget = Self::Unsupported(value) => value;
        /// The cut diagnostics, if a caller limit stopped recovery.
        pub cut() -> &TargetPresentationCut = Self::Cut(value) => value;
    }

    /// Recomputes the mathematical outcome and all stored certificate data.
    pub fn verify(&self) -> bool {
        match self {
            Self::Presented(value) => value.verify(),
            Self::Unsupported(value) => value.verify(),
            Self::Cut(value) => value.verify(),
        }
    }
}
