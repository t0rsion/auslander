use crate::certificate::Certificate;
use crate::target::{TargetLimits, TargetWork};
use crate::tilting_complex::{ApproximationDirection, TiltingComplexLimits};

/// One deterministic mutation step from the regular projective generator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ArtifactMutation {
    pub(super) direction: ApproximationDirection,
    pub(super) summand: usize,
}

impl ArtifactMutation {
    accessor_methods! {
        /// The mutation direction.
        pub direction() -> ApproximationDirection = |this| this.direction;
        /// The replaced summand index.
        pub summand() -> usize = |this| this.summand;
    }
}

/// Limits applied before the artifact parser allocates a declared container.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ArtifactParseLimits {
    /// The greatest accepted input byte count.
    pub max_input_bytes: usize,
    /// The greatest byte count for either embedded completion certificate.
    pub max_certificate_bytes: usize,
    /// The greatest number of stored mutation steps.
    pub max_mutations: usize,
    /// The greatest digit count in one unsigned integer.
    pub max_integer_digits: usize,
}

impl Default for ArtifactParseLimits {
    fn default() -> Self {
        ArtifactParseLimits {
            max_input_bytes: 16_777_216,
            max_certificate_bytes: 4_194_304,
            max_mutations: 65_536,
            max_integer_digits: 20,
        }
    }
}

/// Independent ceilings for one artifact verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ArtifactVerifyLimits {
    /// Parser and allocation ceilings.
    pub parse: ArtifactParseLimits,
    /// The greatest accepted tilting Hom-space limit.
    pub max_hom_spaces: usize,
    /// The greatest accepted target endomorphism dimension limit.
    pub max_endo_dimension: usize,
    /// The greatest accepted target radical-product limit.
    pub max_radical_products: usize,
    /// The greatest accepted target path limit.
    pub max_paths: usize,
    /// The greatest accepted target relation-term limit.
    pub max_relation_terms: usize,
    /// The greatest accepted completion step limit.
    pub max_completion_steps: usize,
    /// The greatest number of charged verifier work units.
    pub max_work_units: usize,
}

impl Default for ArtifactVerifyLimits {
    fn default() -> Self {
        let target = TargetLimits::default();
        ArtifactVerifyLimits {
            parse: ArtifactParseLimits::default(),
            max_hom_spaces: TiltingComplexLimits::default().max_hom_spaces,
            max_endo_dimension: target.max_endo_dimension,
            max_radical_products: target.max_radical_products,
            max_paths: target.max_paths,
            max_relation_terms: target.max_relation_terms,
            max_completion_steps: target.completion.max_steps,
            max_work_units: 1_000_000,
        }
    }
}

/// A canonical standalone derived-equivalence claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivedArtifact {
    pub(super) source: Certificate,
    pub(super) mutations: Vec<ArtifactMutation>,
    pub(super) target: Certificate,
    pub(super) tilting_limits: TiltingComplexLimits,
    pub(super) target_limits: TargetLimits,
    pub(super) work: TargetWork,
    pub(super) fingerprint: String,
}
