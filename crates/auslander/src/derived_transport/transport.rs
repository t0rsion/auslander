use crate::control::ComputationControl;
use crate::derived::{
    AddTComplex, DerivedEquivalenceCertificate, ProjectiveTargetComplex, StrictTransport,
};
use crate::homotopy::BoundedComplex;
use crate::perfect::{
    PerfectReplacement, ReplacementCancellation, ReplacementCut, ReplacementLimits,
    ReplacementOutcome, replace_perfect,
};

use super::DerivedTransportError;
use super::model::{ProjectiveAddTModel, model_projective_complex};

/// Automatic transport fixed by one checked classical tilting certificate.
#[derive(Clone)]
pub struct DerivedTransport {
    certificate: DerivedEquivalenceCertificate,
}

impl DerivedTransport {
    /// Builds automatic transport from a checked certificate.
    pub fn new(
        certificate: DerivedEquivalenceCertificate,
    ) -> Result<DerivedTransport, DerivedTransportError> {
        if !certificate.verify() {
            return Err(DerivedTransportError::InvalidCertificate);
        }
        Ok(DerivedTransport { certificate })
    }

    accessor_methods! {
        /// The checked derived-equivalence certificate.
        pub certificate() -> &DerivedEquivalenceCertificate = |this| &this.certificate;
        /// The strict core used after automatic replacement.
        pub strict() -> &StrictTransport = |this| this.certificate.transport();
    }

    /// Computes forward transport through a checked projective and `add(T)` model.
    pub fn forward(
        &self,
        input: &BoundedComplex,
        limits: ReplacementLimits,
        control: Option<&ComputationControl>,
    ) -> Result<DerivedForwardOutcome, DerivedTransportError> {
        let replacement = match replace_perfect(input, limits, control)? {
            ReplacementOutcome::Replaced(value) => value,
            ReplacementOutcome::Cut(value) => {
                return Ok(DerivedForwardOutcome::ReplacementCut(value));
            }
            ReplacementOutcome::Cancelled(value) => {
                return Ok(DerivedForwardOutcome::ReplacementCancelled(value));
            }
        };
        let source_model =
            model_projective_complex(replacement.projective(), self.certificate.tilting())?;
        let output = self.strict().forward(source_model.model())?;
        Ok(DerivedForwardOutcome::Transported(Box::new(
            DerivedForwardTransport {
                certificate: self.certificate.clone(),
                input: input.clone(),
                replacement,
                source_model,
                output,
            },
        )))
    }

    /// Computes the inverse transport through a checked target replacement.
    pub fn reverse(
        &self,
        input: &BoundedComplex,
        limits: ReplacementLimits,
        control: Option<&ComputationControl>,
    ) -> Result<DerivedReverseOutcome, DerivedTransportError> {
        let replacement = match replace_perfect(input, limits, control)? {
            ReplacementOutcome::Replaced(value) => value,
            ReplacementOutcome::Cut(value) => {
                return Ok(DerivedReverseOutcome::ReplacementCut(value));
            }
            ReplacementOutcome::Cancelled(value) => {
                return Ok(DerivedReverseOutcome::ReplacementCancelled(value));
            }
        };
        let strict_input = self
            .strict()
            .target_complex(replacement.projective().complex().clone())?;
        let output = self.strict().reverse(&strict_input)?;
        Ok(DerivedReverseOutcome::Transported(Box::new(
            DerivedReverseTransport {
                certificate: self.certificate.clone(),
                input: input.clone(),
                replacement,
                strict_input,
                output,
            },
        )))
    }

    /// Computes the inverse tilting transport.
    pub fn derived_tensor(
        &self,
        input: &BoundedComplex,
        limits: ReplacementLimits,
        control: Option<&ComputationControl>,
    ) -> Result<DerivedReverseOutcome, DerivedTransportError> {
        self.reverse(input, limits, control)
    }
}

/// A complete forward derived transport.
#[derive(Clone)]
pub struct DerivedForwardTransport {
    certificate: DerivedEquivalenceCertificate,
    input: BoundedComplex,
    replacement: PerfectReplacement,
    source_model: ProjectiveAddTModel,
    output: ProjectiveTargetComplex,
}

impl DerivedForwardTransport {
    accessor_methods! {
        /// The ordinary source complex.
        pub input() -> &BoundedComplex = |this| &this.input;
        /// The checked source projective replacement.
        pub replacement() -> &PerfectReplacement = |this| &this.replacement;
        /// The checked `add(T)` model of the projective replacement.
        pub source_model() -> &ProjectiveAddTModel = |this| &this.source_model;
        /// The transported projective target complex.
        pub output() -> &ProjectiveTargetComplex = |this| &this.output;
    }

    /// Rechecks replacement, the `add(T)` model, and strict transport.
    pub fn verify(&self) -> bool {
        self.certificate.verify()
            && self.input.verify()
            && self.replacement.verify()
            && self.replacement.original().agrees_with(&self.input)
            && self.source_model.verify()
            && self.output.verify()
            && model_projective_complex(self.replacement.projective(), self.certificate.tilting())
                .is_ok_and(|model| {
                    model
                        .model()
                        .complex()
                        .agrees_with(self.source_model.model().complex())
                        && self
                            .certificate
                            .transport()
                            .forward(model.model())
                            .is_ok_and(|output| output.complex().agrees_with(self.output.complex()))
                })
    }
}

/// A complete forward result or a typed source-replacement boundary.
#[derive(Clone)]
pub enum DerivedForwardOutcome {
    /// Forward transport completed.
    Transported(Box<DerivedForwardTransport>),
    /// Source replacement reached a resource limit.
    ReplacementCut(ReplacementCut),
    /// Source replacement was cancelled.
    ReplacementCancelled(ReplacementCancellation),
}

impl DerivedForwardOutcome {
    optional_accessors! {
        /// The complete forward transport.
        pub transported() -> &DerivedForwardTransport = Self::Transported(value) => value;
        /// The source replacement cut.
        pub replacement_cut() -> &ReplacementCut = Self::ReplacementCut(value) => value;
        /// The source replacement cancellation.
        pub replacement_cancellation() -> &ReplacementCancellation = Self::ReplacementCancelled(value) => value;
    }
}

/// A complete inverse derived transport.
#[derive(Clone)]
pub struct DerivedReverseTransport {
    certificate: DerivedEquivalenceCertificate,
    input: BoundedComplex,
    replacement: PerfectReplacement,
    strict_input: ProjectiveTargetComplex,
    output: AddTComplex,
}

impl DerivedReverseTransport {
    accessor_methods! {
        /// The ordinary target complex.
        pub input() -> &BoundedComplex = |this| &this.input;
        /// The checked projective target replacement.
        pub replacement() -> &PerfectReplacement = |this| &this.replacement;
        /// The strict target model.
        pub strict_input() -> &ProjectiveTargetComplex = |this| &this.strict_input;
        /// The transported source complex in `add(T)`.
        pub output() -> &AddTComplex = |this| &this.output;
    }

    /// Rechecks replacement and strict inverse transport.
    pub fn verify(&self) -> bool {
        if !self.certificate.verify()
            || !self.input.verify()
            || !self.replacement.verify()
            || !self.replacement.original().agrees_with(&self.input)
            || !self.strict_input.verify()
            || !self.output.verify()
        {
            return false;
        }
        let strict = self.certificate.transport();
        strict
            .target_complex(self.replacement.projective().complex().clone())
            .is_ok_and(|input| {
                input.complex().agrees_with(self.strict_input.complex())
                    && strict
                        .reverse(&input)
                        .is_ok_and(|output| output.complex().agrees_with(self.output.complex()))
            })
    }
}

/// A complete inverse result or a typed target-replacement boundary.
#[derive(Clone)]
pub enum DerivedReverseOutcome {
    /// Inverse transport completed.
    Transported(Box<DerivedReverseTransport>),
    /// Target replacement reached a resource limit.
    ReplacementCut(ReplacementCut),
    /// Target replacement was cancelled.
    ReplacementCancelled(ReplacementCancellation),
}

impl DerivedReverseOutcome {
    optional_accessors! {
        /// The complete inverse transport.
        pub transported() -> &DerivedReverseTransport = Self::Transported(value) => value;
        /// The target replacement cut.
        pub replacement_cut() -> &ReplacementCut = Self::ReplacementCut(value) => value;
        /// The target replacement cancellation.
        pub replacement_cancellation() -> &ReplacementCancellation = Self::ReplacementCancelled(value) => value;
    }
}
