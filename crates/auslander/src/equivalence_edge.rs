//! Composable Rickard equivalence edges from certified tilting complexes.

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::complex_target::{
    ComplexTargetError, ComplexTargetOutcome, VerifiedComplexTargetPresentation,
    present_complex_target,
};
use crate::target::TargetLimits;
use crate::tilting_complex::CertifiedTiltingComplex;

fn same_algebra(left: &Algebra, right: &Algebra) -> bool {
    left.certificate() == right.certificate()
}

/// A checked Rickard equivalence from `A` to `End_K(T)^op`.
#[derive(Clone, Debug)]
pub struct DerivedEquivalenceEdge {
    tilting: CertifiedTiltingComplex,
    target: VerifiedComplexTargetPresentation,
}

impl DerivedEquivalenceEdge {
    /// Recovers the split target of one certified tilting complex.
    pub fn recover(
        tilting: CertifiedTiltingComplex,
        limits: &TargetLimits,
    ) -> Result<DerivedEquivalenceEdgeOutcome, ComplexTargetError> {
        match present_complex_target(&tilting, limits)? {
            ComplexTargetOutcome::Presented(target) => Ok(
                DerivedEquivalenceEdgeOutcome::Certified(Box::new(DerivedEquivalenceEdge {
                    tilting,
                    target: *target,
                })),
            ),
            ComplexTargetOutcome::Cut(cut) => Ok(DerivedEquivalenceEdgeOutcome::Cut(cut)),
        }
    }

    accessor_methods! {
        /// The source algebra.
        pub source() -> &Arc<Algebra> = |this| this.tilting.candidate().algebra();
        /// The certified tilting complex.
        pub tilting() -> &CertifiedTiltingComplex = |this| &this.tilting;
        /// The verified target presentation.
        pub target_presentation() -> &VerifiedComplexTargetPresentation = |this| &this.target;
        /// The target algebra.
        pub target() -> &Arc<Algebra> = |this| this.target.target();
    }

    /// Rechecks the tilting claim and the recovered coordinate algebra map.
    pub fn verify(&self) -> bool {
        self.tilting.verify()
            && self.target.verify()
            && self
                .target
                .tilting()
                .candidate()
                .summands()
                .iter()
                .zip(self.tilting.candidate().summands())
                .all(|(left, right)| left.complex().agrees_with(right.complex()))
    }

    /// Starts a composable path with this forward edge.
    pub fn path(&self) -> DerivedEquivalencePath {
        DerivedEquivalencePath {
            source: self.source().clone(),
            steps: vec![DirectedDerivedEquivalence {
                edge: self.clone(),
                direction: EquivalenceDirection::Forward,
            }],
        }
    }

    /// Returns the checked formal inverse of this Rickard edge.
    pub fn inverse(&self) -> DirectedDerivedEquivalence {
        DirectedDerivedEquivalence {
            edge: self.clone(),
            direction: EquivalenceDirection::Inverse,
        }
    }
}

/// Edge construction completed or retained a target cut.
#[derive(Clone, Debug)]
pub enum DerivedEquivalenceEdgeOutcome {
    /// A complete equivalence edge.
    Certified(Box<DerivedEquivalenceEdge>),
    /// Target recovery stopped at a typed limit.
    Cut(Box<crate::complex_target::ComplexTargetCut>),
}

/// The direction in which one stored Rickard edge is used.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EquivalenceDirection {
    /// From the tilting complex's source to its endomorphism target.
    Forward,
    /// The inverse equivalence from the target to the source.
    Inverse,
}

/// One forward or inverse use of a certified edge.
#[derive(Clone, Debug)]
pub struct DirectedDerivedEquivalence {
    edge: DerivedEquivalenceEdge,
    direction: EquivalenceDirection,
}

impl DirectedDerivedEquivalence {
    accessor_methods! {
        /// The underlying certified edge.
        pub edge() -> &DerivedEquivalenceEdge = |this| &this.edge;
        /// The selected direction.
        pub direction() -> EquivalenceDirection = |this| this.direction;
    }

    /// The algebra at which this directed edge starts.
    pub fn source(&self) -> &Arc<Algebra> {
        match self.direction {
            EquivalenceDirection::Forward => self.edge.source(),
            EquivalenceDirection::Inverse => self.edge.target(),
        }
    }

    /// The algebra at which this directed edge ends.
    pub fn target(&self) -> &Arc<Algebra> {
        match self.direction {
            EquivalenceDirection::Forward => self.edge.target(),
            EquivalenceDirection::Inverse => self.edge.source(),
        }
    }

    /// Reverses this use of the stored edge.
    pub fn inverse(&self) -> DirectedDerivedEquivalence {
        DirectedDerivedEquivalence {
            edge: self.edge.clone(),
            direction: match self.direction {
                EquivalenceDirection::Forward => EquivalenceDirection::Inverse,
                EquivalenceDirection::Inverse => EquivalenceDirection::Forward,
            },
        }
    }
}

/// Why two equivalence paths do not compose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EquivalenceCompositionError {
    /// The left target and right source have different completion certificates.
    AlgebraMismatch,
}

display_error! { error EquivalenceCompositionError {
    Self::AlgebraMismatch => "equivalence paths meet at different algebras";
} }

/// An ordered composition of certified forward and inverse edges.
#[derive(Clone, Debug)]
pub struct DerivedEquivalencePath {
    source: Arc<Algebra>,
    steps: Vec<DirectedDerivedEquivalence>,
}

impl DerivedEquivalencePath {
    /// Builds the identity path on one checked algebra.
    pub fn identity(algebra: &Arc<Algebra>) -> DerivedEquivalencePath {
        DerivedEquivalencePath {
            source: algebra.clone(),
            steps: Vec::new(),
        }
    }

    accessor_methods! {
        /// The first algebra.
        pub source() -> &Arc<Algebra> = |this| &this.source;
        /// The ordered directed edges.
        pub steps() -> &[DirectedDerivedEquivalence] = |this| &this.steps;
    }

    /// The last algebra.
    pub fn target(&self) -> &Arc<Algebra> {
        self.steps
            .last()
            .map_or(&self.source, DirectedDerivedEquivalence::target)
    }

    /// Appends one directed edge after checking the middle algebra.
    pub fn then_edge(
        &self,
        next: DirectedDerivedEquivalence,
    ) -> Result<DerivedEquivalencePath, EquivalenceCompositionError> {
        if !same_algebra(self.target(), next.source()) {
            return Err(EquivalenceCompositionError::AlgebraMismatch);
        }
        let mut steps = self.steps.clone();
        steps.push(next);
        Ok(DerivedEquivalencePath {
            source: self.source.clone(),
            steps,
        })
    }

    /// Composes two checked paths without flattening their edge certificates.
    pub fn then(
        &self,
        next: &DerivedEquivalencePath,
    ) -> Result<DerivedEquivalencePath, EquivalenceCompositionError> {
        if !same_algebra(self.target(), next.source()) {
            return Err(EquivalenceCompositionError::AlgebraMismatch);
        }
        let mut steps = self.steps.clone();
        steps.extend(next.steps.clone());
        Ok(DerivedEquivalencePath {
            source: self.source.clone(),
            steps,
        })
    }

    /// Reverses the path and every stored edge direction.
    pub fn inverse(&self) -> DerivedEquivalencePath {
        DerivedEquivalencePath {
            source: self.target().clone(),
            steps: self
                .steps
                .iter()
                .rev()
                .map(DirectedDerivedEquivalence::inverse)
                .collect(),
        }
    }

    /// Rechecks every edge and each structural middle-algebra identification.
    pub fn verify(&self) -> bool {
        let mut current = &self.source;
        for step in &self.steps {
            if !step.edge.verify() || !same_algebra(current, step.source()) {
                return false;
            }
            current = step.target();
        }
        true
    }
}
