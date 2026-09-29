use std::sync::Arc;

use crate::algebra::Algebra;
use crate::control::ComputationControl;

use super::{
    DerivedInvariantKind, DerivedInvariants, InvariantLimits, InvariantReading, InvariantValue,
    derived_invariant,
};

/// Why two invariant records give no inequivalence witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessError {
    /// The algebras live over different prime fields.
    FieldMismatch { left: u64, right: u64 },
    /// The records were computed under different limits.
    LimitsMismatch,
    /// The named invariant has no two finished values that differ.
    NoDifference(DerivedInvariantKind),
}

display_error! { error WitnessError {
    Self::FieldMismatch { left, right } => "the algebras live over GF({left}) and GF({right})";
    Self::LimitsMismatch => "the invariant records use different limits";
    Self::NoDifference(kind) => "the invariant {kind:?} does not separate the algebras";
} }

/// Two algebras over one field and one derived invariant whose finished values
/// differ, which proves that the algebras are not derived equivalent.
#[derive(Clone, Debug)]
pub struct DerivedInequivalenceWitness {
    pub(super) left: Arc<Algebra>,
    pub(super) right: Arc<Algebra>,
    pub(super) kind: DerivedInvariantKind,
    pub(super) limits: InvariantLimits,
    pub(super) left_value: InvariantValue,
    pub(super) right_value: InvariantValue,
}

impl DerivedInequivalenceWitness {
    /// Builds a witness from two computed records and the separating kind.
    ///
    /// Errors when the fields or the limits differ, or when `kind` does not
    /// separate the records. See [`super::first_difference`].
    pub fn new(
        left: &DerivedInvariants,
        right: &DerivedInvariants,
        kind: DerivedInvariantKind,
    ) -> Result<DerivedInequivalenceWitness, WitnessError> {
        let (left_field, right_field) = (left.algebra.field(), right.algebra.field());
        if left_field != right_field {
            return Err(WitnessError::FieldMismatch {
                left: left_field.modulus(),
                right: right_field.modulus(),
            });
        }
        if left.limits != right.limits {
            return Err(WitnessError::LimitsMismatch);
        }
        match (left.reading(kind), right.reading(kind)) {
            (InvariantReading::Finished(left_value), InvariantReading::Finished(right_value))
                if left_value.differs_from(right_value) =>
            {
                Ok(DerivedInequivalenceWitness {
                    left: left.algebra.clone(),
                    right: right.algebra.clone(),
                    kind,
                    limits: left.limits,
                    left_value: left_value.clone(),
                    right_value: right_value.clone(),
                })
            }
            _ => Err(WitnessError::NoDifference(kind)),
        }
    }

    accessor_methods! {
        /// The first algebra.
        pub left() -> &Arc<Algebra> = |this| &this.left;
        /// The second algebra.
        pub right() -> &Arc<Algebra> = |this| &this.right;
        /// The separating invariant.
        pub kind() -> DerivedInvariantKind = |this| this.kind;
        /// The limits under which both values finished.
        pub limits() -> InvariantLimits = |this| this.limits;
        /// The value for the first algebra.
        pub left_value() -> &InvariantValue = |this| &this.left_value;
        /// The value for the second algebra.
        pub right_value() -> &InvariantValue = |this| &this.right_value;
    }

    /// Recomputes the invariant for both algebras from scratch.
    ///
    /// Accepts only when both fields agree, both recomputed values finish and
    /// equal the stored values, and the values differ.
    pub fn verify(&self) -> bool {
        let control = ComputationControl::new();
        let recomputed = |algebra, stored: &InvariantValue| {
            matches!(
                derived_invariant(algebra, self.kind, self.limits, &control),
                Ok(InvariantReading::Finished(value)) if value == *stored
            )
        };
        self.left.field() == self.right.field()
            && self.left_value.differs_from(&self.right_value)
            && recomputed(&self.left, &self.left_value)
            && recomputed(&self.right, &self.right_value)
    }
}
