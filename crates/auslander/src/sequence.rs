//! Checked short exact sequences: construction from an `Ext^1` class, recovery
//! of that class, and split status with a proof either way.
//!
//! [`ShortExactSequence::new`] checks exactness one vertex at a time. The
//! inclusion is mono by rank, the projection is epi by rank, the composite is
//! zero, and the dimensions add. Those four facts together force image equals
//! kernel, so nothing else is computed.
//!
//! [`ShortExactSequence::split_status`] solves the retraction system in a fixed
//! order. The unknowns are the entries of `r: E -> N`, vertex-major then
//! row-major. The equations are the commuting squares in (arrow, row, column)
//! lexicographic order, then the `iota.then(r) = id` constraints, again
//! vertex-major then row-major. A solution gives a [`SplitWitness`]. An
//! inconsistent system gives a [`NonSplitWitness`] holding a dual vector `y`
//! with `y A = 0` and `y b = 1`. That `y` is the identity block of the pivot
//! row of the RREF of the augmented system `[A | b | I]`. The pivot of that row
//! sits in the `b` column, and RREF makes it 1, so `y b = 1` holds and fixes
//! the scale of `y`. No further normalization is needed. Either witness
//! rechecks by multiplication alone.

mod construction;
mod helpers;
mod splitting;

use crate::field::Fp;
use crate::hom::{Morphism, matrix_is_zero};
use crate::module::Module;

/// Rejected short exact sequence input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SequenceError {
    /// The inclusion's target is not the projection's source (by
    /// [`Module::ptr_eq`]).
    EndpointMismatch,
    /// The inclusion's rank at this vertex is below the sub dimension, so the
    /// inclusion is not mono.
    NotMono { vertex: u32 },
    /// The projection's rank at this vertex is below the quotient dimension,
    /// so the projection is not epi.
    NotEpi { vertex: u32 },
    /// The composite inclusion-then-projection is nonzero at this vertex.
    CompositeNonzero { vertex: u32 },
    /// `dim middle != dim sub + dim quotient` at this vertex.
    DimensionMismatch { vertex: u32 },
    /// The class or space has the wrong cohomological degree.
    WrongDegree { expected: usize, got: usize },
    /// The space's source module is not this sequence's quotient (by
    /// [`Module::ptr_eq`]).
    SpaceSourceMismatch,
    /// The space's target module is not this sequence's sub (by
    /// [`Module::ptr_eq`]).
    SpaceTargetMismatch,
}

display_error! { error SequenceError {
    Self::EndpointMismatch => "the inclusion's target is not the projection's source";
    Self::NotMono { vertex } => "the inclusion is not mono at vertex {vertex}";
    Self::NotEpi { vertex } => "the projection is not epi at vertex {vertex}";
    Self::CompositeNonzero { vertex } => "the composite is nonzero at vertex {vertex}";
    Self::DimensionMismatch { vertex } => "the middle dimension is not sub plus quotient at vertex {vertex}";
    Self::WrongDegree { expected, got } => "degree is {got}, this operation needs degree {expected}";
    Self::SpaceSourceMismatch => "the space's source module is not the sequence's quotient";
    Self::SpaceTargetMismatch => "the space's target module is not the sequence's sub";
} }

/// A short exact sequence `0 -> sub -> middle -> quotient -> 0`, exact per
/// vertex by construction.
///
/// Fields are private; construction goes through [`ShortExactSequence::new`]
/// or [`ShortExactSequence::from_ext1`], so every value is exact.
#[derive(Clone, Debug)]
pub struct ShortExactSequence {
    sub: Module,
    middle: Module,
    quotient: Module,
    inclusion: Morphism,
    projection: Morphism,
}

impl ShortExactSequence {
    /// Builds the sequence after checking, one vertex at a time: the inclusion
    /// is mono by rank, the projection is epi by rank, the composite is zero,
    /// and `dim middle = dim sub + dim quotient`. Those four force exactness.
    ///
    /// # Errors
    /// [`SequenceError::EndpointMismatch`] when the inclusion's target is not
    /// the projection's source, otherwise the per-vertex variant naming the
    /// first vertex that fails.
    pub fn new(
        inclusion: Morphism,
        projection: Morphism,
    ) -> Result<ShortExactSequence, SequenceError> {
        if !inclusion.target().ptr_eq(projection.source()) {
            return Err(SequenceError::EndpointMismatch);
        }
        let sub = inclusion.source().clone();
        let middle = inclusion.target().clone();
        let quotient = projection.target().clone();
        let field = sub.field();
        let nv = sub.algebra().quiver().num_vertices();
        for v in 0..nv {
            if inclusion.map_at(v).rank(&field) < sub.dim_at(v) {
                return Err(SequenceError::NotMono { vertex: v });
            }
        }
        for v in 0..nv {
            if projection.map_at(v).rank(&field) < quotient.dim_at(v) {
                return Err(SequenceError::NotEpi { vertex: v });
            }
        }
        let composite = inclusion.then(&projection).expect("endpoints were checked");
        for v in 0..nv {
            if !matrix_is_zero(composite.map_at(v)) {
                return Err(SequenceError::CompositeNonzero { vertex: v });
            }
        }
        for v in 0..nv {
            if middle.dim_at(v) != sub.dim_at(v) + quotient.dim_at(v) {
                return Err(SequenceError::DimensionMismatch { vertex: v });
            }
        }
        Ok(ShortExactSequence {
            sub,
            middle,
            quotient,
            inclusion,
            projection,
        })
    }

    accessor_methods! {
        /// The sub module `N`.
        pub sub() -> &Module = |this| &this.sub;
        /// The middle module `E`.
        pub middle() -> &Module = |this| &this.middle;
        /// The quotient module `M`.
        pub quotient() -> &Module = |this| &this.quotient;
        /// The inclusion `N -> E`.
        pub inclusion() -> &Morphism = |this| &this.inclusion;
        /// The projection `E -> M`.
        pub projection() -> &Morphism = |this| &this.projection;
    }
}

/// The outcome of [`ShortExactSequence::split_status`]; each variant carries
/// its proof.
#[derive(Clone, Debug)]
pub enum SplitStatus {
    /// The sequence splits, with the retraction and section that prove it.
    Split(SplitWitness),
    /// The sequence does not split, with the dual vector that proves the
    /// retraction system inconsistent.
    NonSplit(NonSplitWitness),
}

/// A retraction and section proving a sequence split.
#[derive(Clone, Debug)]
pub struct SplitWitness {
    retraction: Morphism,
    section: Morphism,
}

impl SplitWitness {
    accessor_methods! {
        /// The retraction `r: E -> N` with `iota.then(r) = id`.
        pub retraction() -> &Morphism = |this| &this.retraction;
        /// The section `s: M -> E` with `s.then(projection) = id`.
        pub section() -> &Morphism = |this| &this.section;
    }
}

/// A dual vector proving the retraction system inconsistent: `y A = 0` and
/// `y b = 1` for the system built in the fixed order.
#[derive(Clone, Debug)]
pub struct NonSplitWitness {
    dual: Vec<Fp>,
}

impl NonSplitWitness {
    accessor_methods! {
        /// The dual vector, one entry per equation of the retraction system.
        pub dual() -> &[Fp] = |this| &this.dual;
    }
}

#[cfg(test)]
mod tests;
