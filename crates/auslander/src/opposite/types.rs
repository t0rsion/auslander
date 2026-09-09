use std::sync::Arc;

use crate::algebra::Algebra;
use crate::quiver::{ArrowId, PathWord, Quiver, QuiverError};

/// Rejected duality or element-matrix input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OppositeError {
    /// The value lives over an algebra that is neither side of the [`OppositeMap`].
    AlgebraOutsidePair,
    /// `dual_of_target` is not entrywise the dual of the morphism's target.
    NotDualOfTarget,
    /// `dual_of_source` is not entrywise the dual of the morphism's source.
    NotDualOfSource,
    /// A summand vertex outside `0..num_vertices`.
    SummandOutOfRange { vertex: u32, num_vertices: u32 },
    /// `entries` needs one row per source summand.
    RowCountMismatch { expected: usize, got: usize },
    /// Row `row` of `entries` needs one entry per target summand.
    ColumnCountMismatch {
        row: usize,
        expected: usize,
        got: usize,
    },
    /// Entry `(row, col)` needs one coefficient per normal word from
    /// `targets[col]` to `sources[row]`.
    CoefficientCountMismatch {
        row: usize,
        col: usize,
        expected: usize,
        got: usize,
    },
    /// Entry `(row, col)` holds a coefficient at `index` whose representative is
    /// not canonical for the algebra's field.
    NonCanonicalCoefficient {
        row: usize,
        col: usize,
        index: usize,
    },
    /// The morphism's source is not entrywise the standard direct sum of the
    /// declared source summands.
    SourceNotTheDeclaredSum,
    /// As [`Self::SourceNotTheDeclaredSum`], for the target.
    TargetNotTheDeclaredSum,
}

display_error! { error OppositeError {
    Self::AlgebraOutsidePair => "the algebra is neither side of the opposite pair";
    Self::NotDualOfTarget => "dual_of_target is not the entrywise dual of the morphism's target";
    Self::NotDualOfSource => "dual_of_source is not the entrywise dual of the morphism's source";
    Self::SummandOutOfRange { vertex, num_vertices } => "summand vertex {vertex} outside 0..{num_vertices}";
    Self::RowCountMismatch { expected, got } => "entries has {got} rows, sources has {expected} summands";
    Self::ColumnCountMismatch { row, expected, got } => "entries row {row} has {got} columns, targets has {expected} summands";
    Self::CoefficientCountMismatch { row, col, expected, got } => "entry ({row}, {col}) has {got} coefficients, its path component has {expected}";
    Self::NonCanonicalCoefficient { row, col, index } => "entry ({row}, {col}) has a non-canonical coefficient at index {index} for the algebra's field";
    Self::SourceNotTheDeclaredSum => "the morphism's source is not the standard direct sum of the declared source summands";
    Self::TargetNotTheDeclaredSum => "the morphism's target is not the standard direct sum of the declared target summands";
} }

/// An algebra paired with its opposite, carrying the arrow and word
/// correspondence in both directions.
///
/// Arrow ids are shared: arrow `a: i → j` of one side corresponds to the arrow
/// with the same id running `j → i` on the other, and a path word corresponds
/// to its reversal.
#[derive(Clone, Debug)]
pub struct OppositeMap {
    pub(super) algebra: Arc<Algebra>,
    pub(super) opposite: Arc<Algebra>,
}

impl OppositeMap {
    accessor_methods! {
        /// The original algebra.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The opposite algebra.
        pub opposite() -> &Arc<Algebra> = |this| &this.opposite;
        /// The opposite-side arrow of `a`: the same id, endpoints swapped.
        ///
        /// # Panics
        /// Panics unless `a` is an arrow of the algebra's quiver.
        pub arrow_to_op(a: ArrowId) -> ArrowId = |this| checked_arrow(a, this.algebra.quiver().num_arrows(), "arrow_to_op");
        /// The algebra-side arrow of an opposite arrow, as [`Self::arrow_to_op`].
        ///
        /// # Panics
        /// Panics unless `a` is an arrow of the opposite quiver.
        pub arrow_from_op(a: ArrowId) -> ArrowId = |this| checked_arrow(a, this.opposite.quiver().num_arrows(), "arrow_from_op");
    }

    /// The reversal of a path word of the algebra as a word of the opposite.
    /// Errors when `word` is not a path of the algebra's quiver.
    pub fn word_to_op(&self, word: &PathWord) -> Result<PathWord, QuiverError> {
        word.validate_in(self.algebra.quiver())?;
        Ok(reversed(word, self.opposite.quiver()))
    }

    /// The reversal of a word of the opposite as a word of the algebra, as
    /// [`Self::word_to_op`].
    pub fn word_from_op(&self, word: &PathWord) -> Result<PathWord, QuiverError> {
        word.validate_in(self.opposite.quiver())?;
        Ok(reversed(word, self.algebra.quiver()))
    }

    pub(super) fn other_side(
        &self,
        algebra: &Arc<Algebra>,
    ) -> Result<&Arc<Algebra>, OppositeError> {
        if Arc::ptr_eq(algebra, &self.algebra) {
            Ok(&self.opposite)
        } else if Arc::ptr_eq(algebra, &self.opposite) {
            Ok(&self.algebra)
        } else {
            Err(OppositeError::AlgebraOutsidePair)
        }
    }
}

fn checked_arrow(arrow: ArrowId, count: usize, site: &str) -> ArrowId {
    assert!(
        arrow.index() < count,
        "{site}: arrow id {} out of range",
        arrow.0
    );
    arrow
}

/// Caller guarantees `word` is a path of the quiver that `quiver` reverses.
/// The reversed arrows then compose left to right in `quiver` itself.
pub(super) fn reversed(word: &PathWord, quiver: &Quiver) -> PathWord {
    if word.is_trivial() {
        PathWord::trivial_unchecked(word.source())
    } else {
        let arrows = word.arrows().iter().rev().copied().collect();
        PathWord::from_arrows_unchecked(quiver, arrows)
    }
}
