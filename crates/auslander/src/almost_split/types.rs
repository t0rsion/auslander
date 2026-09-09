use crate::arquiver::IndecomposableCatalog;
use crate::ext::ExtClass;
use crate::field::Fp;
use crate::homspace::row_times;
use crate::indec::IndecomposableModule;
use crate::iso::{IsoOutcome, is_isomorphic};
use crate::linalg::DenseMat;
use crate::sequence::{NonSplitWitness, ShortExactSequence};

use super::stable::{action_matrices, ext_sequence_holds, socle_kernel};
use super::{catalog, stable_end};
use crate::ar::tau;

/// The outcome of [`crate::almost_split::almost_split`]. A projective module has no almost-split
/// sequence ending at it.
// An outcome is built once and matched once, so the size gap between the
// variants never costs a hot copy.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum AlmostSplitOutcome {
    /// The module is projective, so no almost-split sequence ends at it.
    Projective,
    /// The almost-split sequence ending at the module, with its witness.
    Sequence(AlmostSplitSequence),
}

/// An almost-split sequence `0 -> tau M -> E -> M -> 0` with the chosen AR
/// class it realizes and the witness that gates the claim.
///
/// Fields are private; construction goes through [`crate::almost_split::almost_split`] or
/// [`crate::almost_split::almost_split_via_catalog`], so every value passed the socle
/// construction and its internal gates.
#[derive(Clone, Debug)]
pub struct AlmostSplitSequence {
    pub(in crate::almost_split) sequence: ShortExactSequence,
    pub(in crate::almost_split) class: ExtClass,
    pub(in crate::almost_split) witness: AlmostSplitWitness,
}

impl AlmostSplitSequence {
    accessor_methods! {
        /// The sequence `0 -> tau M -> E -> M -> 0`.
        pub sequence() -> &ShortExactSequence = |this| &this.sequence;
        /// The chosen AR class: the first RREF row of the Ext socle.
        ///
        /// The class is deterministic, not canonical. Any nonzero socle element
        /// gives an almost-split sequence isomorphic to this one after suitable
        /// automorphisms of the end terms. With the end terms fixed, distinct
        /// socle classes are inequivalent extensions.
        pub chosen_ar_class() -> &ExtClass = |this| &this.class;
        /// The witness behind the almost-split claim.
        pub witness() -> &AlmostSplitWitness = |this| &this.witness;
    }

    /// Rechecks the AR duality witness against `m`, with the sequence and
    /// class this value holds.
    ///
    /// Returns false when the value carries the catalog witness instead; that
    /// route is [`AlmostSplitSequence::verify_with_catalog`]. See
    /// [`ArDualityWitness::verify`] for what is rechecked.
    pub fn verify(&self, m: &IndecomposableModule) -> bool {
        match &self.witness {
            AlmostSplitWitness::ArDuality(witness) => {
                witness.verify(m, &self.sequence, &self.class)
            }
            AlmostSplitWitness::ExhaustiveCatalog(_) => false,
        }
    }

    /// Rechecks the catalog witness against `m` and `catalog`, with the
    /// sequence and class this value holds.
    ///
    /// Returns false when the value carries the AR duality witness instead;
    /// that route is [`AlmostSplitSequence::verify`]. See
    /// [`crate::almost_split::CatalogWitness::verify`] for what is rechecked.
    pub fn verify_with_catalog(
        &self,
        m: &IndecomposableModule,
        catalog: &IndecomposableCatalog,
    ) -> bool {
        match &self.witness {
            AlmostSplitWitness::ExhaustiveCatalog(witness) => {
                witness.verify(m, catalog, &self.sequence, &self.class)
            }
            AlmostSplitWitness::ArDuality(_) => false,
        }
    }
}

/// Which route certified the sequence.
#[derive(Clone, Debug)]
pub enum AlmostSplitWitness {
    /// The AR duality route of [`crate::almost_split::almost_split`].
    ArDuality(ArDualityWitness),
    /// The exhaustive catalog route of
    /// [`crate::almost_split::almost_split_via_catalog`].
    ExhaustiveCatalog(catalog::CatalogWitness),
}

/// The stored data of the AR duality route: enough to recheck every gate of
/// the socle construction from the live modules.
#[derive(Clone, Debug)]
pub struct ArDualityWitness {
    // RREF coordinates of a basis of rad End(M), one element per row.
    pub(in crate::almost_split) radical_coords: DenseMat,
    // Coordinates of class . r_j per radical basis element, all zero.
    pub(in crate::almost_split) action_traces: Vec<Vec<Fp>>,
    // RREF basis of the socle kernel.
    pub(in crate::almost_split) socle_rref: DenseMat,
    // Index of the chosen socle row; the construction always picks 0.
    pub(in crate::almost_split) chosen_row: usize,
    pub(in crate::almost_split) ext_dim: usize,
    pub(in crate::almost_split) stable_end_dim: usize,
    pub(in crate::almost_split) socle_dim: usize,
    pub(in crate::almost_split) residue_degree: usize,
    pub(in crate::almost_split) non_split: NonSplitWitness,
}

impl ArDualityWitness {
    accessor_methods! {
        /// RREF coordinates of the stored `rad End(M)` basis, one element per
        /// row.
        pub radical_basis_coords() -> &DenseMat = |this| &this.radical_coords;
        /// The coordinates of `class . r_j` per radical basis element; every
        /// entry is zero.
        pub action_traces() -> &[Vec<Fp>] = |this| &this.action_traces;
        /// The RREF basis of the socle kernel.
        pub socle_rref() -> &DenseMat = |this| &this.socle_rref;
        /// The index of the chosen socle row, always 0. The choice is
        /// deterministic, not canonical, and [`ArDualityWitness::verify`] rejects
        /// any other row.
        pub chosen_row() -> usize = |this| this.chosen_row;
        /// The stored `dim_Fp Ext^1(M, tau M)`.
        pub ext_dim() -> usize = |this| this.ext_dim;
        /// The stored `dim_Fp stable End(M)`.
        pub stable_end_dim() -> usize = |this| this.stable_end_dim;
        /// The stored socle dimension.
        pub socle_dim() -> usize = |this| this.socle_dim;
        /// The stored residue degree of `End(M)`.
        pub residue_degree() -> usize = |this| this.residue_degree;
        /// The proof that the sequence does not split.
        pub non_split() -> &NonSplitWitness = |this| &this.non_split;
    }

    /// Rechecks the witness against the live modules.
    ///
    /// Starts from the class's own [`crate::ext::ExtSpace`]. Later checks read that space,
    /// so a tampered resolution, cocycle basis, coboundary basis, complement,
    /// or representative would otherwise certify itself.
    /// [`crate::ext::ExtSpace::matches_recomputation`] rebuilds all of it from the live
    /// endpoint modules and compares. The checks are:
    ///
    /// - The class's space equals a fresh recomputation, field by field.
    /// - The AR translate, recomputed through the certified double route, is
    ///   isomorphic to the space's target and passes the indecomposability
    ///   gate.
    /// - The stored radical basis equals the live `rad End(M)` basis, and the
    ///   action matrices are recomputed from it.
    /// - The recomputed socle kernel equals the stored RREF, and every stored
    ///   socle row annihilates every action matrix.
    /// - The chosen row is row 0, the row the construction always picks, and
    ///   it carries the class's coordinates; the class is nonzero.
    /// - The stored action traces equal fresh products and are all zero.
    /// - The two dimension equalities hold against fresh computations.
    /// - The sequence is exact through the [`ShortExactSequence`] constructor
    ///   and recovers the class.
    /// - [`NonSplitWitness::verify`] passes.
    ///
    /// The sequence and class are the caller's, not this witness's own. For
    /// the pair the almost-split value holds, call
    /// [`AlmostSplitSequence::verify`].
    pub fn verify(
        &self,
        m: &IndecomposableModule,
        sequence: &ShortExactSequence,
        class: &ExtClass,
    ) -> bool {
        let space = class.space();
        verify_guard!(ext_sequence_holds(m, sequence, class));
        // The construction uses tau(m) as the Ext space target, and the
        // recomputed translate is a fresh module value. So the comparison has
        // to be a certified isomorphism, not pointer identity. An Unknown
        // outcome fails verification.
        let_or_false!(Ok(translate) = tau(m.module()));
        verify_guard!(IndecomposableModule::new(&translate).is_ok());
        verify_guard!(matches!(
            is_isomorphic(&translate, space.target()),
            Ok(IsoOutcome::Isomorphic(_))
        ));
        let field = m.module().field();
        verify_guard!(self.radical_coords == *m.endo().radical_basis());
        let d = space.dim();
        verify_guard!(self.ext_dim == d && self.ext_dim == self.stable_end_dim);
        let_or_false!(Ok(stable) = stable_end(m.module()));
        verify_guard!(stable.dim() == self.stable_end_dim);
        verify_guard!(
            self.socle_dim == self.socle_rref.rows()
                && self.residue_degree == m.residue_degree()
                && self.socle_dim == self.residue_degree
        );
        let_or_false!(Ok(action) = action_matrices(m, space));
        verify_guard!(socle_kernel(&action, d, &field) == self.socle_rref);
        verify_guard!(!(0..self.socle_rref.rows()).any(|r| {
            action.iter().any(|a| {
                row_times(self.socle_rref.row(r), a, &field)
                    .iter()
                    .any(|v| !v.is_zero())
            })
        }));
        // Row 0 is the crate's choice, and the determinism fingerprint pins
        // its coordinates. Another socle row would give an almost-split
        // sequence too, but not this crate's, so it is rejected here.
        verify_guard!(
            self.chosen_row == 0
                && self.socle_rref.rows() > 0
                && class.coordinates() == self.socle_rref.row(0)
                && !class.is_zero()
        );
        verify_guard!(
            self.action_traces.len() == action.len()
                && !self.action_traces.iter().zip(&action).any(|(trace, a)| {
                    *trace != row_times(class.coordinates(), a, &field)
                        || trace.iter().any(|v| !v.is_zero())
                })
        );
        self.non_split.verify(sequence)
    }
}
