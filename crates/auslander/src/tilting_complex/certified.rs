use std::ops::Deref;

use super::cache::HomotopyBlockCache;
use super::classification::classify_with_goal;
use super::*;

/// Which shifted Hom spaces a classification requires to vanish.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OrthogonalityGoal {
    /// Every nonzero shift. The first nonzero class rejects.
    Tilting,
    /// Every positive shift. The first nonzero class in a negative shift is
    /// kept as [`CertifiedSiltingComplex::negative_class`], and later negative
    /// shifts are skipped.
    Silting,
}

/// A certified basic silting complex.
///
/// The summands are pairwise non-isomorphic with local degree-zero
/// endomorphism rings, the generation witness is checked, and
/// `Hom_K(T, T[q])` is zero for every `q > 0`. The complex is tilting exactly
/// when [`Self::negative_class`] is `None`. Every [`CertifiedTiltingComplex`]
/// dereferences to one.
#[derive(Clone)]
pub struct CertifiedSiltingComplex {
    pub(super) candidate: TiltingComplexCandidate,
    pub(super) generation: ThickGenerationWitness,
    pub(super) degree_zero_endomorphisms: Vec<HomotopyHomQuotient>,
    pub(super) degree_zero_residues: Vec<Vec<Fp>>,
    pub(super) zero_shifted_homs: Vec<TiltingHomCheck>,
    pub(super) negative_class: Option<Box<TiltingSelfOrthogonalityRejection>>,
    pub(super) limits: TiltingComplexLimits,
    pub(super) block_cache: HomotopyBlockCache,
    pub(super) work: TiltingComplexWork,
}

impl std::fmt::Debug for CertifiedSiltingComplex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CertifiedSiltingComplex")
            .field("summands", &self.candidate.len())
            .field("zero_shifted_homs", &self.zero_shifted_homs.len())
            .field("tilting", &self.negative_class.is_none())
            .field("hom_spaces_built", &self.work.hom_spaces_built())
            .field("hom_spaces_reused", &self.work.hom_spaces_reused())
            .finish()
    }
}

impl CertifiedSiltingComplex {
    accessor_methods! {
        /// The ordered projective-complex candidate.
        pub candidate() -> &TiltingComplexCandidate = |this| &this.candidate;
        /// The checked thick-generation witness.
        pub generation() -> &ThickGenerationWitness = |this| &this.generation;
        /// One degree-zero endomorphism quotient per summand.
        pub degree_zero_endomorphisms() -> &[HomotopyHomQuotient] = |this| &this.degree_zero_endomorphisms;
        /// The residue map `End_K(T_i) → k` of each summand, in the
        /// coordinates of its degree-zero endomorphism quotient. Its kernel is
        /// the radical.
        pub degree_zero_residues() -> &[Vec<Fp>] = |this| &this.degree_zero_residues;
        /// Every checked zero quotient in a nonzero shift.
        pub zero_shifted_homs() -> &[TiltingHomCheck] = |this| &this.zero_shifted_homs;
        /// A nonzero class in a negative shift, which rules out tilting.
        pub negative_class() -> Option<&TiltingSelfOrthogonalityRejection> = |this| this.negative_class.as_deref();
        /// The effective classification limits.
        pub limits() -> TiltingComplexLimits = |this| this.limits;
        /// The exact homotopy-block work for this classification.
        pub work() -> TiltingComplexWork = |this| this.work;
    }

    pub(super) fn block_cache(&self) -> &HomotopyBlockCache {
        &self.block_cache
    }

    /// The tilting certificate, when no negative class exists.
    ///
    /// Without a negative class the silting check examined every nonzero
    /// shift, so the certificate equals the one the tilting check builds.
    pub fn to_tilting(&self) -> Option<CertifiedTiltingComplex> {
        self.negative_class
            .is_none()
            .then(|| CertifiedTiltingComplex {
                silting: self.clone(),
            })
    }

    /// Recomputes the complete silting classification.
    pub fn verify(&self) -> bool {
        self.rebuilds(OrthogonalityGoal::Silting)
    }

    fn rebuilds(&self, goal: OrthogonalityGoal) -> bool {
        let rebuilt = classify_with_goal(
            self.candidate.clone(),
            Some(self.generation.clone()),
            self.limits,
            goal,
        );
        rebuilt.is_ok_and(|rebuilt| {
            rebuilt.zero_shifted_homs.len() == self.zero_shifted_homs.len()
                && rebuilt.negative_class.is_none() == self.negative_class.is_none()
                && rebuilt.degree_zero_residues == self.degree_zero_residues
        })
    }
}

/// A certified basic tilting complex: a silting complex whose shifted Hom
/// spaces vanish in every nonzero shift.
#[derive(Clone, Debug)]
pub struct CertifiedTiltingComplex {
    pub(super) silting: CertifiedSiltingComplex,
}

impl Deref for CertifiedTiltingComplex {
    type Target = CertifiedSiltingComplex;

    fn deref(&self) -> &CertifiedSiltingComplex {
        &self.silting
    }
}

impl CertifiedTiltingComplex {
    /// The silting certificate, which has no negative class.
    pub fn into_silting(self) -> CertifiedSiltingComplex {
        self.silting
    }

    /// Recomputes the complete tilting classification.
    pub fn verify(&self) -> bool {
        self.silting.negative_class.is_none() && self.silting.rebuilds(OrthogonalityGoal::Tilting)
    }
}
