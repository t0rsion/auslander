//! Projectively trivial maps, stable Hom, the AR socle construction, and
//! witnessed almost-split sequences.
//!
//! Factorization lemma: a map `f: M -> N` factors through some projective
//! module exactly when it factors through the projective cover
//! `pi_N: P(N) -> N`. Proof: take `f = a.then(b)` with projective middle `Q`.
//! Then `b: Q -> N` lifts through the epi `pi_N` because `Q` is projective,
//! giving `b = b'.then(pi_N)` and `f = (a.then(b')).then(pi_N)`. So the
//! projectively trivial subspace of `Hom(M, N)` is the image of
//! `Hom(M, P(N)) -> Hom(M, N)`, `h -> h.then(pi_N)`, and [`stable_hom`] is the
//! quotient of `Hom(M, N)` by that image.
//!
//! `End(M)` acts on `Ext^1(M, tau M)` on the left, equivalently as a right
//! `End(M)^op` action. For `phi` in `End(M)`, lift `phi` over the minimal
//! resolution of `M`: `phi_0: P_0 -> P_0` with `phi_0.then(aug) = aug.then(phi)`,
//! then `phi_1: P_1 -> P_1` with `phi_1.then(d_1) = d_1.then(phi_0)`. The
//! action on the class of a representative cocycle `c: P_1 -> tau M` is the
//! class of `phi_1.then(c)`. Writing `A_phi` for the matrix of that map in the
//! fixed Ext basis, `Ext^1(-, tau M)` is contravariant, so
//! `A_{phi.then(psi)} = A_psi A_phi`: the assignment reverses the crate's
//! diagrammatic product and is an anti-representation, not a representation.
//!
//! The socle is unaffected, which is why the crate keeps the left action.
//! `rad End(M)` is a two-sided ideal, so its left and right annihilators in
//! `Ext^1(M, tau M)` are the same set, and the kernel of the stacked action
//! matrices is that set either way.
//!
//! A projectively trivial endomorphism acts as zero, because `Ext^1(P, -) = 0`,
//! so the action factors through [`stable_end`]. Every lift solves its systems
//! with free variables zeroed, so the action matrices are deterministic in the
//! fixed Ext basis.
//!
//! Socle criterion (Auslander, Reiten, and Smalo, "Representation Theory of
//! Artin Algebras", IV.2 with V.2). Let `M` be indecomposable and
//! non-projective over an Artin algebra. Then `Ext^1(M, tau M)` is dual to the
//! stable endomorphism algebra of `M`, which here means [`stable_end`]:
//! `End(M)` modulo the maps that factor through a projective. The duality is
//! natural in both arguments, and the nonzero elements of the socle of
//! `Ext^1(M, tau M)` as an `End(M)`-module are exactly the almost-split
//! classes. The socle is the annihilator of `rad End(M)`, one set on either
//! side. Naturality turns annihilation by `rad End(M)` into the
//! right-almost-split lifting property. The argument is cited, not re-proved
//! in code. The code checks the hypotheses: the
//! [`crate::indec::IndecomposableModule`] gate,
//! the projectivity cross-check, and the two dimension gates of the duality.
//! The theorem supplies the almost-split property itself.
//!
//! The chosen class is the first RREF row of the socle: deterministic, not
//! canonical. When the residue degree `d` of `M` exceeds 1, the socle has
//! dimension `d` over `F_p` and no basis-independent preferred element exists.
//! With the end terms fixed, distinct nonzero socle classes are inequivalent
//! as extensions. Their sequences are isomorphic after suitable automorphisms
//! of the end terms, so the almost-split sequence is unique up to isomorphism
//! of sequences.

mod catalog;
mod construction;
mod errors;
mod stable;
mod types;

pub use catalog::{CatalogEntryCheck, CatalogWitness};
pub use construction::{almost_split, almost_split_via_catalog};
pub use errors::{AlmostSplitError, DefectKind};
pub use stable::{projectively_trivial, stable_end, stable_hom};
pub use types::{AlmostSplitOutcome, AlmostSplitSequence, AlmostSplitWitness, ArDualityWitness};

#[cfg(test)]
mod tests;
