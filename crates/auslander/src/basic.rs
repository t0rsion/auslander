//! Basic decompositions, projective support, and exact identity for basic
//! pairs.
//!
//! A pair is `(M, P)` with `P` projective. Both parts are basic: their
//! indecomposable summands are pairwise non-isomorphic.
//!
//! The module part is a [`BasicDecomposition`]. [`BasicDecomposition::new`]
//! runs [`crate::decompose::krull_schmidt`], certifies every summand through
//! [`crate::indec::IndecomposableModule`], and rejects a repeated summand with
//! [`BasicError::NotBasic`]. An undetermined summand is
//! [`BasicError::CertificationBlocked`], never a silent distinct value.
//!
//! Three constructors skip that work when basicness is already known:
//! [`BasicDecomposition::without`] drops a summand,
//! [`BasicDecomposition::with_new_summand`] appends a certified one, and
//! [`BasicDecomposition::from_catalog`] takes distinct catalog entries. Each
//! keeps the summand values it was given, which is what a
//! [`crate::taurigid::TauCache`] keyed by module identity needs.
//!
//! The projective part is a [`ProjectiveSupport`]. Over a basic algebra a
//! basic projective is determined by a vertex subset, so the type stores
//! sorted deduplicated vertices and rebuilds the canonical sum of `P_v` on
//! demand. Identity of the projective half is exact set equality.
//!
//! [`pair_iso`] decides identity of two pairs. It has no undecided outcome:
//! both inputs are certified basic pairs, and between certified
//! indecomposables the radical criterion either produces an isomorphism or
//! proves every composite lies in the radical. An undecided comparison is a
//! crate defect, reported as [`BasicError::Defect`].
//!
//! [`PairFingerprint`] is a cheap sound prefilter. Equal pairs have equal
//! fingerprints; equal fingerprints prove nothing, so the certified test
//! stays mandatory.

mod closure;
mod decomposition;
mod support;

pub use closure::*;
pub use decomposition::*;
pub(crate) use support::pairwise_distinct_by;
pub use support::*;

#[cfg(test)]
mod tests;
