//! Support tau-tilting pairs, decided by support arithmetic, and a
//! definition-only enumerator over an exhaustive catalog.
//!
//! A pair is `(M, P)` with `M` basic and `P` a basic projective. It is a
//! support tau-tilting pair when `Hom(P, M) = 0`, `M` is tau-rigid, and
//! `|M| + |P| = n`, where `n` is the number of vertices and `|X|` counts
//! indecomposable summands. [`AlmostCompletePair`] takes the same conditions
//! with `|M| + |P| = n - 1`. Mutation is defined through it.
//!
//! The projective part is forced, not searched. Take `M` tau-rigid and write
//! `r = |M|`, `s` for the number of vertices where `M` is nonzero, and `C` for
//! the remaining vertices. Then a support tau-tilting pair with module part
//! `M` exists exactly when `r = s`, and its projective part is the sum of
//! `P_v` over `C`. An almost complete pair with module part `M` has `P` equal
//! to `C` when `s = r + 1`, and to `C` minus one vertex when `s = r`. No other
//! case is possible. So [`SupportTauTiltingPair`] stores the module part and
//! the tau-rigidity witness alone, [`AlmostCompletePair`] adds the omitted
//! vertex, and both derive the support on request. The proofs sit on
//! `support_complement` and on the two `classify_with_cache` constructors.
//!
//! The projective part is a vertex subset because every algebra this crate
//! builds is a bound quiver algebra `kQ/I` with `I` admissible, which makes
//! it basic: the indecomposable projectives are the `n` modules
//! `P_v = e_v A`, pairwise non-isomorphic. Nothing here needs `Q` connected.
//!
//! Tau-rigidity is decided summandwise, through
//! [`crate::taurigid::is_tau_rigid_summandwise`] over a
//! [`crate::taurigid::TauCache`]. `tau` never runs on an assembled module.
//! Additivity of `tau` and `Hom` makes the summandwise
//! calculation exact. It says nothing about which part of `tau` dominates
//! cost, so no claim about that is made here.
//!
//! [`enumerate_over_catalog`] lists the pairs of one algebra from the
//! definition alone, with no mutation theory. Its completeness is the
//! classification theorem behind an [`crate::arquiver::IndecomposableCatalog`],
//! so it runs only over the algebras such a catalog covers.

mod almost;
mod catalog;
mod conditions;
mod errors;
mod pair;

pub use almost::{AlmostCompleteClassification, AlmostCompletePair};
pub use catalog::{CatalogEnumeration, enumerate_over_algebra, enumerate_over_catalog};
pub use errors::{PairRejection, SupportTauError};
pub use pair::{SupportTauTiltingClassification, SupportTauTiltingPair};

#[cfg(test)]
mod tests;
