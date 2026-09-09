//! Direct-sum decomposition: verified splits, idempotent splitting, and
//! certificates.
//!
//! A [`Split`] checks its identities at construction, so holding one is proof of a
//! direct-sum decomposition. [`decompose`] splits until each summand reaches one
//! of two states. In the first, the summand's endomorphism algebra is local, which
//! [`crate::endo::EndoAlgebra`] decides exactly, so the summand is indecomposable
//! ([`Certificate::Indecomposable`]). In the second, every splitting route has run
//! out and nothing is claimed either way ([`Certificate::Undetermined`]).
//!
//! Splitting tries three routes in order: a lifted central idempotent of the
//! semisimple quotient, a constructed non-unit non-nilpotent element, and
//! seeded-random Fitting elements `M = ker(φⁿ) ⊕ im(φⁿ)` with a bounded retry
//! count.
//!
//! `Undetermined` is reachable, not a formality. Every route is bounded, and the
//! constructed route needs a drawn minimal polynomial that is squarefree and
//! reducible, which is likely but not guaranteed.

mod algorithm;
mod outcome;
mod split;

pub use algorithm::decompose;
pub use outcome::{Certificate, Decomposition, IsoClass, KrullSchmidtOutcome, krull_schmidt};
pub use split::{Split, SplitError};

pub(crate) use algorithm::decompose_with_root_endo;
pub(crate) use outcome::krull_schmidt_from_decomposition;
pub(crate) use split::{add_morphisms, direct_sum_or_zero, inverse_morphism, mutually_inverse};

#[cfg(test)]
mod tests;
