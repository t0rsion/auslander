//! Left mutation of a support tau-tilting pair at a module summand slot.
//!
//! A vertex is a pair `(M, P)` with module summands `X_1, ..., X_m`. Slot `j`
//! addresses `X_j`. Only module summands have slots. Mutation at a summand of
//! the projective part is always a right mutation, so a walk that descends
//! from `(A, 0)` never performs one. `docs/support-tau-tilting.md` section 8 records
//! that as a deviation from the earlier signed-slot design.
//!
//! Exactly one of two branches holds at a slot, and [`mutate_at`] decides
//! which by computation.
//!
//! 1. `X_j` lies in `Fac(M/X_j)`. The mutation at slot `j` is then a right
//!    mutation and there is no left mutation. [`FacWitness`] proves the
//!    membership by one rank comparison per vertex.
//! 2. Otherwise the left mutation exists. [`Mutation`] carries the target pair
//!    and a [`MutationWitness`].
//!
//! # Proof of adjacency
//!
//! The construction does not prove that the built pair is the mutation. The
//! proof runs through the almost complete pair:
//!
//! 1. `(U, Q) = (M/X_j, P)` is an almost complete support tau-tilting pair,
//!    certified by [`crate::supporttau::AlmostCompletePair`].
//! 2. `(M, P)` extends `(U, Q)`.
//! 3. `(M', P')` extends `(U, Q)`.
//! 4. The two completions are not isomorphic.
//! 5. `(M', P')` is a support tau-tilting pair, certified by
//!    [`crate::supporttau::SupportTauTiltingPair`].
//!
//! An almost complete support tau-tilting pair is a direct summand of exactly
//! two basic support tau-tilting pairs (Adachi, Iyama, and Reiten,
//! "tau-tilting theory", Compositio Math. 150 (2014), 415-452, Theorem 2.18,
//! two complements). With the five checks above, that theorem identifies
//! `(M', P')` as the mutation at slot `j`, and the `Fac` test of branch 1
//! identifies the direction (same paper, Definition-Proposition 2.28, and
//! Proposition 2.22: exactly one of `X in Fac U` and the containment
//! `perp(tau U) is inside perp(tau X)` holds).
//!
//! The theorem holds over an arbitrary field. Its hypothesis reads "let
//! `Lambda` be a finite dimensional `k`-algebra", and the algebraically closed
//! hypothesis of the paper's introduction is re-imposed at the head of section
//! 5, which would be pointless if it were already in force. Demonet, Iyama,
//! and Jasso, "tau-tilting finite algebras, bricks and g-vectors"
//! (arXiv:1503.00285), restate the same result over an arbitrary field for
//! right modules, which is this crate's setting. See
//! `docs/support-tau-tilting.md` section 8.
//!
//! The exchange sequence `X_j -> B -> Y -> 0` is stored as a construction
//! witness. It records how the target was built. It is not the proof of
//! adjacency.
//!
//! # Shapes
//!
//! The two shapes of a left mutation are [`ExchangeShape`]. The construction
//! decides between them by comparing supports, as in AIR Theorem 2.30(a) and
//! (b):
//!
//! - `supp(U)` is smaller than `supp(M)`: the cokernel is zero, `X_j` leaves
//!   the module part, and the one vertex of `supp(M) \ supp(U)` joins the
//!   projective support.
//! - `supp(U)` equals `supp(M)`: the cokernel is a sum of copies of one
//!   indecomposable `Y_1`, and `M' = U + Y_1` with the projective support
//!   unchanged.

mod build;
mod common;
mod engine;
mod error;
mod fac;
mod witness;

pub use engine::{Mutation, SlotOutcome, mutate_at, mutate_at_with_cache};
pub use error::{Endpoint, MutationDefect, MutationError};
pub use fac::FacWitness;
pub use witness::{ExchangeShape, MutationWitness};

#[cfg(test)]
mod tests;
