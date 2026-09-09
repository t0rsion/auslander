//! Bound quiver algebras `kQ/I` with a certificate-verified normal-word basis.
//!
//! [`Algebra`] is the sole runtime algebra type. It owns a prime field, the
//! reduced Groebner basis of its ideal, the normal-word basis, and per-arrow
//! multiplication tables. Every `Algebra` comes from one pipeline: completion
//! emits a certificate, the independent verifier checks it, and the
//! constructor builds the tables from the verified data.
//!
//! Monomial input takes that pipeline. [`monomial_presentation`] turns a
//! [`crate::monomial::MonomialIdeal`] into a [`crate::relation::Presentation`] of one-term
//! relations, and [`monomial_limits`] derives budgets adequate for it. The
//! named constructors ([`linear_an`], [`kronecker`], and the rest) apply that
//! pair to the families of [`crate::monomial`].

#[path = "algebra_parts/build.rs"]
mod build;
#[path = "algebra_parts/constructors.rs"]
mod constructors;
#[path = "algebra_parts/operations.rs"]
mod operations;
#[path = "algebra_parts/radical.rs"]
mod radical;
#[path = "algebra_parts/types.rs"]
mod types;

pub use constructors::{
    an_with_relations, commutative_square, cyclic_nakayama, dual_numbers, kronecker, linear_an,
    linear_nakayama, monomial_algebra, monomial_limits, monomial_presentation, path_algebra,
    radical_square_zero_cycle, truncated_poly,
};
pub use types::{Algebra, AlgebraBuildError, BasisIdx};

#[cfg(test)]
#[path = "algebra_parts/tests.rs"]
mod tests;
