//! Bounded self-Ext algebras with deterministic bases and Yoneda tensors.
//!
//! [`ExtAlgebraOutcome::compute`] computes `Ext^d(M, M)` for every `d` through a caller
//! bound. It returns [`ExtAlgebraOutcome::Complete`] when the minimal
//! resolution of `M` ends within that bound. Otherwise it returns
//! [`ExtAlgebraOutcome::Cut`], which proves the next syzygy is nonzero.
//! Every stored grade and product tensor remains exact in either outcome.
//!
//! Products follow the right-module convention of [`crate::ext::ExtClass::then`]: an
//! entry in degree `(m, n)` is `Ext^m(M, M) x Ext^n(M, M) -> Ext^{m+n}(M, M)`.
//! The left factor acts first.

mod algebra;
mod errors;
mod product;
mod tensor;
mod verify;

pub use algebra::{ExtAlgebra, ExtAlgebraCut, ExtAlgebraOutcome};
pub use errors::{ExtAlgebraError, ExtAlgebraProductError};
pub use tensor::{MultiplicationTensor, ProductRecord};

#[cfg(test)]
mod tests;
