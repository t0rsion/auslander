//! The endomorphism algebra End(M) as a finite-dimensional algebra over F_p.
//!
//! Elements are coordinate vectors in the [`crate::homspace::HomSpace`] basis
//! of `Hom(M, M)`, read off the flattened vertex matrices of a morphism.
//! Multiplication goes through structure constants, each of them the composite
//! of two basis elements re-expressed in the basis. The table of constants is
//! built by the first [`EndoAlgebra::multiply`]: the radical, the semisimple
//! quotient, and locality read none of it.
//!
//! The Jacobson radical is exact in every characteristic. The Friedl-Rónyai chain
//! (Rónyai, "Computing the structure of finite algebras", J. Symbolic Comput. 9
//! (1990)) refines the trace-form kernel with the characteristic polynomial
//! coefficients `c_{p^i}`, which stay F_p-linear on each ideal of the chain. The
//! trace form alone is not enough in small characteristic, so the chain is run to
//! the end rather than trusted after its first step.

mod core;
mod helpers;
mod polynomial;
mod radical;

pub use core::EndoAlgebra;
pub(crate) use helpers::SplitMix64;

#[cfg(test)]
mod tests;
