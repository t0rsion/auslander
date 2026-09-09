//! Morphisms of modules, the Hom functor, and kernels, images, and cokernels.
//!
//! A morphism `f: M → N` stores one `dim M_v × dim N_v` matrix per vertex.
//! A-linearity is the square `f_{s(a)} · N(a) = M(a) · f_{t(a)}` at every
//! arrow `a`. [`Morphism::new`] checks those squares. Endpoints compare by
//! [`crate::module::Module::ptr_eq`], never structurally.

mod core;
mod linear;
mod subquotient;

pub(crate) use core::matrix_is_zero;
pub use core::{HomError, Morphism, identity, zero_morphism};
pub(crate) use linear::{express_in_row_basis, hom_rows};
pub use linear::{hom, hom_dim};
pub use subquotient::{cokernel, image, kernel};
pub(crate) use subquotient::{
    factor_through_monomorphism, quotient_with_projection, submodule_with_inclusion,
};

#[cfg(test)]
mod tests;
