//! Opposite algebras, the k-dual functor `D`, and the Nakayama functor `ν` on
//! maps between projectives.
//!
//! The opposite of `kQ/I` is `kQ^op/I^op`: same vertices, arrow `a: i → j`
//! reversed to the same-id arrow `j → i`, and every relation word reversed.
//! [`opposite`] runs the full completion and verification pipeline on the
//! reversed relations. Reversing the reduced Groebner basis of `I` gives a
//! generating set of `I^op`, not necessarily its reduced Groebner basis;
//! completion recompletes it. Both sides have the same dimension. `D` sends
//! an `A`-module to an `A^op`-module on the dual spaces: same dimension
//! vector, `DM(a^op) = M(a)ᵀ`. Applied twice through one [`OppositeMap`],
//! `D` restores the original module entry for entry.

mod construction;
mod dual;
mod element_matrix;
mod maps;
mod nakayama;
mod types;

pub use construction::opposite;
pub use dual::{dual, dual_morphism};
pub use element_matrix::ElementMatrix;
pub use nakayama::nu_of_presentation_map;
pub use types::{OppositeError, OppositeMap};

#[cfg(test)]
mod tests;
