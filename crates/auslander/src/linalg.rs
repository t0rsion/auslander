//! Exact linear algebra over F_p.
//!
//! Two matrix types share one set of operations: [`crate::linalg::DenseMat`] (row-major
//! contiguous) and [`SparseMat`] (sorted rows, Markowitz-pivoted
//! elimination). Matrices are plain data and do not store their field. Every
//! arithmetic operation takes the [`crate::field::PrimeField`] as an argument. All entries
//! of the operands must belong to that field.
//!
//! Direct callers must supply canonical matrices: every entry is the reduced
//! representative for the field passed, as produced by [`crate::field::PrimeField::elem`].
//! The field arithmetic debug-asserts this and does not re-reduce.
//!
//! Basis-returning operations (`kernel_basis`, `left_kernel_basis`,
//! `row_space_basis`, `image_basis`) return a matrix whose rows are the basis
//! vectors, derived from the reduced row echelon form. The reduced form is
//! unique, so these operations are deterministic. The dense and sparse paths
//! return identical rows in identical order. Callers above this module depend
//! on the exact rows and their order, so both are part of the contract.
//!
//! Every reduction has two forms. `rref`, `rank`, `kernel_basis`, and
//! `row_space_basis` take the matrix by reference and reduce a copy. The
//! matching `into_rref`, `into_rank`, `into_kernel_basis`, and
//! `into_row_space_basis` take the matrix by value and reduce it in place.
//! Both forms return the same thing. The consuming form is crate-private.

mod dense;
mod reducer;
mod sparse;
mod terms;

pub use dense::DenseMat;
pub use reducer::RowReducer;
pub use sparse::{SparseMat, SparseRow};
pub(crate) use terms::merge_scaled_terms;

#[cfg(test)]
mod tests;
