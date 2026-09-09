//! `Hom_A(M, N)` as an explicit vector space: fixed basis, flat coordinates,
//! subspaces, and deterministic quotients.
//!
//! A [`HomSpace`] stores the `hom_rows` rows in the order `hom_rows` fixes:
//! kernel variables vertex-major, then row-major inside a vertex, and one
//! basis vector per free column in increasing column order. Row `i` is basis
//! morphism `i`. A [`HomSubspace`] stores the reduced row echelon form of its
//! spanning set in these coordinates, so two subspaces of compatible spaces
//! are equal exactly when their matrices are equal.
//!
//! The complement rule is fixed crate-wide: to complement a subspace `B`
//! inside an ambient subspace `Z`, scan the RREF basis rows of `Z` in order
//! and keep each row that increases the rank of `B` plus the rows kept so
//! far. [`HomQuotient`] representatives are combinations of the kept rows, so
//! rebuilding a quotient from the same modules gives the same representatives.
//! The AR quiver reads irreducible-map classes off those representatives.
//! `tests/determinism_ar.rs` compares the resulting renderings byte for byte.
//!
//! Two spaces are compatible when their sources are [`crate::module::Module::ptr_eq`] and
//! their targets are [`crate::module::Module::ptr_eq`]. Compatible spaces rebuilt from the
//! same modules have identical bases, and coordinates transport verbatim.

use std::sync::OnceLock;

use crate::hom::Morphism;
use crate::linalg::DenseMat;
use crate::module::Module;

mod core;
mod quotient;
mod space;
mod subspace;

pub(crate) use core::{
    deterministic_complement, flat_row, row_times, rref_coords, rref_coords_many, scale_morphism,
    stack_rows,
};

/// Rejected Hom space input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HomSpaceError {
    /// The morphism's source is not this space's source module (by
    /// [`crate::module::Module::ptr_eq`]).
    SourceMismatch,
    /// The morphism's target is not this space's target module (by
    /// [`crate::module::Module::ptr_eq`]).
    TargetMismatch,
    /// The two subspaces do not share both endpoint modules (by
    /// [`crate::module::Module::ptr_eq`]).
    IncompatibleSubspaces,
    /// The claimed inner subspace has a basis row outside the ambient
    /// subspace.
    NotContained,
    /// The morphism lies outside the ambient subspace of the quotient.
    OutsideSubspace,
}

display_error! { error HomSpaceError {
    Self::SourceMismatch => "the morphism's source is not the space's source";
    Self::TargetMismatch => "the morphism's target is not the space's target";
    Self::IncompatibleSubspaces => "the subspaces do not share both endpoint modules";
    Self::NotContained => "the inner subspace is not contained in the ambient subspace";
    Self::OutsideSubspace => "the morphism lies outside the ambient subspace of the quotient";
} }

/// `Hom_A(M, N)` as its flat rows, in the order `hom_rows` fixes.
///
/// Row `i` is basis element `i` flattened. [`HomSpace::basis_morphism`]
/// unflattens one row, [`HomSpace::basis_iter`] unflattens as the caller
/// consumes, and [`HomSpace::basis`] unflattens all of them once and keeps
/// them.
///
/// Fields are private. Construction goes through [`HomSpace::new`], so the
/// rows are always the `hom_rows` rows of the stored endpoints.
#[derive(Clone, Debug)]
pub struct HomSpace {
    source: Module,
    target: Module,
    // One row per basis element, flattened as in `flat_row`.
    flat: DenseMat,
    basis: OnceLock<Vec<Morphism>>,
}

/// A subspace of a Hom space, stored as the RREF of its spanning set in flat
/// coordinates.
///
/// Fields are private; construction goes through [`HomSpace::subspace`] or
/// [`HomSpace::full_subspace`], so the stored matrix is always the RREF.
#[derive(Clone, Debug)]
pub struct HomSubspace {
    source: Module,
    target: Module,
    // One basis vector per row, in reduced row echelon form.
    basis: DenseMat,
}

/// A quotient of Hom subspaces with deterministic representatives: the
/// denominator subspace plus the complement rows kept by the crate-wide rule.
///
/// Fields are private; construction goes through [`HomSubspace::quotient_by`].
#[derive(Clone, Debug)]
pub struct HomQuotient {
    subspace: HomSubspace,
    // Rows of the ambient RREF kept by the complement rule, in scan order.
    complement: DenseMat,
}

#[cfg(test)]
mod tests;
