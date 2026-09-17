//! Checked string enumeration for gentle algebras whose underlying graph is a tree.
//!
//! A tree gentle algebra has no bands. The string classification therefore lists
//! every indecomposable module by one reduced string, up to reversing the string
//! and inverting every letter. The validator reads the reduced relations stored
//! by [`crate::algebra::Algebra`], so redundant or noncanonical input relations do
//! not affect the domain decision.

mod enumerate;
mod errors;
mod validate;

pub use enumerate::{GentleLetter, GentleString, gentle_tree_indecomposables, gentle_tree_strings};
pub use errors::GentleError;

#[cfg(test)]
mod tests;
