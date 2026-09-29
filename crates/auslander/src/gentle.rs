//! Gentle presentations: recognition, threads, the Avella-Alaminos-Geiss
//! function, canonical keys, and checked string enumeration for trees.
//!
//! [`GentlePresentation`] recognizes a connected algebra whose reduced
//! relations form a gentle presentation. Cycles, loops, parallel arrows, and
//! full relation cycles are accepted. It computes the sign functions `σ` and
//! `ε`, the permitted and forbidden threads, the [`AagFunction`], the genus
//! of the surface model, the complete [`GentleDerivedInvariant`], and a
//! [`GentleKey`] up to isomorphism of bound quivers. [`connected_gentle_keys`]
//! lists one key per class for a given vertex count.
//!
//! A tree gentle algebra has no bands. The string classification therefore lists
//! every indecomposable module by one reduced string, up to reversing the string
//! and inverting every letter. The tree route runs general recognition and adds
//! the tree condition. Both read the reduced relations stored by
//! [`crate::algebra::Algebra`], so redundant or noncanonical input relations do
//! not affect the domain decision.

mod aag;
mod canonical;
mod classes;
mod enumerate;
mod errors;
mod invariant;
mod presentation;
mod shape;
mod surface;
mod threads;
mod validate;

pub use aag::AagFunction;
pub use canonical::{GentleKey, GentleLabeling};
pub use classes::{connected_gentle_algebras, connected_gentle_keys};
pub use enumerate::{GentleLetter, GentleString, gentle_tree_indecomposables, gentle_tree_strings};
pub use errors::GentleError;
pub use invariant::{GentleDerivedInvariant, WindingClass};
pub use presentation::GentlePresentation;
pub use shape::Sign;
pub use threads::GentleThread;

#[cfg(test)]
mod classes_tests;
#[cfg(test)]
mod discovery_tests;
#[cfg(test)]
mod invariant_tests;
#[cfg(test)]
mod presentation_tests;
#[cfg(test)]
mod tests;
