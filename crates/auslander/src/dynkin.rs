//! Dynkin and Euclidean diagrams of a quiver's underlying graph, their root
//! systems, and the indecomposables of a hereditary path algebra of Dynkin
//! type.
//!
//! Recognition matches the underlying graph against the shape of each diagram
//! (Bourbaki, *Groupes et algèbres de Lie*, planches I-IX, and the affine
//! tables of Kac, *Infinite dimensional Lie algebras*, ch. 4). Every decision
//! and every root is an integer computation.
//!
//! Only simply laced diagrams occur: the underlying graph of a quiver has
//! unoriented edges of one length, and a multiple edge is recorded as a
//! multiplicity in the generalized Cartan matrix.

mod constructors;
mod errors;
mod graph;
mod indecomposables;
mod roots;
mod types;

pub use constructors::{dynkin_quiver, euclidean_quiver};
pub use errors::DynkinError;
pub use graph::{dynkin_type, euclidean_type};
pub use indecomposables::dynkin_indecomposables;
pub use roots::{generalized_cartan_matrix, positive_roots};
pub use types::{DynkinType, EuclideanType};

pub(crate) use graph::reachable_count;

#[cfg(test)]
mod tests;
