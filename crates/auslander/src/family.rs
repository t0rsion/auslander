//! Compiled fixed-pattern families of module arrow maps.
//!
//! A [`CompiledModuleFamily`] fixes one algebra, one dimension vector, and
//! one arrow-matrix layout. A specialization fills fixed and named parameter
//! coordinates and sets every other coordinate to zero. The compiled relation
//! plan checks each fiber before construction. Structural metadata does not
//! decide ranks, dimensions, or uniformity of fibers.

mod layout;
mod metadata;
mod specialize;
mod types;

pub use types::{
    CompiledModuleFamily, FamilyArrowLayout, FamilyCoordinate, FamilyCoordinateRange, FamilyError,
    FamilyFixedEntry, FamilyLayout, FamilyParameter, FamilyParameterPosition, HomCoefficientSide,
    HomEquationLayout, HomEquationTerm, HomVariable, RelationEvaluationLayout, RelationTermLayout,
};

#[cfg(test)]
mod tests;
