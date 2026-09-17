//! Shared Ext data and finite direct-sum coordinates over an exhaustive catalog.
//!
//! A [`CatalogAtlas`] fixes one [`IndecomposableCatalog`](crate::arquiver::IndecomposableCatalog) and one inclusive Ext
//! degree bound. It stores every ordered pair table and one source resolution
//! per catalog entry. Multiplicity enumeration uses the same entry order.
//! Atlas and multiplicity limits bound their named storage and search work.
//! These operations do not accept cooperative cancellation control.

mod core;
mod multiplicity;
mod scores;
mod types;

pub use core::CatalogAtlas;
pub use multiplicity::{
    MultiplicityComplete, MultiplicityCut, MultiplicityCutReason, MultiplicityOutcome,
};
pub use scores::AtlasScoreError;
pub use types::{
    AtlasMaterializeError, CatalogAtlasError, CatalogAtlasLimits, CatalogAtlasWork, CatalogExtRow,
    CatalogExtTable, MultiplicityError, MultiplicityLimits, MultiplicityVector,
};

#[cfg(test)]
mod tests;
