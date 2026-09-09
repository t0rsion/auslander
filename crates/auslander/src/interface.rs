//! Hom spaces from a checked separator equalizer.
//!
//! A partition has left and right interiors and a shared interface. No arrow
//! joins the two interiors, and no defining relation uses vertices from both.
//! Under these checked hypotheses, a global morphism is a pair of piece
//! morphisms whose vertex maps agree on the interface.
//!
//! [`InterfaceFamilyHomPlan`] specializes a [`crate::family::CompiledModuleFamily`]
//! when every parameter lies on an interface arrow. It eliminates outer-arrow
//! equations once and solves only interface equations for each fiber pair.

mod family;
mod hereditary;
mod hom;
mod partition;

pub use family::{
    InterfaceFamilyHom, InterfaceFamilyHomError, InterfaceFamilyHomPlan, InterfaceFamilyHomWork,
};
pub use hereditary::{
    InterfaceFamilyHereditaryError, InterfaceFamilyHereditaryPair, InterfaceFamilyHereditaryPlan,
    InterfaceFamilyHereditaryWork,
};
pub use hom::{InterfaceHom, InterfaceHomPlan, InterfaceHomWork};
pub use partition::{InterfaceHomError, InterfacePartition, InterfaceRegion};

#[cfg(test)]
mod tests;
