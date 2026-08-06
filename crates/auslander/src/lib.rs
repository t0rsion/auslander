//! Finite-dimensional basic algebras kQ/I over a checked prime field, and their
//! finite-dimensional right modules. I is an admissible ideal presented by
//! uniform relations; every algebra is built through completion into a reduced
//! Groebner basis and independent verification of the emitted certificate.

pub mod algebra;
pub mod ar;
pub mod certificate;
pub mod completion;
pub mod decompose;
pub mod dynkin;
pub mod endo;
pub mod enumerate;
pub mod ext;
pub mod field;
pub mod hom;
pub mod injective;
pub mod iso;
pub mod linalg;
pub mod module;
pub mod opposite;
pub mod order;
pub mod quiver;
pub mod radical;
pub mod relation;
pub mod resolution;
pub mod verify;
