//! Bounded homological complexes and their homotopy category.
//!
//! A [`BoundedComplex`] stores terms in increasing homological degree. Its
//! differential at degree `n` has type `C_n -> C_(n - 1)`. A [`ChainMap`]
//! stores one module morphism in every degree and preserves this differential.
//! The shift is `(C[s])_n = C_(n - s)`, with differential multiplied by
//! `(-1)^s`. The mapping cone uses `Cone(f)_n = Y_n (+) X_(n - 1)` and
//! differential `[d_Y, f; 0, -d_X]`.

mod chain;
mod complex;
mod cone;
mod hom;

pub use chain::{ChainHomotopy, ChainMap, ChainMapError};
pub use complex::{
    BoundedComplex, BoundedComplexError, DegreeRange, DegreeRangeError, direct_sum_complexes,
};
pub use hom::{
    ChainHomQuotient, ChainHomSpace, DegreeComplex, Homotopy, HomotopyHom, HomotopyHomQuotient,
};

#[cfg(test)]
mod tests;
