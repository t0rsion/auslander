//! Checked bounded projective complexes and quasi-isomorphisms.
//!
//! A projective term carries a split into canonical projectives. A
//! quasi-isomorphism carries the exact mapping cone that proves its claim.

mod budget;
mod cover;
mod quasi;
mod replacement;
mod resolution;
mod term;
mod totalization;
mod work;

pub use budget::{
    ReplacementCancellation, ReplacementCompletedStage, ReplacementCut, ReplacementCutStage,
    ReplacementLimits, ReplacementOutcome, ReplacementReservation, ReplacementResource,
    ReplacementWork,
};
pub use cover::{ComplexProjectiveCover, ComplexProjectiveCoverError, projective_complex_cover};
pub use quasi::{QuasiIsomorphism, QuasiIsomorphismError};
pub use replacement::{PerfectReplacement, PerfectReplacementError, ReplacementError};
pub use resolution::replace_perfect;
pub use term::{
    ProjectiveComplex, ProjectiveComplexError, ProjectiveTermError, ProjectiveTermWitness,
};
