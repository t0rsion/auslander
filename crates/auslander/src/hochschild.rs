//! Relative normalized bar Hochschild cohomology with typed resource cuts.
//!
//! The complex uses `S = product_v F_p e_v` and `J = rad A`. For a bound
//! quiver algebra, `S` is separable and the nontrivial normal words form a
//! basis of `J`, so this computes ordinary Hochschild cohomology. Degree `n`
//! inputs are composable `n`-tuples of nontrivial normal words. The tuples are
//! streamed in lexicographic basis-index order. Only coordinate ranks and
//! output indices remain in a completed result.
//!
//! [`BarLimits`] has four independent ceilings: tensor tuples per degree,
//! cochain dimension per degree, retained matrix entries plus live scratch,
//! and work units across the request. A cut keeps only degrees that finished
//! before the rejected reservation.

#[path = "hochschild/bar.rs"]
mod bar;
#[path = "hochschild/cochain.rs"]
mod cochain;
#[path = "hochschild/limits.rs"]
mod limits;
#[path = "hochschild/outcome.rs"]
mod outcome;
#[path = "hochschild/verification.rs"]
mod verification;

pub use bar::bar_hochschild;
pub use limits::*;
pub use outcome::*;

#[cfg(test)]
#[path = "hochschild/tests.rs"]
mod tests;
