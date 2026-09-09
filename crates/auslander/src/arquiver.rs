//! The category radical of certified indecomposables, exhaustive
//! indecomposable catalogs, and the valued Auslander-Reiten quiver.
//!
//! For certified indecomposables `X` and `Y`, the radical of the module
//! category is exact and needs no catalog. Two cases:
//!
//! - `X` and `Y` are not isomorphic. Then no map `X -> Y` is invertible, so
//!   `rad(X, Y) = Hom(X, Y)`.
//! - `X` and `Y` are isomorphic. Fix one isomorphism `u: Y -> X`. Then
//!   `rad(X, Y) = { f : f.then(u) in rad End(X) }`. The condition is linear
//!   in `f`, so the result is a [`crate::homspace::HomSubspace`]. The subspace does not depend
//!   on the choice of `u`: a second isomorphism is `u.then(a)` for an
//!   automorphism `a` of `X`, and `rad End(X)` is a two-sided ideal, so
//!   `f.then(u).then(a)` lies in the radical exactly when `f.then(u)` does.
//!
//! The square of the radical needs a catalog. Through a list `C` of
//! indecomposables,
//!
//! ```text
//! rad2(X, Y) = sum over Z in C of span{ f.then(g) :
//!     f in basis rad(X, Z), g in basis rad(Z, Y) }
//! ```
//!
//! The sum runs over `C` in catalog order. The result is a span, so the
//! order does not change it.
//!
//! Lemma: when `C` is exhaustive, this is the true `rad^2(X, Y)`. Any element
//! of `rad^2(X, Y)` factors as `X -> M -> Y` through some module `M` with both
//! legs in the radical. Krull-Schmidt splits `M` into indecomposables, each
//! isomorphic to a catalog member, and the radical is an ideal, so every
//! component of the factorization stays a radical map. With less than an
//! exhaustive catalog the same sum is only a subspace of `rad^2`. The API
//! keeps the two apart by construction: [`radical_square_through_catalog`]
//! and everything built on it take an [`IndecomposableCatalog`], and a
//! catalog is built only from a complete enumeration.
//!
//! `Irr(X, Y) = rad(X, Y) / rad^2(X, Y)` is [`irreducible_quotient`]. Its
//! nonzero elements are the classes of the irreducible maps `X -> Y`. Its
//! dimension is the base dimension of the arrow `X -> Y` of the AR quiver,
//! and the arrow exists exactly when that dimension is positive.
//!
//! `Irr(X, Y)` is a vector space over the residue field of `End(X)` and over
//! the residue field of `End(Y)`, so both residue degrees divide the base
//! dimension, and [`ArArrow`] stores the two quotients. When both residue
//! degrees are 1 the three numbers agree, the base dimension says everything
//! about the arrow, and [`ArArrow::valuation`] reports
//! [`ArrowValuation::Plain`]. When a residue degree `d` exceeds 1, the base
//! dimension counts `d` prime-field dimensions per dimension over that residue
//! field, so no single integer is the multiplicity of the arrow. In that case
//! `valuation` reports [`ArrowValuation::Valued`] with all three numbers. The
//! crate offers no bare multiplicity accessor, so no caller can read one
//! number where two are needed.

mod catalog;
mod errors;
mod quiver;
mod radical;

pub use catalog::{CatalogProvenance, IndecomposableCatalog};
pub use errors::ArQuiverError;
pub use quiver::{ArArrow, ArQuiver, ArVertex, ArrowValuation, ar_quiver};
pub use radical::{category_radical, irreducible_quotient, radical_square_through_catalog};

#[cfg(test)]
mod tests;
