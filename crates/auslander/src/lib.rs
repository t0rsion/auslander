//! Finite-dimensional basic algebras `kQ/I` over a checked prime field, and
//! their finite-dimensional right modules.
//!
//! `I` is an admissible ideal presented by uniform relations, each one a
//! k-linear combination of parallel paths. Every algebra comes from one
//! pipeline: completion rewrites the relations into a reduced Groebner basis
//! and emits a certificate, and an independent verifier checks that
//! certificate before the algebra is built.
//!
//! Two conventions are fixed crate-wide. Modules are right modules, written
//! with row vectors. Paths compose left to right: `a·b` means first `a`, then
//! `b`, and `M(a·b) = M(a) M(b)`.
//!
//! Partiality is typed. A dimension known only from below comes back as
//! `Bounded::AtLeast`, and a resolution prefix that runs out of budget ends in
//! `ResolutionEnd::Cut` with the next syzygy known to be nonzero. Nothing
//! truncates silently.

pub mod algebra;
pub mod almost_split;
pub mod approx;
pub mod ar;
pub mod arquiver;
pub mod basic;
pub mod certificate;
pub mod completion;
pub mod decompose;
pub mod dynkin;
pub mod endo;
pub mod enumerate;
pub mod ext;
pub mod field;
pub mod hom;
pub mod homspace;
pub mod indec;
pub mod injective;
pub mod iso;
pub mod linalg;
pub mod module;
pub mod monomial;
pub mod mutation;
pub mod opposite;
pub mod order;
pub mod profile;
pub mod quiver;
pub mod radical;
pub mod relation;
pub mod resolution;
pub mod sequence;
pub mod supporttau;
pub mod taugraph;
pub mod taurigid;
pub mod verify;
