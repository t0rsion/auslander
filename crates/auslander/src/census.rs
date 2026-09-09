//! Certified finite-field module censuses for one dimension vector.
//!
//! [`Census`] visits every arrow-matrix tuple in a checked prime field, in a
//! arrow-id order and row-major order within each matrix. It keeps one
//! representative of each class decided by [`crate::iso::is_isomorphic`].
//! The raw search space is exponential:
//! for a dimension vector `d`, it has `p^N` tuples where
//! `N = Σ_a d[source(a)] d[target(a)]`. A complete result is available only
//! when that finite search finishes and every comparison is certified.

include!("census/domain.rs");
include!("census/records.rs");
include!("census/request.rs");
include!("census/engine.rs");
include!("census/portable_parser.rs");
include!("census/portable.rs");
include!("census/portable_verify.rs");
include!("census/tests.rs");
