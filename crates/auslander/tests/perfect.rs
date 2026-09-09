//! Acceptance tests for checked projective complexes and quasi-isomorphisms.

mod common;

use common::f5;

#[path = "perfect/cover.rs"]
mod cover;
#[path = "perfect/quasi.rs"]
mod quasi;
#[path = "perfect/replacement.rs"]
mod replacement;
#[path = "perfect/terms.rs"]
mod terms;
