//! Acceptance tests for support tau-tilting pairs and graphs.
//!
//! Every number here is derived in the comment above the assertion. Three
//! derivations carry the rest:
//!
//! - Semisimple on `n` vertices has `2^n` pairs. Every module is semisimple
//!   and projective, so `tau = 0`, every subset of the simples is tau-rigid,
//!   and `|M| + |P| = n` forces `P` to be the complementary vertex set.
//! - Over a hereditary algebra of Dynkin type the pairs with `|M| = k` are the
//!   tilting modules of the full subquiver on a `k`-subset of the vertices.
//!   The number of tilting modules of type `T` is the positive Catalan number
//!   `prod_i (e_i + h - 1) / (e_i + 1)`, taken over the exponents `e_i` of `T`
//!   with `h` its Coxeter number. That count is 2 for `A_2`, 5 for `A_3`, and
//!   20 for `D_4`. Summing over subsets gives the histograms and the totals 5,
//!   14, and 50.
//! - On the two Nakayama fixtures the indecomposables and `tau` are short
//!   enough to list, so the pair sets are counted by hand in `catalog_fixtures`.
//!
//! The design puts the D_4 walk in the always-on block. It does not fit: a
//! D_4 walk and its closure recheck cost more over two fields than the rest
//! of the always-on block, and the recheck is the slower half. D_4 keeps its
//! always-on catalog route and moves its walk to `#[ignore]`, together with
//! the 16-vertex Kronecker walk. The heavy cases run under
//! `cargo test -- --ignored`.
//!
//! What "tampered" means here. Every witness type has private fields and no
//! public mutator, so an integration test cannot corrupt a stored witness. It
//! can only hand a checking constructor input that fails the condition, which
//! is what `the_checking_constructors_reject_input_that_fails_a_condition`
//! does. Field-level tampering is the in-module corpus of design section 15.

mod common;

#[path = "acceptance_tau/checks.rs"]
mod checks;
#[path = "acceptance_tau/fixtures.rs"]
mod fixtures;
#[path = "acceptance_tau/kronecker.rs"]
mod kronecker;
#[path = "acceptance_tau/pentagon.rs"]
mod pentagon;
#[path = "acceptance_tau/routes.rs"]
mod routes;
#[path = "acceptance_tau/witnesses.rs"]
mod witnesses;
