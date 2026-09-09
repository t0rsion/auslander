use std::sync::Arc;

use auslander::algebra::{Algebra, commutative_square};
use auslander::module::Module;

use super::common::f5;

pub(super) fn square() -> Arc<Algebra> {
    commutative_square(f5())
}

pub(super) fn dim_vecs(modules: &[Module]) -> Vec<Vec<usize>> {
    modules.iter().map(|m| m.dim_vector().to_vec()).collect()
}

pub(super) const SQUARE_CARTAN: [[usize; 4]; 4] =
    [[1, 1, 1, 1], [0, 1, 0, 1], [0, 0, 1, 1], [0, 0, 0, 1]];

pub(super) const PREPROJECTIVE_CARTAN: [[usize; 3]; 3] = [[1, 1, 1], [1, 2, 1], [1, 1, 1]];
