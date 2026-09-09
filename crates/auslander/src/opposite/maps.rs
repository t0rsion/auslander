use std::sync::Arc;

use crate::algebra::Algebra;
use crate::linalg::DenseMat;
use crate::module::{Module, summand_sum};

pub(super) fn build_vertex_maps<FR, FC, FB>(
    algebra: &Algebra,
    sources: &[u32],
    targets: &[u32],
    row_width: FR,
    col_width: FC,
    mut fill: FB,
) -> Vec<DenseMat>
where
    FR: Fn(u32, u32) -> usize,
    FC: Fn(u32, u32) -> usize,
    FB: FnMut(u32, usize, u32, usize, u32, usize, usize, &mut DenseMat),
{
    (0..algebra.quiver().num_vertices())
        .map(|w| {
            let rows = sources.iter().map(|&s| row_width(s, w)).sum();
            let cols = targets.iter().map(|&t| col_width(t, w)).sum();
            let mut matrix = DenseMat::zero(rows, cols);
            let mut row_offset = 0;
            for (k, &s) in sources.iter().enumerate() {
                let mut col_offset = 0;
                for (l, &t) in targets.iter().enumerate() {
                    fill(w, k, s, l, t, row_offset, col_offset, &mut matrix);
                    col_offset += col_width(t, w);
                }
                row_offset += row_width(s, w);
            }
            matrix
        })
        .collect()
}

pub(super) fn projective_sum(algebra: &Arc<Algebra>, vertices: &[u32]) -> Module {
    summand_sum(algebra, vertices, Module::projective)
}

pub(super) fn injective_sum(algebra: &Arc<Algebra>, vertices: &[u32]) -> Module {
    summand_sum(algebra, vertices, Module::injective)
}
