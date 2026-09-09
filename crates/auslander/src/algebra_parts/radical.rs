use crate::field::Fp;
use crate::linalg::DenseMat;

use super::types::{Algebra, AlgebraBuildError};

impl Algebra {
    /// The chain `J^0 ⊇ J^1 ⊇ ... ⊇ J^d = 0`, entry `k` holding `J^k`, or a
    /// rejection when no `d` with `J^d = 0` exists.
    ///
    /// The chain is descending, so within `dim` steps it either reaches zero
    /// or repeats a nonzero dimension. A repeat means `J^k = J^{k+1}`, hence
    /// `J^k = J^m` for every `m >= k`, so `J` is not nilpotent and the ideal
    /// is not admissible. Multiplication tables are the only input. Leading
    /// words alone cannot decide this: `(x³)` and `(x³ - x²)` share every
    /// leading word, and only the first is admissible.
    pub(super) fn radical_chain(&self) -> Result<Vec<Vec<Vec<DenseMat>>>, AlgebraBuildError> {
        let total =
            |power: &[Vec<DenseMat>]| -> usize { power.iter().flatten().map(DenseMat::rows).sum() };
        let n = self.quiver.num_vertices() as usize;
        // J^0 is A itself, and paths_between(u, v) is a basis of e_u A e_v,
        // so the component of J^0 at (u, v) is the identity.
        let identity: Vec<Vec<DenseMat>> = (0..n)
            .map(|u| {
                (0..n)
                    .map(|v| DenseMat::identity(self.between[u][v].len()))
                    .collect()
            })
            .collect();
        let mut chain = vec![identity];
        for _ in 0..=self.dim() {
            let dimension = total(chain.last().expect("the chain starts at J^0"));
            if dimension == 0 {
                return Ok(chain);
            }
            let next = self.radical_step(chain.last().expect("the chain starts at J^0"));
            let next_dimension = total(&next);
            debug_assert!(next_dimension <= dimension, "J^{{k+1}} is contained in J^k");
            if next_dimension == dimension {
                return Err(AlgebraBuildError::NonAdmissible {
                    stable_power: chain.len() - 1,
                    dimension,
                });
            }
            chain.push(next);
        }
        unreachable!("a strictly descending chain of subspaces of A reaches zero within dim steps")
    }

    /// The stored component of `e_u · J^k · e_v`, one spanning vector per
    /// row, in the coordinates of [`Self::paths_between`]`(u, v)`. `J^0` is
    /// the algebra itself, so `k = 0` gives the identity. Panics if either
    /// vertex is out of range.
    ///
    /// Row-space iteration computes `J^k`: `J^1` is the span of the
    /// non-trivial basis words and `J^{k+1}` is the span of `x·a` over `x`
    /// spanning `J^k` and arrows `a`. Word length does not decide radical
    /// depth: an inhomogeneous relation can place a short normal word inside
    /// a deep radical power. The iteration runs at construction; this method
    /// indexes the stored matrix.
    pub fn radical_power_matrix(&self, u: u32, v: u32, k: usize) -> &DenseMat {
        assert!(u < self.quiver.num_vertices() && v < self.quiver.num_vertices());
        &self.radical_power(k)[u as usize][v as usize]
    }

    accessor_methods! {
        /// The least `k` with `J^k = 0`, read off the stored chain. Finite for
        /// every constructed algebra: an `Algebra` exists only when its arrow
        /// ideal `J` is nilpotent. The Jacobson radical of a finite-dimensional
        /// algebra is always nilpotent, but `J` is the arrow ideal. A quotient
        /// can be finite dimensional with `J` not nilpotent.
        pub nilpotency_degree() -> usize = |this| this.radical_powers.len() - 1;
    }

    /// Row-reduced component matrices of `J^k`, indexed `[u][v]` with columns
    /// over `paths_between(u, v)`.
    ///
    /// The stored chain stops at `J^d = 0`, and `J^k = 0` for every `k >= d`,
    /// so an index past the end reads the last entry.
    fn radical_power(&self, k: usize) -> &[Vec<DenseMat>] {
        &self.radical_powers[k.min(self.nilpotency_degree())]
    }

    /// `J^{k+1}` from `J^k`: right-multiply every spanning row by every
    /// arrow and row-reduce each component. For `J^0` (identity components)
    /// this yields `J^1`, the span of the non-trivial basis words, because
    /// every non-trivial normal word is a normal word times its last arrow.
    fn radical_step(&self, power: &[Vec<DenseMat>]) -> Vec<Vec<DenseMat>> {
        let n = self.quiver.num_vertices() as usize;
        let positions = self.component_positions();
        let mut rows: Vec<Vec<Vec<Vec<Fp>>>> = vec![vec![Vec::new(); n]; n];
        for u in 0..n {
            for (w, component) in power[u].iter().enumerate() {
                let word_indices = &self.between[u][w];
                for r in 0..component.rows() {
                    let row = component.row(r);
                    for &a in self.quiver.arrows_from(w as u32) {
                        let v = self.quiver.target(a) as usize;
                        let mut image = vec![self.field.zero(); self.between[u][v].len()];
                        for (pos, &c) in row.iter().enumerate() {
                            if c.is_zero() {
                                continue;
                            }
                            for &(q, qc) in self.right_mul(word_indices[pos], a) {
                                image[positions[q]] =
                                    self.field.add(image[positions[q]], self.field.mul(c, qc));
                            }
                        }
                        if image.iter().any(|c| !c.is_zero()) {
                            rows[u][v].push(image);
                        }
                    }
                }
            }
        }
        (0..n)
            .map(|u| {
                (0..n)
                    .map(|v| {
                        let cols = self.between[u][v].len();
                        DenseMat::from_rows_with_cols(&rows[u][v], cols)
                            .into_row_space_basis(&self.field)
                    })
                    .collect()
            })
            .collect()
    }

    /// Position of each basis word within `paths_between` of its own
    /// endpoints.
    pub(crate) fn component_positions(&self) -> Vec<usize> {
        let mut positions = vec![usize::MAX; self.basis.len()];
        for row in &self.between {
            for component in row {
                for (i, &b) in component.iter().enumerate() {
                    positions[b] = i;
                }
            }
        }
        positions
    }
}
