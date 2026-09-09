use std::sync::Arc;

use crate::algebra::Algebra;
use crate::field::{Fp, PrimeField};
use crate::hom::Morphism;
use crate::linalg::DenseMat;
use crate::module::same_representation;

use super::maps::{build_vertex_maps, projective_sum};
use super::types::{OppositeError, OppositeMap, reversed};

/// A map between finite direct sums of indecomposable projectives
/// `⊕_k P_{sources[k]} → ⊕_l P_{targets[l]}`, stored as an element matrix.
///
/// `Hom_A(e_i A, e_j A) ≅ e_j A e_i` by `f ↦ f(e_i)`, the inverse acting by
/// left multiplication. The map acts as `v_l = Σ_k x_{k,l}·u_k`, so the entry
/// at `(k, l)` lies in `e_{targets[l]} A e_{sources[k]}`. The entry is stored
/// as its coefficients on `paths_between(targets[l], sources[k])`, in that
/// order.
#[derive(Clone, Debug)]
pub struct ElementMatrix {
    algebra: Arc<Algebra>,
    sources: Vec<u32>,
    targets: Vec<u32>,
    entries: Vec<Vec<Vec<Fp>>>,
}

impl ElementMatrix {
    /// Builds an element matrix after checking summand vertices, entry shapes,
    /// and coefficient canonicity for the algebra's field.
    pub fn new(
        algebra: Arc<Algebra>,
        sources: Vec<u32>,
        targets: Vec<u32>,
        entries: Vec<Vec<Vec<Fp>>>,
    ) -> Result<ElementMatrix, OppositeError> {
        let field = algebra.field();
        validate_summands(&algebra, &sources, &targets)?;
        if entries.len() != sources.len() {
            return Err(OppositeError::RowCountMismatch {
                expected: sources.len(),
                got: entries.len(),
            });
        }
        for (row, row_entries) in entries.iter().enumerate() {
            if row_entries.len() != targets.len() {
                return Err(OppositeError::ColumnCountMismatch {
                    row,
                    expected: targets.len(),
                    got: row_entries.len(),
                });
            }
            for (col, coefficients) in row_entries.iter().enumerate() {
                let expected = algebra.paths_between(targets[col], sources[row]).len();
                if coefficients.len() != expected {
                    return Err(OppositeError::CoefficientCountMismatch {
                        row,
                        col,
                        expected,
                        got: coefficients.len(),
                    });
                }
                if let Some(index) = coefficients.iter().position(|c| c.raw() >= field.modulus()) {
                    return Err(OppositeError::NonCanonicalCoefficient { row, col, index });
                }
            }
        }
        Ok(ElementMatrix {
            algebra,
            sources,
            targets,
            entries,
        })
    }

    accessor_methods! {
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        pub field() -> PrimeField = |this| this.algebra.field();
        /// The source summand vertices, `k`-th summand `P_{sources()[k]}`.
        pub sources() -> &[u32] = |this| &this.sources;
        /// The target summand vertices, `l`-th summand `P_{targets()[l]}`.
        pub targets() -> &[u32] = |this| &this.targets;
        /// The coefficients of entry `(k, l)` on
        /// `paths_between(targets()[l], sources()[k])`.
        ///
        /// # Panics
        /// Panics unless `k` and `l` are in range.
        pub entry(k: usize, l: usize) -> &[Fp] = |this| &this.entries[k][l];
    }

    /// Reads the element matrix off a morphism between the standard direct sums
    /// `⊕_k P_{sources[k]} → ⊕_l P_{targets[l]}`. Entry `(k, l)` is the
    /// `l`-block of the image of summand `k`'s generator `e_{sources[k]}`. The
    /// standard sum is the layout of [`crate::module::direct_sum`] over
    /// [`crate::module::Module::projective`] summands. Both endpoints are checked against it
    /// entry for entry.
    pub fn of_morphism(
        f: &Morphism,
        sources: &[u32],
        targets: &[u32],
    ) -> Result<ElementMatrix, OppositeError> {
        let algebra = f.source().algebra().clone();
        validate_summands(&algebra, sources, targets)?;
        let num_vertices = algebra.quiver().num_vertices();
        if !same_representation(f.source(), &projective_sum(&algebra, sources)) {
            return Err(OppositeError::SourceNotTheDeclaredSum);
        }
        if !same_representation(f.target(), &projective_sum(&algebra, targets)) {
            return Err(OppositeError::TargetNotTheDeclaredSum);
        }
        let positions = algebra.component_positions();
        let mut row_offsets = vec![0usize; num_vertices as usize];
        let mut entries = Vec::with_capacity(sources.len());
        for &s in sources {
            let generator_row = row_offsets[s as usize] + positions[algebra.vertex_idempotent(s)];
            let row = f.map_at(s).row(generator_row);
            let mut row_entries = Vec::with_capacity(targets.len());
            let mut col = 0usize;
            for &t in targets {
                let width = algebra.paths_between(t, s).len();
                row_entries.push(row[col..col + width].to_vec());
                col += width;
            }
            entries.push(row_entries);
            for v in 0..num_vertices {
                row_offsets[v as usize] += algebra.paths_between(s, v).len();
            }
        }
        Ok(ElementMatrix {
            algebra,
            sources: sources.to_vec(),
            targets: targets.to_vec(),
            entries,
        })
    }

    /// The morphism the element matrix records, between freshly built standard
    /// sums `⊕_k P_{sources[k]} → ⊕_l P_{targets[l]}`.
    pub fn morphism(&self) -> Morphism {
        let source = projective_sum(&self.algebra, &self.sources);
        let target = projective_sum(&self.algebra, &self.targets);
        let maps = self.vertex_matrices();
        Morphism::new(&source, &target, maps)
            .expect("left multiplication by fixed algebra elements is A-linear")
    }

    /// One matrix per vertex `w`. The `(k, l)` block sends the basis word
    /// `u: sources[k] → w` to `Σ_r c_r (r·u)` over the coefficient words `r` of
    /// entry `(k, l)`, each product expanded to its normal form.
    fn vertex_matrices(&self) -> Vec<DenseMat> {
        let algebra = &self.algebra;
        let field = self.field();
        let positions = algebra.component_positions();
        build_vertex_maps(
            algebra,
            &self.sources,
            &self.targets,
            |s, w| algebra.paths_between(s, w).len(),
            |t, w| algebra.paths_between(t, w).len(),
            |w, k, s, l, t, row_offset, col_offset, mat| {
                for (ri, &r) in algebra.paths_between(t, s).iter().enumerate() {
                    let c = self.entries[k][l][ri];
                    if c.is_zero() {
                        continue;
                    }
                    for (ui, &u) in algebra.paths_between(s, w).iter().enumerate() {
                        for &(product, pc) in &algebra.mul_basis(r, u) {
                            let row = row_offset + ui;
                            let col = col_offset + positions[product];
                            let add = field.mul(c, pc);
                            mat.set(row, col, field.add(mat.get(row, col), add));
                        }
                    }
                }
            },
        )
    }

    /// The image of the matrix under `Hom_A(−, A)`: a map
    /// `⊕_l P^op_{targets[l]} → ⊕_k P^op_{sources[k]}` over the other side of
    /// `op`, with entry `(l, k)` the reversed element of entry `(k, l)`.
    /// `Hom_A(e_v A, A) ≅ A e_v = e_v A^op`, and precomposing left
    /// multiplication turns it into right multiplication. A reversed normal
    /// word need not be normal on the other side, so every reversed word is
    /// expanded to its normal form there. Applying `transpose_over` twice
    /// restores the matrix.
    pub fn transpose_over(&self, op: &OppositeMap) -> Result<ElementMatrix, OppositeError> {
        let to = op.other_side(&self.algebra)?.clone();
        let field = self.field();
        let positions = to.component_positions();
        let entries = self
            .targets
            .iter()
            .enumerate()
            .map(|(l, &t)| {
                self.sources
                    .iter()
                    .enumerate()
                    .map(|(k, &s)| {
                        let mut coefficients = vec![field.zero(); to.paths_between(s, t).len()];
                        for (ri, &r) in self.algebra.paths_between(t, s).iter().enumerate() {
                            let c = self.entries[k][l][ri];
                            if c.is_zero() {
                                continue;
                            }
                            let word = reversed(&self.algebra.basis()[r], to.quiver());
                            let normal = to
                                .nf_word(&word)
                                .expect("reversed words are paths of the opposite quiver");
                            for &(index, nc) in &normal {
                                let slot = &mut coefficients[positions[index]];
                                *slot = field.add(*slot, field.mul(c, nc));
                            }
                        }
                        coefficients
                    })
                    .collect()
            })
            .collect();
        Ok(ElementMatrix {
            algebra: to,
            sources: self.targets.clone(),
            targets: self.sources.clone(),
            entries,
        })
    }
}

fn validate_summands(
    algebra: &Algebra,
    sources: &[u32],
    targets: &[u32],
) -> Result<(), OppositeError> {
    let num_vertices = algebra.quiver().num_vertices();
    for &vertex in sources.iter().chain(targets) {
        if vertex >= num_vertices {
            return Err(OppositeError::SummandOutOfRange {
                vertex,
                num_vertices,
            });
        }
    }
    Ok(())
}
