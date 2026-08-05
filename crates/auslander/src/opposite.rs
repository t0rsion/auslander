//! Opposite algebras, the k-dual functor `D`, and the Nakayama functor `ν` on
//! maps between projectives.
//!
//! The opposite of the monomial algebra `kQ/I` is `kQ^op/I^op`: same vertices,
//! arrow `a: i → j` reversed to the same-id arrow `j → i`, and every word
//! `a_1 ⋯ a_k` (in particular every forbidden word) reversed to `a_k ⋯ a_1`.
//! Reversal is a bijection between the standard paths of the two sides, so both
//! algebras have the same dimension. `D` sends a right `A`-module to a right
//! `A^op`-module on the dual spaces: same dimension vector,
//! `DM(a^op) = M(a)ᵀ`. Applied twice through one [`OppositeMap`], `D` restores
//! the original module entry for entry.

use std::fmt;
use std::sync::Arc;

use crate::algebra::{BasisIdx, MonomialAlgebra};
use crate::field::{Fp, PrimeField};
use crate::hom::Morphism;
use crate::linalg::DenseMat;
use crate::module::{Module, direct_sum};
use crate::quiver::{ArrowId, PathWord, Quiver, QuiverError};

/// Rejected duality or element-matrix input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OppositeError {
    /// The value lives over an algebra that is neither side of the [`OppositeMap`].
    AlgebraOutsidePair,
    /// `dual_of_target` is not entrywise the dual of the morphism's target.
    NotDualOfTarget,
    /// `dual_of_source` is not entrywise the dual of the morphism's source.
    NotDualOfSource,
    /// A summand vertex outside `0..num_vertices`.
    SummandOutOfRange { vertex: u32, num_vertices: u32 },
    /// `entries` needs one row per source summand.
    RowCountMismatch { expected: usize, got: usize },
    /// Row `row` of `entries` needs one entry per target summand.
    ColumnCountMismatch {
        row: usize,
        expected: usize,
        got: usize,
    },
    /// Entry `(row, col)` needs one coefficient per standard path from
    /// `targets[col]` to `sources[row]`.
    CoefficientCountMismatch {
        row: usize,
        col: usize,
        expected: usize,
        got: usize,
    },
    /// Entry `(row, col)` holds a coefficient at `index` whose representative is
    /// not canonical for the declared field.
    NonCanonicalCoefficient {
        row: usize,
        col: usize,
        index: usize,
    },
    /// The morphism's source is not entrywise the standard direct sum of the
    /// declared source summands.
    SourceNotTheDeclaredSum,
    /// As [`Self::SourceNotTheDeclaredSum`], for the target.
    TargetNotTheDeclaredSum,
}

impl fmt::Display for OppositeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AlgebraOutsidePair => {
                f.write_str("the algebra is neither side of the opposite pair")
            }
            Self::NotDualOfTarget => {
                f.write_str("dual_of_target is not the entrywise dual of the morphism's target")
            }
            Self::NotDualOfSource => {
                f.write_str("dual_of_source is not the entrywise dual of the morphism's source")
            }
            Self::SummandOutOfRange {
                vertex,
                num_vertices,
            } => write!(f, "summand vertex {vertex} outside 0..{num_vertices}"),
            Self::RowCountMismatch { expected, got } => {
                write!(f, "entries has {got} rows, sources has {expected} summands")
            }
            Self::ColumnCountMismatch { row, expected, got } => write!(
                f,
                "entries row {row} has {got} columns, targets has {expected} summands"
            ),
            Self::CoefficientCountMismatch {
                row,
                col,
                expected,
                got,
            } => write!(
                f,
                "entry ({row}, {col}) has {got} coefficients, its path component has {expected}"
            ),
            Self::NonCanonicalCoefficient { row, col, index } => write!(
                f,
                "entry ({row}, {col}) has a non-canonical coefficient at index {index} for the declared field"
            ),
            Self::SourceNotTheDeclaredSum => f.write_str(
                "the morphism's source is not the standard direct sum of the declared source summands",
            ),
            Self::TargetNotTheDeclaredSum => f.write_str(
                "the morphism's target is not the standard direct sum of the declared target summands",
            ),
        }
    }
}

impl std::error::Error for OppositeError {}

/// An algebra paired with its opposite, carrying the arrow and word
/// correspondence in both directions.
///
/// Arrow ids are shared: arrow `a: i → j` of one side corresponds to the arrow
/// with the same id running `j → i` on the other, and a path word corresponds
/// to its reversal.
#[derive(Clone, Debug)]
pub struct OppositeMap {
    algebra: Arc<MonomialAlgebra>,
    opposite: Arc<MonomialAlgebra>,
}

/// The opposite algebra of `algebra` with its arrow/word correspondence: same
/// vertices, arrows reversed keeping their ids, forbidden words reversed.
///
/// ```
/// use auslander::algebra::an_with_relations;
/// use auslander::opposite::opposite;
/// let a = an_with_relations(3, &[(0, 2)]).unwrap();
/// let op = opposite(&a);
/// assert_eq!(op.opposite().dim(), a.dim());
/// ```
pub fn opposite(algebra: &Arc<MonomialAlgebra>) -> OppositeMap {
    let quiver = algebra.quiver();
    let arrows: Vec<(u32, u32)> = quiver.arrows().iter().map(|&(s, t)| (t, s)).collect();
    let reversed_quiver = Quiver::new(quiver.num_vertices(), &arrows)
        .expect("reversing endpoints keeps them in range");
    let forbidden = algebra
        .forbidden()
        .iter()
        .map(|word| word.iter().rev().copied().collect())
        .collect();
    let opposite = MonomialAlgebra::new(reversed_quiver, forbidden)
        .expect("reversal bijects standard paths, so the opposite stays finite-dimensional");
    OppositeMap {
        algebra: algebra.clone(),
        opposite,
    }
}

impl OppositeMap {
    /// The original algebra.
    #[inline]
    pub fn algebra(&self) -> &Arc<MonomialAlgebra> {
        &self.algebra
    }

    /// The opposite algebra.
    #[inline]
    pub fn opposite(&self) -> &Arc<MonomialAlgebra> {
        &self.opposite
    }

    /// The opposite-side arrow of `a`: the same id, endpoints swapped.
    /// Panics if `a` is not an arrow of the algebra's quiver.
    #[inline]
    pub fn arrow_to_op(&self, a: ArrowId) -> ArrowId {
        assert!(
            a.index() < self.algebra.quiver().num_arrows(),
            "arrow_to_op: arrow id {} out of range",
            a.0
        );
        a
    }

    /// The algebra-side arrow of an opposite arrow, as [`Self::arrow_to_op`].
    #[inline]
    pub fn arrow_from_op(&self, a: ArrowId) -> ArrowId {
        assert!(
            a.index() < self.opposite.quiver().num_arrows(),
            "arrow_from_op: arrow id {} out of range",
            a.0
        );
        a
    }

    /// The reversal of a path word of the algebra as a word of the opposite.
    /// Errors when `word` is not a path of the algebra's quiver.
    pub fn word_to_op(&self, word: &PathWord) -> Result<PathWord, QuiverError> {
        word.validate_in(self.algebra.quiver())?;
        Ok(reversed(word, self.opposite.quiver()))
    }

    /// The reversal of a word of the opposite as a word of the algebra, as
    /// [`Self::word_to_op`].
    pub fn word_from_op(&self, word: &PathWord) -> Result<PathWord, QuiverError> {
        word.validate_in(self.opposite.quiver())?;
        Ok(reversed(word, self.algebra.quiver()))
    }

    fn other_side(
        &self,
        algebra: &Arc<MonomialAlgebra>,
    ) -> Result<&Arc<MonomialAlgebra>, OppositeError> {
        if Arc::ptr_eq(algebra, &self.algebra) {
            Ok(&self.opposite)
        } else if Arc::ptr_eq(algebra, &self.opposite) {
            Ok(&self.algebra)
        } else {
            Err(OppositeError::AlgebraOutsidePair)
        }
    }
}

/// Caller guarantees `word` is a path of the quiver that `quiver` reverses.
/// The reversed arrows then compose left to right in `quiver` itself.
fn reversed(word: &PathWord, quiver: &Quiver) -> PathWord {
    if word.is_trivial() {
        PathWord::trivial_unchecked(word.source())
    } else {
        let arrows = word.arrows().iter().rev().copied().collect();
        PathWord::from_arrows_unchecked(quiver, arrows)
    }
}

/// The k-dual `D(M) = Hom_k(M, k)` of a right module over either side of `op`,
/// as a right module over the other side: same dimension vector,
/// `DM(a^op) = M(a)ᵀ`. `dual(&dual(m, op)?, op)?` restores `m` entry for entry,
/// over the same algebra [`Arc`].
pub fn dual(m: &Module, op: &OppositeMap) -> Result<Module, OppositeError> {
    let target = op.other_side(m.algebra())?.clone();
    let maps = (0..m.algebra().quiver().num_arrows())
        .map(|i| m.map(ArrowId(i as u32)).transpose())
        .collect();
    Ok(
        Module::new(target, m.field(), m.dim_vector().to_vec(), maps).expect(
            "a reversed forbidden word acts by the transposed original product, which is zero",
        ),
    )
}

fn same_entries(a: &Module, b: &Module) -> bool {
    Arc::ptr_eq(a.algebra(), b.algebra())
        && a.field() == b.field()
        && a.dim_vector() == b.dim_vector()
        && (0..a.algebra().quiver().num_arrows())
            .all(|i| a.map(ArrowId(i as u32)) == b.map(ArrowId(i as u32)))
}

/// The dual `D(f): D(N) → D(M)` of `f: M → N`, with matrix `f_vᵀ` at each
/// vertex.
///
/// Module identity is nominal, so the caller passes its own dual modules
/// `dual_of_target = D(N)` and `dual_of_source = D(M)`. Both are checked entry
/// for entry against [`dual`]. Dualized composites then share endpoints and
/// compose. Contravariance: dualizing `f.then(g)` against the outer duals
/// equals `dual_morphism` of `g` followed by that of `f` through the shared
/// dual of the middle module.
pub fn dual_morphism(
    f: &Morphism,
    dual_of_target: &Module,
    dual_of_source: &Module,
    op: &OppositeMap,
) -> Result<Morphism, OppositeError> {
    if !same_entries(dual_of_target, &dual(f.target(), op)?) {
        return Err(OppositeError::NotDualOfTarget);
    }
    if !same_entries(dual_of_source, &dual(f.source(), op)?) {
        return Err(OppositeError::NotDualOfSource);
    }
    let maps = (0..f.source().algebra().quiver().num_vertices())
        .map(|v| f.map_at(v).transpose())
        .collect();
    Ok(Morphism::new(dual_of_target, dual_of_source, maps)
        .expect("transposing every matrix of an A-linearity square transposes the square"))
}

/// A map between finite direct sums of indecomposable projectives
/// `⊕_k P_{sources[k]} → ⊕_l P_{targets[l]}`, stored as an element matrix.
///
/// `Hom_A(e_i A, e_j A) ≅ e_j A e_i` by `f ↦ f(e_i)`, the inverse acting by
/// left multiplication. Writing elements of the sums as row tuples, the map
/// acts componentwise as `v_l = Σ_k x_{k,l}·u_k`, so the entry at `(k, l)` lies
/// in `e_{targets[l]} A e_{sources[k]}`. The entry is stored as its
/// coefficients on the standard-path basis
/// `paths_between(targets[l], sources[k])`, in that order.
#[derive(Clone, Debug)]
pub struct ElementMatrix {
    algebra: Arc<MonomialAlgebra>,
    field: PrimeField,
    sources: Vec<u32>,
    targets: Vec<u32>,
    entries: Vec<Vec<Vec<Fp>>>,
}

impl ElementMatrix {
    /// Builds an element matrix after checking summand vertices, entry shapes,
    /// and coefficient canonicity for `field`.
    pub fn new(
        algebra: Arc<MonomialAlgebra>,
        field: PrimeField,
        sources: Vec<u32>,
        targets: Vec<u32>,
        entries: Vec<Vec<Vec<Fp>>>,
    ) -> Result<ElementMatrix, OppositeError> {
        let num_vertices = algebra.quiver().num_vertices();
        for &vertex in sources.iter().chain(&targets) {
            if vertex >= num_vertices {
                return Err(OppositeError::SummandOutOfRange {
                    vertex,
                    num_vertices,
                });
            }
        }
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
            field,
            sources,
            targets,
            entries,
        })
    }

    #[inline]
    pub fn algebra(&self) -> &Arc<MonomialAlgebra> {
        &self.algebra
    }

    #[inline]
    pub fn field(&self) -> PrimeField {
        self.field
    }

    /// The source summand vertices, `k`-th summand `P_{sources()[k]}`.
    #[inline]
    pub fn sources(&self) -> &[u32] {
        &self.sources
    }

    /// The target summand vertices, `l`-th summand `P_{targets()[l]}`.
    #[inline]
    pub fn targets(&self) -> &[u32] {
        &self.targets
    }

    /// The coefficients of entry `(k, l)` on
    /// `paths_between(targets()[l], sources()[k])`. Panics if `k` or `l` is out
    /// of range.
    #[inline]
    pub fn entry(&self, k: usize, l: usize) -> &[Fp] {
        &self.entries[k][l]
    }

    /// Reads the element matrix off a morphism between the standard direct sums
    /// `⊕_k P_{sources[k]} → ⊕_l P_{targets[l]}`. Entry `(k, l)` is the
    /// `l`-block of the image of summand `k`'s generator `e_{sources[k]}`. The
    /// standard sum is the layout of [`crate::module::direct_sum`] over
    /// [`Module::projective`] summands. Both endpoints are checked against it
    /// entry for entry.
    pub fn of_morphism(
        f: &Morphism,
        sources: &[u32],
        targets: &[u32],
    ) -> Result<ElementMatrix, OppositeError> {
        let algebra = f.source().algebra().clone();
        let field = f.source().field();
        let num_vertices = algebra.quiver().num_vertices();
        for &vertex in sources.iter().chain(targets) {
            if vertex >= num_vertices {
                return Err(OppositeError::SummandOutOfRange {
                    vertex,
                    num_vertices,
                });
            }
        }
        if !same_entries(f.source(), &projective_sum(&algebra, field, sources)) {
            return Err(OppositeError::SourceNotTheDeclaredSum);
        }
        if !same_entries(f.target(), &projective_sum(&algebra, field, targets)) {
            return Err(OppositeError::TargetNotTheDeclaredSum);
        }
        let positions = component_positions(&algebra);
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
            field,
            sources: sources.to_vec(),
            targets: targets.to_vec(),
            entries,
        })
    }

    /// The morphism the element matrix records, between freshly built standard
    /// sums `⊕_k P_{sources[k]} → ⊕_l P_{targets[l]}`.
    pub fn morphism(&self) -> Morphism {
        let source = projective_sum(&self.algebra, self.field, &self.sources);
        let target = projective_sum(&self.algebra, self.field, &self.targets);
        let maps = self.vertex_matrices();
        Morphism::new(&source, &target, maps)
            .expect("left multiplication by fixed algebra elements is A-linear")
    }

    /// One matrix per vertex `w`. The `(k, l)` block sends the basis path
    /// `u: sources[k] → w` to `Σ_r c_r (r·u)` over the coefficient paths `r` of
    /// entry `(k, l)`.
    fn vertex_matrices(&self) -> Vec<DenseMat> {
        let algebra = &self.algebra;
        let field = self.field;
        let positions = component_positions(algebra);
        (0..algebra.quiver().num_vertices())
            .map(|w| {
                let rows = self
                    .sources
                    .iter()
                    .map(|&s| algebra.paths_between(s, w).len())
                    .sum();
                let cols = self
                    .targets
                    .iter()
                    .map(|&t| algebra.paths_between(t, w).len())
                    .sum();
                let mut mat = DenseMat::zero(rows, cols);
                let mut row_offset = 0;
                for (k, &s) in self.sources.iter().enumerate() {
                    let mut col_offset = 0;
                    for (l, &t) in self.targets.iter().enumerate() {
                        for (ri, &r) in algebra.paths_between(t, s).iter().enumerate() {
                            let c = self.entries[k][l][ri];
                            if c.is_zero() {
                                continue;
                            }
                            for (ui, &u) in algebra.paths_between(s, w).iter().enumerate() {
                                if let Some(product) = mul_paths(algebra, r, u) {
                                    let row = row_offset + ui;
                                    let col = col_offset + positions[product];
                                    mat.set(row, col, field.add(mat.get(row, col), c));
                                }
                            }
                        }
                        col_offset += algebra.paths_between(t, w).len();
                    }
                    row_offset += algebra.paths_between(s, w).len();
                }
                mat
            })
            .collect()
    }

    /// The image of the matrix under `Hom_A(−, A)`: a map
    /// `⊕_l P^op_{targets[l]} → ⊕_k P^op_{sources[k]}` over the other side of
    /// `op`, with entry `(l, k)` the reversed word of entry `(k, l)`.
    /// `Hom_A(e_v A, A) ≅ A e_v = e_v A^op`, and precomposing left
    /// multiplication turns it into right multiplication. Applying
    /// `transpose_over` twice restores the matrix.
    pub fn transpose_over(&self, op: &OppositeMap) -> Result<ElementMatrix, OppositeError> {
        let to = op.other_side(&self.algebra)?.clone();
        let positions = component_positions(&to);
        let entries = self
            .targets
            .iter()
            .enumerate()
            .map(|(l, &t)| {
                self.sources
                    .iter()
                    .enumerate()
                    .map(|(k, &s)| {
                        let mut coefficients =
                            vec![self.field.zero(); to.paths_between(s, t).len()];
                        for (ri, &r) in self.algebra.paths_between(t, s).iter().enumerate() {
                            let c = self.entries[k][l][ri];
                            if c.is_zero() {
                                continue;
                            }
                            let word = reversed(&self.algebra.basis()[r], to.quiver());
                            let index = to
                                .path_index(&word)
                                .expect("reversed words are paths of the opposite quiver")
                                .expect("the reversal of a standard path is standard");
                            coefficients[positions[index]] = c;
                        }
                        coefficients
                    })
                    .collect()
            })
            .collect();
        Ok(ElementMatrix {
            algebra: to,
            field: self.field,
            sources: self.targets.clone(),
            targets: self.sources.clone(),
            entries,
        })
    }
}

/// The Nakayama functor `ν = D Hom_A(−, A)` on a map between projective sums:
/// the induced morphism `⊕_k I_{sources[k]} → ⊕_l I_{targets[l]}` between the
/// corresponding sums of the injectives built by [`Module::injective`].
///
/// Convention derivation (right modules, row vectors). The `(k, l)` component
/// of the map is left multiplication by `x = Σ_r c_r·r ∈ e_{t_l} A e_{s_k}`
/// (see [`ElementMatrix`]). `Hom_A(−, A)` turns it into right multiplication
/// `·x: A e_{t_l} → A e_{s_k}`. `D` of that is
/// `ν(x): D(A e_{s_k}) = I_{s_k} → D(A e_{t_l}) = I_{t_l}`. So `ν` is
/// covariant and `ν(P_i) = I_i` exactly. On the dual path bases of
/// [`Module::injective`], `ν(x)(q^*) = q^* ∘ (·x)` evaluates on a basis path
/// `p: w → t_l` to the coefficient of `q` in `p·x`, so in the row-vector
/// convention the matrix at vertex `w` has entry `Σ_r c_r [p·r = q]` at row
/// `q ∈ paths(w, s_k)`, column `p ∈ paths(w, t_l)`. Applied to a minimal
/// presentation `P_1 → P_0 → M → 0`, this is the map whose kernel is `τ M`:
/// `Hom_A(−, A)` gives `0 → Hom(M, A) → Hom(P_0, A) → Hom(P_1, A) → Tr M → 0`,
/// and dualizing gives `0 → τ M → ν P_1 → ν P_0 → ν M → 0`.
pub fn nu_of_presentation_map(matrix: &ElementMatrix) -> Morphism {
    let algebra = matrix.algebra();
    let field = matrix.field();
    let positions = component_positions(algebra);
    let source = injective_sum(algebra, field, matrix.sources());
    let target = injective_sum(algebra, field, matrix.targets());
    let maps = (0..algebra.quiver().num_vertices())
        .map(|w| {
            let rows = matrix
                .sources()
                .iter()
                .map(|&s| algebra.paths_between(w, s).len())
                .sum();
            let cols = matrix
                .targets()
                .iter()
                .map(|&t| algebra.paths_between(w, t).len())
                .sum();
            let mut mat = DenseMat::zero(rows, cols);
            let mut row_offset = 0;
            for (k, &s) in matrix.sources().iter().enumerate() {
                let mut col_offset = 0;
                for (l, &t) in matrix.targets().iter().enumerate() {
                    for (ri, &r) in algebra.paths_between(t, s).iter().enumerate() {
                        let c = matrix.entry(k, l)[ri];
                        if c.is_zero() {
                            continue;
                        }
                        for (pi, &p) in algebra.paths_between(w, t).iter().enumerate() {
                            if let Some(q) = mul_paths(algebra, p, r) {
                                let row = row_offset + positions[q];
                                let col = col_offset + pi;
                                mat.set(row, col, field.add(mat.get(row, col), c));
                            }
                        }
                    }
                    col_offset += algebra.paths_between(w, t).len();
                }
                row_offset += algebra.paths_between(w, s).len();
            }
            mat
        })
        .collect();
    Morphism::new(&source, &target, maps)
        .expect("ν of an element matrix is A-linear between the injective sums")
}

/// Position of each standard path within `paths_between` of its own endpoints,
/// indexed by [`BasisIdx`].
fn component_positions(algebra: &MonomialAlgebra) -> Vec<usize> {
    let n = algebra.quiver().num_vertices();
    let mut positions = vec![usize::MAX; algebra.dim()];
    for u in 0..n {
        for v in 0..n {
            for (i, &b) in algebra.paths_between(u, v).iter().enumerate() {
                positions[b] = i;
            }
        }
    }
    positions
}

/// `basis[p] · basis[q]` as a basis index, `None` when the product is zero.
/// Caller guarantees `target(p) == source(q)`.
fn mul_paths(algebra: &MonomialAlgebra, p: BasisIdx, q: BasisIdx) -> Option<BasisIdx> {
    debug_assert_eq!(algebra.basis()[p].target(), algebra.basis()[q].source());
    let mut acc = p;
    for &a in algebra.basis()[q].arrows() {
        acc = algebra.right_mul(acc, a)?;
    }
    Some(acc)
}

fn summand_sum(
    algebra: &Arc<MonomialAlgebra>,
    field: PrimeField,
    vertices: &[u32],
    build: fn(&Arc<MonomialAlgebra>, PrimeField, u32) -> Module,
) -> Module {
    match vertices {
        [] => Module::zero(algebra, field),
        &[v] => build(algebra, field, v),
        _ => {
            let parts: Vec<Module> = vertices.iter().map(|&v| build(algebra, field, v)).collect();
            let refs: Vec<&Module> = parts.iter().collect();
            direct_sum(&refs).0
        }
    }
}

fn projective_sum(algebra: &Arc<MonomialAlgebra>, field: PrimeField, vertices: &[u32]) -> Module {
    summand_sum(algebra, field, vertices, Module::projective)
}

fn injective_sum(algebra: &Arc<MonomialAlgebra>, field: PrimeField, vertices: &[u32]) -> Module {
    summand_sum(algebra, field, vertices, Module::injective)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{
        an_with_relations, cyclic_nakayama, dual_numbers, kronecker, linear_an,
        radical_square_zero_cycle,
    };
    use crate::hom::{hom, identity, kernel};

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn mat(field: &PrimeField, rows: &[&[i64]]) -> DenseMat {
        let rows: Vec<Vec<Fp>> = rows
            .iter()
            .map(|r| r.iter().map(|&v| field.elem(v)).collect())
            .collect();
        DenseMat::from_rows(&rows)
    }

    #[test]
    fn opposite_reverses_arrows_and_keeps_ids() {
        let a = linear_an(3);
        let op = opposite(&a);
        assert_eq!(op.opposite().quiver().arrows(), &[(1, 0), (2, 1)]);
        assert_eq!(op.arrow_to_op(ArrowId(1)), ArrowId(1));
        assert_eq!(op.arrow_from_op(ArrowId(0)), ArrowId(0));
    }

    #[test]
    fn opposite_reverses_forbidden_words() {
        let a = an_with_relations(3, &[(0, 2)]).unwrap();
        let op = opposite(&a);
        assert_eq!(op.opposite().forbidden(), &[vec![ArrowId(1), ArrowId(0)]]);
    }

    #[test]
    fn opposite_preserves_dimension() {
        for a in [
            linear_an(4),
            an_with_relations(3, &[(0, 2)]).unwrap(),
            kronecker(3),
            dual_numbers(),
            cyclic_nakayama(&[3, 3, 3]).unwrap(),
            radical_square_zero_cycle(3),
        ] {
            assert_eq!(opposite(&a).opposite().dim(), a.dim());
        }
    }

    #[test]
    fn opposite_of_the_opposite_restores_quiver_and_relations() {
        for a in [
            linear_an(3),
            an_with_relations(3, &[(0, 2)]).unwrap(),
            cyclic_nakayama(&[3, 3, 3]).unwrap(),
        ] {
            let double = opposite(opposite(&a).opposite());
            assert_eq!(double.opposite().quiver(), a.quiver());
            assert_eq!(double.opposite().forbidden(), a.forbidden());
        }
    }

    #[test]
    fn word_to_op_reverses_the_arrow_word_and_round_trips() {
        let a = linear_an(3);
        let op = opposite(&a);
        let word = PathWord::from_arrows(a.quiver(), &[ArrowId(0), ArrowId(1)]).unwrap();
        let rev = op.word_to_op(&word).unwrap();
        assert_eq!(rev.arrows(), &[ArrowId(1), ArrowId(0)]);
        assert_eq!((rev.source(), rev.target()), (2, 0));
        assert_eq!(op.word_from_op(&rev).unwrap(), word);
        let trivial = PathWord::trivial(a.quiver(), 1).unwrap();
        assert_eq!(op.word_to_op(&trivial).unwrap(), trivial);
    }

    #[test]
    fn word_to_op_rejects_words_from_the_other_side() {
        let a = linear_an(3);
        let op = opposite(&a);
        let backwards =
            PathWord::from_arrows(op.opposite().quiver(), &[ArrowId(1), ArrowId(0)]).unwrap();
        assert!(op.word_to_op(&backwards).is_err());
        assert!(op.word_from_op(&backwards).is_ok());
    }

    #[test]
    fn dual_transposes_each_arrow_matrix() {
        let a = dual_numbers();
        let field = f5();
        let m = Module::new(
            a.clone(),
            field,
            vec![2],
            vec![mat(&field, &[&[0, 1], &[0, 0]])],
        )
        .unwrap();
        let op = opposite(&a);
        let d = dual(&m, &op).unwrap();
        assert!(Arc::ptr_eq(d.algebra(), op.opposite()));
        assert_eq!(d.dim_vector(), m.dim_vector());
        assert_eq!(*d.map(ArrowId(0)), m.map(ArrowId(0)).transpose());
    }

    #[test]
    fn dual_of_a_module_over_the_opposite_lands_back_over_the_algebra() {
        let a = linear_an(3);
        let op = opposite(&a);
        let m = Module::projective(op.opposite(), f5(), 0);
        let d = dual(&m, &op).unwrap();
        assert!(Arc::ptr_eq(d.algebra(), &a));
    }

    #[test]
    fn dual_rejects_a_module_outside_the_pair() {
        let a = linear_an(3);
        let other = linear_an(3);
        let op = opposite(&a);
        let m = Module::simple(&other, f5(), 0);
        assert_eq!(
            dual(&m, &op).unwrap_err(),
            OppositeError::AlgebraOutsidePair
        );
    }

    #[test]
    fn double_dual_is_the_identity_entry_for_entry() {
        let a = an_with_relations(3, &[(0, 2)]).unwrap();
        let field = f5();
        let op = opposite(&a);
        for v in 0..3 {
            for m in [
                Module::simple(&a, field, v),
                Module::projective(&a, field, v),
                Module::injective(&a, field, v),
            ] {
                let dd = dual(&dual(&m, &op).unwrap(), &op).unwrap();
                assert!(same_entries(&dd, &m), "D(D(M)) != M at vertex {v}");
            }
        }
    }

    #[test]
    fn dual_of_the_identity_is_the_identity() {
        let a = linear_an(3);
        let field = f5();
        let op = opposite(&a);
        let p0 = Module::projective(&a, field, 0);
        let dp0 = dual(&p0, &op).unwrap();
        let d_id = dual_morphism(&identity(&p0), &dp0, &dp0, &op).unwrap();
        assert_eq!(d_id, identity(&dp0));
    }

    #[test]
    fn dual_morphism_transposes_vertex_matrices() {
        let a = linear_an(3);
        let field = f5();
        let op = opposite(&a);
        let p1 = Module::projective(&a, field, 1);
        let p0 = Module::projective(&a, field, 0);
        let f = hom(&p1, &p0).unwrap().remove(0);
        let dp1 = dual(&p1, &op).unwrap();
        let dp0 = dual(&p0, &op).unwrap();
        let df = dual_morphism(&f, &dp0, &dp1, &op).unwrap();
        for v in 0..3 {
            assert_eq!(*df.map_at(v), f.map_at(v).transpose());
        }
        assert!(df.source().ptr_eq(&dp0));
        assert!(df.target().ptr_eq(&dp1));
    }

    #[test]
    fn dual_morphism_is_contravariant_on_a_composition() {
        // Right-module Hom runs down the arrows: f: P_2 → P_1, g: P_1 → P_0.
        let a = linear_an(3);
        let field = f5();
        let op = opposite(&a);
        let p2 = Module::projective(&a, field, 2);
        let p1 = Module::projective(&a, field, 1);
        let p0 = Module::projective(&a, field, 0);
        let f = hom(&p2, &p1).unwrap().remove(0);
        let g = hom(&p1, &p0).unwrap().remove(0);
        let d2 = dual(&p2, &op).unwrap();
        let d1 = dual(&p1, &op).unwrap();
        let d0 = dual(&p0, &op).unwrap();
        let left = dual_morphism(&f.then(&g).unwrap(), &d0, &d2, &op).unwrap();
        let right = dual_morphism(&g, &d0, &d1, &op)
            .unwrap()
            .then(&dual_morphism(&f, &d1, &d2, &op).unwrap())
            .unwrap();
        assert!(!left.is_zero());
        assert_eq!(left, right);
    }

    #[test]
    fn dual_morphism_rejects_a_wrong_dual() {
        let a = linear_an(3);
        let field = f5();
        let op = opposite(&a);
        let p0 = Module::projective(&a, field, 0);
        let f = identity(&p0);
        let dp0 = dual(&p0, &op).unwrap();
        let wrong = Module::simple(op.opposite(), field, 0);
        assert_eq!(
            dual_morphism(&f, &wrong, &dp0, &op).unwrap_err(),
            OppositeError::NotDualOfTarget
        );
        assert_eq!(
            dual_morphism(&f, &dp0, &wrong, &op).unwrap_err(),
            OppositeError::NotDualOfSource
        );
    }

    #[test]
    fn element_matrix_new_rejects_shape_and_canonicity_violations() {
        let a = linear_an(3);
        let field = f5();
        assert_eq!(
            ElementMatrix::new(a.clone(), field, vec![3], Vec::new(), vec![Vec::new()])
                .unwrap_err(),
            OppositeError::SummandOutOfRange {
                vertex: 3,
                num_vertices: 3
            }
        );
        assert_eq!(
            ElementMatrix::new(a.clone(), field, vec![0], vec![0], Vec::new()).unwrap_err(),
            OppositeError::RowCountMismatch {
                expected: 1,
                got: 0
            }
        );
        assert_eq!(
            ElementMatrix::new(a.clone(), field, vec![0], vec![0], vec![Vec::new()]).unwrap_err(),
            OppositeError::ColumnCountMismatch {
                row: 0,
                expected: 1,
                got: 0
            }
        );
        assert_eq!(
            ElementMatrix::new(a.clone(), field, vec![0], vec![0], vec![vec![Vec::new()]])
                .unwrap_err(),
            OppositeError::CoefficientCountMismatch {
                row: 0,
                col: 0,
                expected: 1,
                got: 0
            }
        );
        let f7 = PrimeField::new(7).unwrap();
        assert_eq!(
            ElementMatrix::new(a, field, vec![0], vec![0], vec![vec![vec![f7.elem(6)]]])
                .unwrap_err(),
            OppositeError::NonCanonicalCoefficient {
                row: 0,
                col: 0,
                index: 0
            }
        );
    }

    #[test]
    fn element_matrix_realizes_left_multiplication() {
        // Hom(P_1, P_0) over A_3 is spanned by left multiplication by the arrow
        // a, sending e_1 ↦ a and b ↦ ab.
        let a = linear_an(3);
        let field = f5();
        let em =
            ElementMatrix::new(a, field, vec![1], vec![0], vec![vec![vec![field.one()]]]).unwrap();
        let f = em.morphism();
        assert_eq!(f.source().dim_vector(), &[0, 1, 1]);
        assert_eq!(f.target().dim_vector(), &[1, 1, 1]);
        assert_eq!(*f.map_at(0), DenseMat::zero(0, 1));
        assert_eq!(*f.map_at(1), DenseMat::identity(1));
        assert_eq!(*f.map_at(2), DenseMat::identity(1));
    }

    #[test]
    fn element_matrix_of_morphism_round_trips() {
        let a = an_with_relations(3, &[(0, 2)]).unwrap();
        let field = f5();
        let em = ElementMatrix::new(a, field, vec![1], vec![0], vec![vec![vec![field.elem(3)]]])
            .unwrap();
        let back = ElementMatrix::of_morphism(&em.morphism(), &[1], &[0]).unwrap();
        assert_eq!(back.sources(), &[1]);
        assert_eq!(back.targets(), &[0]);
        assert_eq!(back.entry(0, 0), &[field.elem(3)]);
    }

    #[test]
    fn of_morphism_recovers_a_two_summand_matrix() {
        let a = kronecker(2);
        let field = f5();
        let entries = vec![
            vec![vec![field.elem(1), field.elem(2)]],
            vec![vec![field.elem(3), field.elem(4)]],
        ];
        let em = ElementMatrix::new(a, field, vec![1, 1], vec![0], entries.clone()).unwrap();
        let back = ElementMatrix::of_morphism(&em.morphism(), &[1, 1], &[0]).unwrap();
        assert_eq!(back.entry(0, 0), entries[0][0].as_slice());
        assert_eq!(back.entry(1, 0), entries[1][0].as_slice());
    }

    #[test]
    fn of_morphism_rejects_endpoints_that_are_not_the_declared_sums() {
        let a = linear_an(3);
        let field = f5();
        let p0 = Module::projective(&a, field, 0);
        let f = identity(&p0);
        assert_eq!(
            ElementMatrix::of_morphism(&f, &[1], &[0]).unwrap_err(),
            OppositeError::SourceNotTheDeclaredSum
        );
        assert_eq!(
            ElementMatrix::of_morphism(&f, &[0], &[1]).unwrap_err(),
            OppositeError::TargetNotTheDeclaredSum
        );
    }

    #[test]
    fn transpose_over_swaps_summands_and_reverses_words() {
        let a = linear_an(3);
        let field = f5();
        let op = opposite(&a);
        // x = ab ∈ e_0 A e_2, the map P_2 → P_0.
        let em = ElementMatrix::new(
            a.clone(),
            field,
            vec![2],
            vec![0],
            vec![vec![vec![field.one()]]],
        )
        .unwrap();
        let t = em.transpose_over(&op).unwrap();
        assert!(Arc::ptr_eq(t.algebra(), op.opposite()));
        assert_eq!(t.sources(), &[0]);
        assert_eq!(t.targets(), &[2]);
        assert_eq!(t.entry(0, 0), &[field.one()]);
        let back = t.transpose_over(&op).unwrap();
        assert!(Arc::ptr_eq(back.algebra(), &a));
        assert_eq!(back.sources(), em.sources());
        assert_eq!(back.targets(), em.targets());
        assert_eq!(back.entry(0, 0), em.entry(0, 0));
    }

    #[test]
    fn nu_of_the_identity_on_p_v_is_the_identity_on_i_v() {
        let a = an_with_relations(3, &[(0, 2)]).unwrap();
        let field = f5();
        for v in 0..3u32 {
            let component = a.paths_between(v, v);
            let mut coefficients = vec![field.zero(); component.len()];
            let position = component
                .iter()
                .position(|&b| b == a.vertex_idempotent(v))
                .expect("the trivial path lies in its own component");
            coefficients[position] = field.one();
            let em =
                ElementMatrix::new(a.clone(), field, vec![v], vec![v], vec![vec![coefficients]])
                    .unwrap();
            let nu = nu_of_presentation_map(&em);
            let injective = Module::injective(&a, field, v);
            assert!(same_entries(nu.source(), &injective), "ν(P_{v}) source");
            assert!(same_entries(nu.target(), &injective), "ν(P_{v}) target");
            for w in 0..3 {
                assert_eq!(*nu.map_at(w), DenseMat::identity(injective.dim_at(w)));
            }
        }
    }

    #[test]
    fn nu_kernel_of_the_a3_presentation_of_s0_is_s1() {
        // d_1 for S_0 over A_3 is left multiplication by a: P_1 → P_0. The
        // kernel of ν(d_1): I_1 → I_0 is the AR translate τ S_0 = S_1.
        let a = linear_an(3);
        let field = f5();
        let em =
            ElementMatrix::new(a, field, vec![1], vec![0], vec![vec![vec![field.one()]]]).unwrap();
        let nu = nu_of_presentation_map(&em);
        assert_eq!(nu.source().dim_vector(), &[1, 1, 0]);
        assert_eq!(nu.target().dim_vector(), &[1, 0, 0]);
        let (ker, _) = kernel(&nu);
        assert_eq!(ker.dim_vector(), &[0, 1, 0]);
    }

    #[test]
    fn nu_of_an_empty_source_is_a_map_from_the_zero_module() {
        let a = linear_an(3);
        let field = f5();
        let em = ElementMatrix::new(a.clone(), field, Vec::new(), vec![2], Vec::new()).unwrap();
        let nu = nu_of_presentation_map(&em);
        assert!(nu.source().is_zero());
        assert_eq!(
            nu.target().dim_vector(),
            Module::injective(&a, field, 2).dim_vector()
        );
        let (ker, _) = kernel(&nu);
        assert!(ker.is_zero());
    }
}
