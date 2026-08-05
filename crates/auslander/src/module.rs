//! Finite-dimensional right modules over a monomial algebra.
//!
//! A module assigns to each vertex `v` the row-vector space `k^{dims[v]}` and to each
//! arrow `a` a `dims[source(a)] × dims[target(a)]` matrix; a path acts by the product
//! of its arrow matrices in word order, so `M(p·q) = M(p) M(q)` under the left-to-right
//! convention of [`crate::quiver`]. Construction verifies that every minimal forbidden
//! word acts as zero; this suffices for the whole ideal, because any longer element of
//! `I` contains a forbidden factor whose matrix product is already zero. A `Module`
//! value is therefore always a genuine `kQ/I`-module.

use std::fmt;
use std::sync::Arc;

use crate::algebra::MonomialAlgebra;
use crate::field::PrimeField;
use crate::hom::Morphism;
use crate::linalg::DenseMat;
use crate::quiver::{ArrowId, PathWord, QuiverError};

/// Rejected module construction input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModuleError {
    /// `dims` needs one entry per vertex.
    DimsLengthMismatch { expected: usize, got: usize },
    /// `maps` needs one matrix per arrow.
    MapCountMismatch { expected: usize, got: usize },
    /// `maps[arrow]` must be `dims[source] × dims[target]`.
    MapShapeMismatch {
        arrow: ArrowId,
        expected: (usize, usize),
        got: (usize, usize),
    },
    /// `maps[arrow]` holds an entry at `(row, col)` whose representative is not
    /// canonical for the declared field (not below its modulus); the entry was
    /// produced by a different field.
    NonCanonicalEntry {
        arrow: ArrowId,
        row: usize,
        col: usize,
    },
    /// The arrow matrices along minimal forbidden word `index` have nonzero product,
    /// so the data is a `kQ`-representation but not a `kQ/I`-module.
    ForbiddenWordActsNonzero { index: usize },
}

impl fmt::Display for ModuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DimsLengthMismatch { expected, got } => {
                write!(f, "dims has {got} entries, quiver has {expected} vertices")
            }
            Self::MapCountMismatch { expected, got } => {
                write!(f, "maps has {got} matrices, quiver has {expected} arrows")
            }
            Self::MapShapeMismatch {
                arrow,
                expected,
                got,
            } => write!(
                f,
                "map for arrow {} is {}x{}, expected {}x{}",
                arrow.0, got.0, got.1, expected.0, expected.1
            ),
            Self::NonCanonicalEntry { arrow, row, col } => write!(
                f,
                "map for arrow {} has a non-canonical entry at ({row}, {col}) for the declared field",
                arrow.0
            ),
            Self::ForbiddenWordActsNonzero { index } => {
                write!(f, "forbidden word {index} acts as a nonzero matrix")
            }
        }
    }
}

impl std::error::Error for ModuleError {}

/// A finite-dimensional right `kQ/I`-module, validated at construction.
///
/// Identity is nominal, matching the algebra [`Arc`] policy: clones share the
/// underlying representation and compare equal under [`Module::ptr_eq`], while
/// two modules constructed separately are distinct even when entrywise
/// identical. Morphism endpoints use this identity. There is no structural
/// equality. Cloning is cheap (a reference count bump).
#[derive(Clone, Debug)]
pub struct Module(Arc<ModuleInner>);

#[derive(Debug)]
struct ModuleInner {
    algebra: Arc<MonomialAlgebra>,
    field: PrimeField,
    dims: Vec<usize>,
    // One matrix per arrow, dims[source] × dims[target], acting on row vectors.
    maps: Vec<DenseMat>,
}

fn is_zero_mat(m: &DenseMat) -> bool {
    (0..m.rows()).all(|r| m.row(r).iter().all(|v| v.is_zero()))
}

impl Module {
    /// Builds a module after checking map shapes, entry canonicity for `field`,
    /// and that every minimal forbidden word acts as zero.
    pub fn new(
        algebra: Arc<MonomialAlgebra>,
        field: PrimeField,
        dims: Vec<usize>,
        maps: Vec<DenseMat>,
    ) -> Result<Module, ModuleError> {
        let quiver = algebra.quiver();
        let num_vertices = quiver.num_vertices() as usize;
        if dims.len() != num_vertices {
            return Err(ModuleError::DimsLengthMismatch {
                expected: num_vertices,
                got: dims.len(),
            });
        }
        if maps.len() != quiver.num_arrows() {
            return Err(ModuleError::MapCountMismatch {
                expected: quiver.num_arrows(),
                got: maps.len(),
            });
        }
        for (i, map) in maps.iter().enumerate() {
            let arrow = ArrowId(i as u32);
            let expected = (
                dims[quiver.source(arrow) as usize],
                dims[quiver.target(arrow) as usize],
            );
            let got = (map.rows(), map.cols());
            if got != expected {
                return Err(ModuleError::MapShapeMismatch {
                    arrow,
                    expected,
                    got,
                });
            }
        }
        for (i, map) in maps.iter().enumerate() {
            if let Some((row, col)) = map.first_noncanonical(&field) {
                return Err(ModuleError::NonCanonicalEntry {
                    arrow: ArrowId(i as u32),
                    row,
                    col,
                });
            }
        }
        for (index, word) in algebra.forbidden().iter().enumerate() {
            let mut acc = maps[word[0].index()].clone();
            for &a in &word[1..] {
                acc = acc.mul(&maps[a.index()], &field);
            }
            if !is_zero_mat(&acc) {
                return Err(ModuleError::ForbiddenWordActsNonzero { index });
            }
        }
        Ok(Module(Arc::new(ModuleInner {
            algebra,
            field,
            dims,
            maps,
        })))
    }

    /// Whether `self` and `other` are the same module value (clones of one
    /// construction), the identity used for morphism endpoints.
    #[inline]
    pub fn ptr_eq(&self, other: &Module) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    /// The zero module.
    pub fn zero(algebra: &Arc<MonomialAlgebra>, field: PrimeField) -> Module {
        let dims = vec![0; algebra.quiver().num_vertices() as usize];
        let maps = vec![DenseMat::zero(0, 0); algebra.quiver().num_arrows()];
        Module::new(algebra.clone(), field, dims, maps).expect("the zero module is a module")
    }

    /// The simple module `S_v`: one-dimensional at `v`, zero elsewhere, all arrows
    /// acting as zero.
    ///
    /// # Panics
    /// Panics if `v` is not a vertex of the algebra's quiver.
    pub fn simple(algebra: &Arc<MonomialAlgebra>, field: PrimeField, v: u32) -> Module {
        let quiver = algebra.quiver();
        assert!(v < quiver.num_vertices(), "simple: vertex {v} out of range");
        let dims: Vec<usize> = (0..quiver.num_vertices())
            .map(|w| usize::from(w == v))
            .collect();
        let maps = (0..quiver.num_arrows())
            .map(|i| {
                let a = ArrowId(i as u32);
                DenseMat::zero(
                    dims[quiver.source(a) as usize],
                    dims[quiver.target(a) as usize],
                )
            })
            .collect();
        Module::new(algebra.clone(), field, dims, maps).expect("S_v is a module")
    }

    /// The indecomposable projective `P_v = e_v A`: at vertex `w` the basis is the
    /// standard paths `v → w`, and an arrow `a` sends the basis path `p` to
    /// `p·a` when that is standard and to zero otherwise.
    ///
    /// # Panics
    /// Panics if `v` is not a vertex of the algebra's quiver.
    pub fn projective(algebra: &Arc<MonomialAlgebra>, field: PrimeField, v: u32) -> Module {
        let quiver = algebra.quiver();
        assert!(
            v < quiver.num_vertices(),
            "projective: vertex {v} out of range"
        );
        // pos[b] = position of basis path b inside its component's ordered basis.
        let mut pos = vec![usize::MAX; algebra.dim()];
        let mut dims = vec![0usize; quiver.num_vertices() as usize];
        for w in 0..quiver.num_vertices() {
            let component = algebra.paths_between(v, w);
            dims[w as usize] = component.len();
            for (i, &b) in component.iter().enumerate() {
                pos[b] = i;
            }
        }
        let maps = (0..quiver.num_arrows())
            .map(|i| {
                let a = ArrowId(i as u32);
                let (s, t) = (quiver.source(a), quiver.target(a));
                let mut mat = DenseMat::zero(dims[s as usize], dims[t as usize]);
                for (row, &p) in algebra.paths_between(v, s).iter().enumerate() {
                    if let Some(q) = algebra.right_mul(p, a) {
                        mat.set(row, pos[q], field.one());
                    }
                }
                mat
            })
            .collect();
        Module::new(algebra.clone(), field, dims, maps).expect("P_v is a module")
    }

    /// The indecomposable injective `I_v = D(A e_v)`: at vertex `w` the basis is the
    /// dual basis `{p* : p a standard path w → v}`.
    ///
    /// The right action dualizes left multiplication: `(f·a)(x) = f(a·x)`, so for an
    /// arrow `a: w → w'` the matrix entry at row `q ∈ paths(w, v)`, column
    /// `p ∈ paths(w', v)` is 1 exactly when `a·p = q`.
    ///
    /// # Panics
    /// Panics if `v` is not a vertex of the algebra's quiver.
    pub fn injective(algebra: &Arc<MonomialAlgebra>, field: PrimeField, v: u32) -> Module {
        let quiver = algebra.quiver();
        assert!(
            v < quiver.num_vertices(),
            "injective: vertex {v} out of range"
        );
        let mut pos = vec![usize::MAX; algebra.dim()];
        let mut dims = vec![0usize; quiver.num_vertices() as usize];
        for w in 0..quiver.num_vertices() {
            let component = algebra.paths_between(w, v);
            dims[w as usize] = component.len();
            for (i, &b) in component.iter().enumerate() {
                pos[b] = i;
            }
        }
        let maps = (0..quiver.num_arrows())
            .map(|i| {
                let a = ArrowId(i as u32);
                let (s, t) = (quiver.source(a), quiver.target(a));
                let mut mat = DenseMat::zero(dims[s as usize], dims[t as usize]);
                for (col, &p) in algebra.paths_between(t, v).iter().enumerate() {
                    if let Some(q) = algebra.left_mul(a, p) {
                        mat.set(pos[q], col, field.one());
                    }
                }
                mat
            })
            .collect();
        Module::new(algebra.clone(), field, dims, maps).expect("I_v is a module")
    }

    #[inline]
    pub fn algebra(&self) -> &Arc<MonomialAlgebra> {
        &self.0.algebra
    }

    #[inline]
    pub fn field(&self) -> PrimeField {
        self.0.field
    }

    /// The dimension vector, indexed by vertex.
    #[inline]
    pub fn dim_vector(&self) -> &[usize] {
        &self.0.dims
    }

    /// `dim_k M_v`. Panics if `v` is out of range.
    #[inline]
    pub fn dim_at(&self, v: u32) -> usize {
        self.0.dims[v as usize]
    }

    /// `dim_k M`.
    pub fn total_dim(&self) -> usize {
        self.0.dims.iter().sum()
    }

    pub fn is_zero(&self) -> bool {
        self.0.dims.iter().all(|&d| d == 0)
    }

    /// The matrix of `a` acting on row vectors, `dims[source] × dims[target]`.
    /// Panics if `a` is not an arrow of the algebra's quiver.
    #[inline]
    pub fn map(&self, a: ArrowId) -> &DenseMat {
        &self.0.maps[a.index()]
    }

    /// The matrix of `word` acting on row vectors: the identity for a trivial path,
    /// otherwise the product of the arrow matrices in word order. Errors when
    /// `word` is not a path of this algebra's quiver (see [`PathWord::validate_in`]).
    pub fn word_action(&self, word: &PathWord) -> Result<DenseMat, QuiverError> {
        word.validate_in(self.0.algebra.quiver())?;
        let mut acc = DenseMat::identity(self.0.dims[word.source() as usize]);
        for &a in word.arrows() {
            acc = acc.mul(&self.0.maps[a.index()], &self.0.field);
        }
        Ok(acc)
    }
}

/// The direct sum with its block inclusions and projections, in summand order.
///
/// `projections[k]` splits `inclusions[k]` (composes to the identity), and
/// `inclusions[j].then(projections[k])` is zero for `j != k`.
///
/// # Panics
/// Panics on an empty slice or when the summands do not share one algebra and field.
pub fn direct_sum(summands: &[&Module]) -> (Module, Vec<Morphism>, Vec<Morphism>) {
    assert!(!summands.is_empty(), "direct_sum: needs a summand");
    let first = summands[0];
    for s in &summands[1..] {
        assert!(
            Arc::ptr_eq(first.algebra(), s.algebra()),
            "direct_sum: mixed algebras"
        );
        assert_eq!(first.field(), s.field(), "direct_sum: mixed fields");
    }
    let quiver = first.algebra().quiver();
    let n = quiver.num_vertices() as usize;
    let field = first.field();
    let mut offsets = vec![vec![0usize; n]; summands.len()];
    let mut dims = vec![0usize; n];
    for (k, s) in summands.iter().enumerate() {
        for (v, dim) in dims.iter_mut().enumerate() {
            offsets[k][v] = *dim;
            *dim += s.dim_vector()[v];
        }
    }
    let maps = (0..quiver.num_arrows())
        .map(|i| {
            let a = ArrowId(i as u32);
            let (u, w) = (quiver.source(a) as usize, quiver.target(a) as usize);
            let mut mat = DenseMat::zero(dims[u], dims[w]);
            for (k, s) in summands.iter().enumerate() {
                let block = s.map(a);
                for r in 0..block.rows() {
                    for c in 0..block.cols() {
                        mat.set(offsets[k][u] + r, offsets[k][w] + c, block.get(r, c));
                    }
                }
            }
            mat
        })
        .collect();
    let sum = Module::new(first.algebra().clone(), field, dims, maps)
        .expect("a direct sum of modules is a module");
    let mut inclusions = Vec::with_capacity(summands.len());
    let mut projections = Vec::with_capacity(summands.len());
    for (k, s) in summands.iter().enumerate() {
        let mut incl = Vec::with_capacity(n);
        let mut proj = Vec::with_capacity(n);
        for (v, &offset) in offsets[k].iter().enumerate() {
            let mut inc = DenseMat::zero(s.dim_vector()[v], sum.dim_vector()[v]);
            let mut prj = DenseMat::zero(sum.dim_vector()[v], s.dim_vector()[v]);
            for i in 0..s.dim_vector()[v] {
                inc.set(i, offset + i, field.one());
                prj.set(offset + i, i, field.one());
            }
            incl.push(inc);
            proj.push(prj);
        }
        inclusions.push(Morphism::new(s, &sum, incl).expect("block inclusion commutes"));
        projections.push(Morphism::new(&sum, s, proj).expect("block projection commutes"));
    }
    (sum, inclusions, projections)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{an_with_relations, cyclic_nakayama, dual_numbers, linear_an};
    use crate::field::Fp;
    use crate::hom::{identity, zero_morphism};

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
    fn invertible_loop_action_is_rejected() {
        let a = dual_numbers();
        let field = f5();
        let result = Module::new(a, field, vec![1], vec![mat(&field, &[&[1]])]);
        assert_eq!(
            result.unwrap_err(),
            ModuleError::ForbiddenWordActsNonzero { index: 0 }
        );
    }

    #[test]
    fn nilpotent_loop_action_is_accepted() {
        let a = dual_numbers();
        let field = f5();
        let m = Module::new(a, field, vec![2], vec![mat(&field, &[&[0, 1], &[0, 0]])]).unwrap();
        assert_eq!(m.total_dim(), 2);
        assert!(!m.is_zero());
    }

    #[test]
    fn wrong_dims_length_is_rejected() {
        let a = linear_an(3);
        let result = Module::new(a, f5(), vec![1, 1], vec![DenseMat::zero(1, 1); 2]);
        assert_eq!(
            result.unwrap_err(),
            ModuleError::DimsLengthMismatch {
                expected: 3,
                got: 2
            }
        );
    }

    #[test]
    fn wrong_map_shape_is_rejected() {
        let a = linear_an(3);
        let maps = vec![DenseMat::zero(1, 1), DenseMat::zero(2, 1)];
        let result = Module::new(a, f5(), vec![1, 1, 1], maps);
        assert_eq!(
            result.unwrap_err(),
            ModuleError::MapShapeMismatch {
                arrow: ArrowId(1),
                expected: (1, 1),
                got: (2, 1)
            }
        );
    }

    #[test]
    fn zero_module_has_dimension_zero() {
        let a = linear_an(3);
        let z = Module::zero(&a, f5());
        assert!(z.is_zero());
        assert_eq!(z.total_dim(), 0);
        assert_eq!(z.dim_vector(), &[0, 0, 0]);
    }

    #[test]
    fn word_action_multiplies_arrow_matrices_in_word_order() {
        let a = linear_an(3);
        let field = f5();
        let p0 = Module::projective(&a, field, 0);
        let word =
            PathWord::from_arrows(a.quiver(), &[ArrowId(0), ArrowId(1)]).expect("path a·b in A_3");
        let expected = p0.map(ArrowId(0)).mul(p0.map(ArrowId(1)), &field);
        assert_eq!(p0.word_action(&word), Ok(expected));
        let trivial = PathWord::trivial(a.quiver(), 0).unwrap();
        assert_eq!(p0.word_action(&trivial), Ok(DenseMat::identity(1)));
    }

    #[test]
    fn word_action_rejects_a_word_from_another_quiver() {
        let a = linear_an(3);
        let other = dual_numbers();
        let p0 = Module::projective(&a, f5(), 0);
        let word = PathWord::from_arrows(other.quiver(), &[ArrowId(0)]).unwrap();
        assert_eq!(
            p0.word_action(&word),
            Err(QuiverError::EndpointsDisagree {
                stored: (0, 0),
                computed: (0, 1),
            })
        );
    }

    #[test]
    fn non_canonical_entry_is_rejected_before_relation_checks() {
        // The entry 3 is canonical in F_5 but not in F_2; over F_2 the loop's square
        // would also violate x² = 0, and the canonicity error must win.
        let a = dual_numbers();
        let f2 = PrimeField::new(2).unwrap();
        let maps = vec![mat(&f5(), &[&[3]])];
        assert_eq!(
            Module::new(a, f2, vec![1], maps).unwrap_err(),
            ModuleError::NonCanonicalEntry {
                arrow: ArrowId(0),
                row: 0,
                col: 0,
            }
        );
    }

    #[test]
    fn simple_is_one_dimensional_at_its_vertex() {
        let a = an_with_relations(3, &[(0, 2)]).unwrap();
        for v in 0..3 {
            let s = Module::simple(&a, f5(), v);
            let expected: Vec<usize> = (0..3).map(|w| usize::from(w == v as usize)).collect();
            assert_eq!(s.dim_vector(), expected.as_slice());
        }
    }

    // Cartan orientation: c[i][j] = dim e_i A e_j, so row i is the dimension vector of
    // P_i = e_i A and column j is the dimension vector of I_j = D(A e_j).
    #[test]
    fn projective_dim_vectors_are_cartan_rows() {
        let field = f5();
        for algebra in [
            linear_an(3),
            an_with_relations(3, &[(0, 2)]).unwrap(),
            cyclic_nakayama(&[2, 2, 2]).unwrap(),
        ] {
            let cartan = algebra.cartan_matrix();
            for v in 0..algebra.quiver().num_vertices() {
                let p = Module::projective(&algebra, field, v);
                assert_eq!(p.dim_vector(), cartan[v as usize].as_slice(), "P_{v}");
            }
        }
    }

    #[test]
    fn injective_dim_vectors_are_cartan_columns() {
        let field = f5();
        for algebra in [
            linear_an(3),
            an_with_relations(3, &[(0, 2)]).unwrap(),
            cyclic_nakayama(&[2, 2, 2]).unwrap(),
        ] {
            let cartan = algebra.cartan_matrix();
            for v in 0..algebra.quiver().num_vertices() {
                let i = Module::injective(&algebra, field, v);
                let column: Vec<usize> = cartan.iter().map(|row| row[v as usize]).collect();
                assert_eq!(i.dim_vector(), column.as_slice(), "I_{v}");
            }
        }
    }

    #[test]
    fn a3_mod_ab_projective_p0_has_dimension_vector_1_1_0() {
        let a = an_with_relations(3, &[(0, 2)]).unwrap();
        let p0 = Module::projective(&a, f5(), 0);
        assert_eq!(p0.dim_vector(), &[1, 1, 0]);
    }

    #[test]
    fn direct_sum_projections_split_inclusions() {
        let a = linear_an(3);
        let field = f5();
        let p0 = Module::projective(&a, field, 0);
        let p1 = Module::projective(&a, field, 1);
        let s2 = Module::simple(&a, field, 2);
        let parts = [&p0, &p1, &s2];
        let (sum, inclusions, projections) = direct_sum(&parts);
        for v in 0..3 {
            assert_eq!(
                sum.dim_at(v),
                parts.iter().map(|m| m.dim_at(v)).sum::<usize>()
            );
        }
        for (k, part) in parts.iter().enumerate() {
            assert_eq!(
                inclusions[k].then(&projections[k]).unwrap(),
                identity(part),
                "π_{k} ∘ ι_{k}"
            );
            for (j, other) in parts.iter().enumerate() {
                if j != k {
                    assert_eq!(
                        inclusions[j].then(&projections[k]).unwrap(),
                        zero_morphism(other, part).unwrap(),
                        "π_{k} ∘ ι_{j}"
                    );
                }
            }
        }
    }
}
