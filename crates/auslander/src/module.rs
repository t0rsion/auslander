//! Finite-dimensional modules over an [`Algebra`].
//!
//! A module assigns to each vertex `v` the space `k^{dims[v]}`, and to each
//! arrow `a` a `dims[source(a)] × dims[target(a)]` matrix. A path acts by the
//! product of its arrow matrices in word order.
//!
//! [`Module::new`] checks that every relation of the reduced Groebner basis
//! acts as the zero matrix. That covers the whole ideal: the action of
//! `u·r·v` factors through the matrix of `r`. A `Module` is always a
//! `kQ/I`-module.

use std::sync::Arc;

use crate::algebra::{Algebra, BasisIdx};
use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, matrix_is_zero};
use crate::linalg::DenseMat;
use crate::profile::{Site, hit};
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
    /// `maps[arrow]` has an entry at `(row, col)` not below the field modulus.
    NonCanonicalEntry {
        arrow: ArrowId,
        row: usize,
        col: usize,
    },
    /// Groebner relation `index` acts as a nonzero matrix, so the data is a
    /// `kQ`-representation but not a `kQ/I`-module.
    RelationActsNonzero { index: usize },
}

display_error! { error ModuleError {
    Self::DimsLengthMismatch { expected, got } => "dims has {got} entries, quiver has {expected} vertices";
    Self::MapCountMismatch { expected, got } => "maps has {got} matrices, quiver has {expected} arrows";
    Self::MapShapeMismatch { arrow, expected, got } => "map for arrow {} is {}x{}, expected {}x{}", arrow.0, got.0, got.1, expected.0, expected.1;
    Self::NonCanonicalEntry { arrow, row, col } => "map for arrow {} has a non-canonical entry at ({row}, {col}) for the algebra's field", arrow.0;
    Self::RelationActsNonzero { index } => "relation {index} acts as a nonzero matrix";
} }

/// A finite-dimensional `kQ/I`-module, validated at construction.
///
/// Identity is nominal, matching the algebra [`Arc`] policy. Clones share one
/// representation and compare equal under [`Module::ptr_eq`]. Two modules built
/// separately stay distinct even when entrywise identical. Morphism endpoints
/// use this identity.
#[derive(Clone, Debug)]
pub struct Module(Arc<ModuleInner>);

#[derive(Debug)]
struct ModuleInner {
    algebra: Arc<Algebra>,
    dims: Vec<usize>,
    // One matrix per arrow, dims[source] × dims[target].
    maps: Vec<DenseMat>,
}

fn zero_maps(algebra: &Algebra, dims: &[usize]) -> Vec<DenseMat> {
    let quiver = algebra.quiver();
    (0..quiver.num_arrows())
        .map(|i| {
            let arrow = ArrowId(i as u32);
            DenseMat::zero(
                dims[quiver.source(arrow) as usize],
                dims[quiver.target(arrow) as usize],
            )
        })
        .collect()
}

fn basis_data(
    algebra: &Arc<Algebra>,
    vertex: u32,
    incoming: bool,
    kind: &str,
) -> (Vec<usize>, Vec<usize>) {
    let quiver = algebra.quiver();
    assert!(
        vertex < quiver.num_vertices(),
        "{kind}: vertex {vertex} out of range"
    );
    let mut positions = vec![usize::MAX; algebra.dim()];
    let mut dims = vec![0usize; quiver.num_vertices() as usize];
    for w in 0..quiver.num_vertices() {
        let component = if incoming {
            algebra.paths_between(w, vertex)
        } else {
            algebra.paths_between(vertex, w)
        };
        dims[w as usize] = component.len();
        for (index, &basis) in component.iter().enumerate() {
            positions[basis] = index;
        }
    }
    (dims, positions)
}

/// Whether two modules over one algebra have the same representation data.
pub(crate) fn same_representation(a: &Module, b: &Module) -> bool {
    Arc::ptr_eq(a.algebra(), b.algebra())
        && a.dim_vector() == b.dim_vector()
        && a.0.maps == b.0.maps
}

/// Whether two morphisms have the same endpoint and vertex-matrix data.
pub(crate) fn same_morphism_data(a: &Morphism, b: &Morphism) -> bool {
    same_representation(a.source(), b.source())
        && same_representation(a.target(), b.target())
        && (0..a.source().algebra().quiver().num_vertices()).all(|v| a.map_at(v) == b.map_at(v))
}

/// Whether two slices have equal length and match entry by entry.
pub(crate) fn same_slice<T>(left: &[T], right: &[T], same: impl Fn(&T, &T) -> bool) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(a, b)| same(a, b))
}

impl Module {
    fn from_parts(algebra: Arc<Algebra>, dims: Vec<usize>, maps: Vec<DenseMat>) -> Module {
        Module(Arc::new(ModuleInner {
            algebra,
            dims,
            maps,
        }))
    }

    /// Builds a module after checking map shapes, entry canonicity for the
    /// algebra's field, and that every Groebner relation acts as zero.
    pub fn new(
        algebra: Arc<Algebra>,
        dims: Vec<usize>,
        maps: Vec<DenseMat>,
    ) -> Result<Module, ModuleError> {
        hit(Site::ModuleNew);
        let field = algebra.field();
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
            if let Some((row, col)) = map.first_noncanonical(&field) {
                return Err(ModuleError::NonCanonicalEntry { arrow, row, col });
            }
        }
        for (index, relation) in algebra.relations().iter().enumerate() {
            hit(Site::ModuleRelationCheck);
            let source = relation.source() as usize;
            let target = relation.target() as usize;
            let mut acc = DenseMat::zero(dims[source], dims[target]);
            for (coeff, word) in relation.terms() {
                let mut action = DenseMat::identity(dims[source]);
                for &a in word.arrows() {
                    action = action.mul(&maps[a.index()], &field);
                }
                acc.add_scaled_assign(&action, *coeff, &field);
            }
            if !matrix_is_zero(&acc) {
                return Err(ModuleError::RelationActsNonzero { index });
            }
        }
        Ok(Module::from_parts(algebra, dims, maps))
    }

    /// Builds a module from representation data whose relation actions were checked.
    ///
    /// The caller must check every obligation of [`Module::new`]. Debug builds
    /// rerun those checks and reject a false internal certificate.
    pub(crate) fn from_relation_checked(
        algebra: Arc<Algebra>,
        dims: Vec<usize>,
        maps: Vec<DenseMat>,
    ) -> Module {
        debug_assert!(
            Module::new(algebra.clone(), dims.clone(), maps.clone()).is_ok(),
            "from_relation_checked: the representation data does not define a module"
        );
        Module::from_parts(algebra, dims, maps)
    }

    accessor_methods! {
        /// Whether `self` and `other` are clones of one construction, the
        /// identity used for morphism endpoints.
        pub ptr_eq(other: &Module) -> bool = |this| Arc::ptr_eq(&this.0, &other.0);
        /// Address of the shared representation, a hash key for nominal identity.
        ///
        /// Equal addresses mean [`Module::ptr_eq`]. The address is valid only
        /// while a clone stays alive: dropping the last clone frees it for the
        /// next allocation, so a map keyed by it has to hold the module too.
        pub(crate) addr() -> usize = |this| Arc::as_ptr(&this.0) as usize;
    }

    /// The zero module.
    pub fn zero(algebra: &Arc<Algebra>) -> Module {
        let dims = vec![0; algebra.quiver().num_vertices() as usize];
        let maps = zero_maps(algebra, &dims);
        Module::new(algebra.clone(), dims, maps).expect("the zero module is a module")
    }

    /// The simple module `S_v`: one-dimensional at `v`, zero at every other vertex,
    /// with every arrow acting as zero.
    ///
    /// # Panics
    /// Panics if `v` is not a vertex of the algebra's quiver.
    pub fn simple(algebra: &Arc<Algebra>, v: u32) -> Module {
        let quiver = algebra.quiver();
        assert!(v < quiver.num_vertices(), "simple: vertex {v} out of range");
        let dims: Vec<usize> = (0..quiver.num_vertices())
            .map(|w| usize::from(w == v))
            .collect();
        let maps = zero_maps(algebra, &dims);
        Module::new(algebra.clone(), dims, maps).expect("S_v is a module")
    }

    /// The indecomposable projective `P_v = e_v A`: at vertex `w` the basis is the
    /// normal words `v → w`, and an arrow `a` sends the basis word `p` to the
    /// normal form of `p·a`.
    ///
    /// # Panics
    /// Panics if `v` is not a vertex of the algebra's quiver.
    pub fn projective(algebra: &Arc<Algebra>, v: u32) -> Module {
        hit(Site::ModuleProjective);
        let quiver = algebra.quiver();
        let (dims, pos) = basis_data(algebra, v, false, "projective");
        let maps = (0..quiver.num_arrows())
            .map(|i| {
                let a = ArrowId(i as u32);
                let (s, t) = (quiver.source(a), quiver.target(a));
                let mut mat = DenseMat::zero(dims[s as usize], dims[t as usize]);
                for (row, &p) in algebra.paths_between(v, s).iter().enumerate() {
                    for &(q, c) in algebra.right_mul(p, a) {
                        mat.set(row, pos[q], c);
                    }
                }
                mat
            })
            .collect();
        Module::new(algebra.clone(), dims, maps).expect("P_v is a module")
    }

    /// The indecomposable injective `I_v = D(A e_v)`: at vertex `w` the basis is the
    /// dual basis `{p* : p a normal word w → v}`.
    ///
    /// The right action dualizes left multiplication: `(f·a)(x) = f(a·x)`, so for an
    /// arrow `a: w → w'` the matrix entry at row `q ∈ paths(w, v)`, column
    /// `p ∈ paths(w', v)` is the coefficient of `q` in the normal form of `a·p`.
    ///
    /// # Panics
    /// Panics if `v` is not a vertex of the algebra's quiver.
    pub fn injective(algebra: &Arc<Algebra>, v: u32) -> Module {
        hit(Site::ModuleInjective);
        let quiver = algebra.quiver();
        let (dims, pos) = basis_data(algebra, v, true, "injective");
        let maps = (0..quiver.num_arrows())
            .map(|i| {
                let a = ArrowId(i as u32);
                let (s, t) = (quiver.source(a), quiver.target(a));
                let mut mat = DenseMat::zero(dims[s as usize], dims[t as usize]);
                for (col, &p) in algebra.paths_between(t, v).iter().enumerate() {
                    for &(q, c) in algebra.left_mul(a, p) {
                        mat.set(pos[q], col, c);
                    }
                }
                mat
            })
            .collect();
        Module::new(algebra.clone(), dims, maps).expect("I_v is a module")
    }

    accessor_methods! {
        /// The algebra the module lives over.
        pub algebra() -> &Arc<Algebra> = |this| &this.0.algebra;
        /// The algebra's field.
        pub field() -> PrimeField = |this| this.0.algebra.field();
        /// The dimension vector, indexed by vertex.
        pub dim_vector() -> &[usize] = |this| &this.0.dims;
        /// `dim_k M_v`.
        ///
        /// # Panics
        /// Panics if `v` is not a vertex of the algebra's quiver.
        pub dim_at(v: u32) -> usize = |this| this.0.dims[v as usize];
        /// `dim_k M`.
        pub total_dim() -> usize = |this| this.0.dims.iter().sum();
        /// Whether every vertex dimension is zero.
        pub is_zero() -> bool = |this| this.0.dims.iter().all(|&d| d == 0);
        /// The matrix of `a`, `dims[source] × dims[target]`.
        ///
        /// # Panics
        /// Panics if `a` is not an arrow of the algebra's quiver.
        pub map(a: ArrowId) -> &DenseMat = |this| &this.0.maps[a.index()];
    }

    /// The matrix of `word`: the identity for a trivial path, otherwise the
    /// product of the arrow matrices in word order. Errors when `word` is not a
    /// path of this algebra's quiver (see [`PathWord::validate_in`]).
    pub fn word_action(&self, word: &PathWord) -> Result<DenseMat, QuiverError> {
        hit(Site::WordAction);
        word.validate_in(self.0.algebra.quiver())?;
        let field = self.field();
        let mut acc = DenseMat::identity(self.0.dims[word.source() as usize]);
        for &a in word.arrows() {
            acc = acc.mul(&self.0.maps[a.index()], &field);
        }
        Ok(acc)
    }

    /// The matrix of the uniform element `Σ c_i · basis[i]`, `dims[u] × dims[v]`
    /// for the shared source `u` and target `v` of the named basis words.
    ///
    /// # Panics
    /// Panics when `terms` is empty, names a basis index out of range, or
    /// mixes sources or targets.
    pub fn element_action(&self, terms: &[(BasisIdx, Fp)]) -> DenseMat {
        hit(Site::ElementAction);
        assert!(!terms.is_empty(), "element_action: terms are empty");
        let basis = self.0.algebra.basis();
        let source = basis[terms[0].0].source();
        let target = basis[terms[0].0].target();
        let field = self.field();
        let mut acc = DenseMat::zero(self.0.dims[source as usize], self.0.dims[target as usize]);
        for &(index, coeff) in terms {
            let word = &basis[index];
            assert!(
                word.source() == source && word.target() == target,
                "element_action: terms mix sources or targets"
            );
            let action = self
                .word_action(word)
                .expect("algebra basis words are valid in their own quiver");
            acc.add_scaled_assign(&action, coeff, &field);
        }
        acc
    }
}

/// The direct sum with its block inclusions and projections, in summand order.
///
/// `projections[k]` splits `inclusions[k]` (composes to the identity), and
/// `inclusions[j].then(projections[k])` is zero for `j != k`.
///
/// # Panics
/// Panics on an empty slice or when the summands do not share one algebra.
pub fn direct_sum(summands: &[&Module]) -> (Module, Vec<Morphism>, Vec<Morphism>) {
    hit(Site::DirectSum);
    assert!(!summands.is_empty(), "direct_sum: needs a summand");
    let first = summands[0];
    assert!(
        summands[1..]
            .iter()
            .all(|s| Arc::ptr_eq(first.algebra(), s.algebra())),
        "direct_sum: mixed algebras"
    );
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
    let sum = Module::new(first.algebra().clone(), dims, maps)
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
        // The arrow matrices of the sum are block diagonal and these maps are
        // block selections, so both squares hold by construction. See
        // `Morphism::new_unchecked`.
        inclusions.push(Morphism::new_unchecked(s, &sum, incl));
        projections.push(Morphism::new_unchecked(&sum, s, proj));
    }
    (sum, inclusions, projections)
}

/// The ordered sum of modules built at the listed vertices, or zero when empty.
pub(crate) fn summand_sum(
    algebra: &Arc<Algebra>,
    vertices: &[u32],
    build: fn(&Arc<Algebra>, u32) -> Module,
) -> Module {
    match vertices {
        [] => Module::zero(algebra),
        [vertex] => build(algebra, *vertex),
        _ => {
            let parts: Vec<Module> = vertices.iter().map(|&v| build(algebra, v)).collect();
            direct_sum(&parts.iter().collect::<Vec<_>>()).0
        }
    }
}

#[cfg(test)]
mod tests;
