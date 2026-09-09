use std::sync::Arc;

use crate::field::Fp;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::profile::{Site, hit};
use crate::quiver::ArrowId;

pub(crate) fn matrix_is_zero(matrix: &DenseMat) -> bool {
    (0..matrix.rows()).all(|row| matrix.row(row).iter().all(|value| value.is_zero()))
}

/// Rejected morphism input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HomError {
    /// Source and target live over different algebras (distinct [`Arc`]s).
    DifferentAlgebras,
    /// `maps` needs one matrix per vertex.
    MapCountMismatch { expected: usize, got: usize },
    /// `maps[vertex]` must be `dim M_vertex × dim N_vertex`.
    MapShapeMismatch {
        vertex: u32,
        expected: (usize, usize),
        got: (usize, usize),
    },
    /// `maps[vertex]` has an entry at `(row, col)` not below the field modulus.
    NonCanonicalEntry { vertex: u32, row: usize, col: usize },
    /// The square `f_{s(a)} · N(a) = M(a) · f_{t(a)}` fails at this arrow.
    SquareViolated { arrow: ArrowId },
    /// Composition `f.then(g)` requires the target of `f` and the source of `g`
    /// to be the same module in the sense of [`Module::ptr_eq`].
    EndpointMismatch,
}

display_error! { error HomError {
    Self::DifferentAlgebras => "modules live over different algebras";
    Self::MapCountMismatch { expected, got } => "morphism has {got} maps, quiver has {expected} vertices";
    Self::MapShapeMismatch { vertex, expected, got } => "map at vertex {vertex} is {}x{}, expected {}x{}", got.0, got.1, expected.0, expected.1;
    Self::NonCanonicalEntry { vertex, row, col } => "map at vertex {vertex} has a non-canonical entry at ({row}, {col}) for the modules' field";
    Self::SquareViolated { arrow } => "commuting square fails at arrow {}", arrow.0;
    Self::EndpointMismatch => "target of the first morphism is not the source of the second";
} }

/// An A-linear map between modules over the same algebra.
#[derive(Clone, Debug)]
pub struct Morphism {
    source: Module,
    target: Module,
    // One matrix per vertex, dim source_v × dim target_v.
    maps: Vec<DenseMat>,
}

/// Two morphisms are equal when their endpoints are pointer-identical (see
/// [`Module::ptr_eq`]) and their vertex matrices are equal. Parallel morphisms
/// between separately constructed copies of the same modules never compare equal.
impl PartialEq for Morphism {
    fn eq(&self, other: &Morphism) -> bool {
        self.source.ptr_eq(&other.source)
            && self.target.ptr_eq(&other.target)
            && self.maps == other.maps
    }
}

impl Eq for Morphism {}

pub(super) fn check_parallel(m: &Module, n: &Module) -> Result<(), HomError> {
    if !Arc::ptr_eq(m.algebra(), n.algebra()) {
        return Err(HomError::DifferentAlgebras);
    }
    Ok(())
}

impl Morphism {
    pub(super) fn from_parts(source: &Module, target: &Module, maps: Vec<DenseMat>) -> Morphism {
        Morphism {
            source: source.clone(),
            target: target.clone(),
            maps,
        }
    }

    /// Builds a morphism `m → n` after checking algebra agreement, map shapes,
    /// entry canonicity for the modules' field, and every commuting square.
    pub fn new(
        source: &Module,
        target: &Module,
        maps: Vec<DenseMat>,
    ) -> Result<Morphism, HomError> {
        hit(Site::MorphismNew);
        let (m, n) = (source, target);
        check_parallel(m, n)?;
        let quiver = m.algebra().quiver();
        let num_vertices = quiver.num_vertices() as usize;
        if maps.len() != num_vertices {
            return Err(HomError::MapCountMismatch {
                expected: num_vertices,
                got: maps.len(),
            });
        }
        let field = m.field();
        for (v, map) in maps.iter().enumerate() {
            let expected = (m.dim_at(v as u32), n.dim_at(v as u32));
            let got = (map.rows(), map.cols());
            if got != expected {
                return Err(HomError::MapShapeMismatch {
                    vertex: v as u32,
                    expected,
                    got,
                });
            }
            if let Some((row, col)) = map.first_noncanonical(&field) {
                return Err(HomError::NonCanonicalEntry {
                    vertex: v as u32,
                    row,
                    col,
                });
            }
        }
        for i in 0..quiver.num_arrows() {
            hit(Site::MorphismSquare);
            let arrow = ArrowId(i as u32);
            let (u, v) = (quiver.source(arrow), quiver.target(arrow));
            let left = maps[u as usize].mul(n.map(arrow), &field);
            let right = m.map(arrow).mul(&maps[v as usize], &field);
            if left != right {
                return Err(HomError::SquareViolated { arrow });
            }
        }
        Ok(Morphism::from_parts(source, target, maps))
    }

    /// Builds a morphism `source -> target` from maps the caller has already
    /// proved A-linear, without the checks [`Morphism::new`] runs.
    ///
    /// The caller takes on every obligation `Morphism::new` discharges:
    /// `source` and `target` share one algebra, `maps` holds one matrix per
    /// vertex, `maps[v]` is `dim source_v x dim target_v`, every entry is a
    /// canonical representative for the field, and
    /// `maps[s(a)] · target(a) = source(a) · maps[t(a)]` at every arrow `a`.
    /// Break one and the value is not a morphism.
    ///
    /// Under `debug_assertions` this runs `Morphism::new` on the same
    /// arguments and panics if it rejects them, so `cargo test` checks every
    /// square that a release build skips.
    ///
    /// Every call site states the theorem that discharges the obligations, in
    /// the docstring of the function it sits in. One call site has no such
    /// place: the loop body in [`crate::module::direct_sum`], so its theorem
    /// is here.
    ///
    /// The arrow matrix of the sum is block diagonal:
    /// `sum(a)[off_k[u] + r][off_k[w] + c] = s_k(a)[r][c]` on the diagonal
    /// blocks and zero off them, where `u = s(a)` and `w = t(a)`.
    /// The inclusion `incl_k` selects a block of columns, so
    /// `(incl_{k,u} · sum(a))[i][j] = sum(a)[off_k[u] + i][j]`, which is
    /// `s_k(a)[i][c]` at `j = off_k[w] + c` and zero at every `j` in another
    /// block. That is `(s_k(a) · incl_{k,w})[i][j]` entry for entry. The
    /// projection `prj_k` selects a block of rows, so
    /// `(sum(a) · prj_{k,w})[t][c] = sum(a)[t][off_k[w] + c]`, which is
    /// `s_k(a)[i][c]` at `t = off_k[u] + i` and zero at every `t` in another
    /// block; that is `(prj_{k,u} · s_k(a))[t][c]`. The entries of both are
    /// `0` and `1`, which are canonical for every prime field.
    pub(crate) fn new_unchecked(source: &Module, target: &Module, maps: Vec<DenseMat>) -> Morphism {
        debug_assert!(
            Morphism::new(source, target, maps.clone()).is_ok(),
            "new_unchecked: the maps are not an A-linear map of these modules"
        );
        Morphism::from_parts(source, target, maps)
    }

    accessor_methods! {
        /// The source module.
        pub source() -> &Module = |this| &this.source;
        /// The target module.
        pub target() -> &Module = |this| &this.target;
        /// The matrix at vertex `v`. Panics if `v` is out of range.
        pub map_at(v: u32) -> &DenseMat = |this| &this.maps[v as usize];
    }

    /// The composite "first `self`, then `g`": at each vertex the matrix is
    /// `self_v · g_v`. The result runs from the source of `self` to the target of
    /// `g`.
    ///
    /// Errors with [`HomError::EndpointMismatch`] unless the target of `self` is the
    /// source of `g` in the sense of [`Module::ptr_eq`].
    pub fn then(&self, g: &Morphism) -> Result<Morphism, HomError> {
        hit(Site::MorphismThen);
        if !self.target.ptr_eq(&g.source) {
            return Err(HomError::EndpointMismatch);
        }
        let field = self.source.field();
        let maps = self
            .maps
            .iter()
            .zip(&g.maps)
            .map(|(a, b)| a.mul(b, &field))
            .collect();
        Ok(Morphism::from_parts(&self.source, &g.target, maps))
    }

    /// Whether every vertex matrix is square and invertible.
    pub fn is_isomorphism(&self) -> bool {
        let field = self.source.field();
        self.maps
            .iter()
            .all(|m| m.rows() == m.cols() && m.rank(&field) == m.rows())
    }

    /// The image of a module element given as one row vector per vertex.
    ///
    /// # Panics
    /// Panics when `element` does not hold one vector per vertex, or when a vector's
    /// length differs from the source dimension at its vertex.
    pub fn apply(&self, element: &[Vec<Fp>]) -> Vec<Vec<Fp>> {
        assert_eq!(
            element.len(),
            self.maps.len(),
            "apply: needs one vector per vertex"
        );
        let field = self.source.field();
        self.maps
            .iter()
            .zip(element)
            .map(|(map, x)| map.transpose().mul_vec(x, &field))
            .collect()
    }

    /// Whether every vertex matrix is zero.
    pub fn is_zero(&self) -> bool {
        self.maps.iter().all(matrix_is_zero)
    }
}

/// The identity morphism on `m`.
pub fn identity(m: &Module) -> Morphism {
    let maps = m
        .dim_vector()
        .iter()
        .map(|&d| DenseMat::identity(d))
        .collect();
    Morphism::from_parts(m, m, maps)
}

/// The zero morphism `m → n`; errors when the modules do not share one algebra
/// (the same [`Arc`]).
pub fn zero_morphism(m: &Module, n: &Module) -> Result<Morphism, HomError> {
    check_parallel(m, n)?;
    let maps = m
        .dim_vector()
        .iter()
        .zip(n.dim_vector())
        .map(|(&a, &b)| DenseMat::zero(a, b))
        .collect();
    Ok(Morphism::from_parts(m, n, maps))
}
