//! Morphisms of right modules, the Hom functor, and kernels, images, and cokernels.
//!
//! A morphism `f: M → N` stores one `dim M_v × dim N_v` matrix per vertex, acting on
//! row vectors (`x ↦ x f_v`). A-linearity is the commuting square
//! `f_{s(a)} · N(a) = M(a) · f_{t(a)}` for every arrow `a`: applying `f` and then
//! acting sends a row vector `x ∈ M_{s(a)}` to `x f_{s(a)} N(a)`, while acting and
//! then applying `f` sends it to `x M(a) f_{t(a)}`.
//!
//! A [`Morphism`] carries its source and target [`Module`]s (cheap clones) alongside
//! its vertex matrices. [`Morphism::new`] checks the squares against those modules, so
//! a `Morphism` from a constructor in this module is A-linear for the modules it was
//! built with. Composition, kernels, images, and cokernels take their endpoints from
//! the morphism itself. Endpoints compare by the nominal identity of
//! [`Module::ptr_eq`], never structurally.

use std::fmt;
use std::sync::Arc;

use crate::field::{Fp, PrimeField};
use crate::homspace::HomSpace;
use crate::linalg::{DenseMat, SparseMat, SparseRow};
use crate::module::Module;
use crate::profile::{Site, hit};
use crate::quiver::ArrowId;

/// Rejected morphism input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HomError {
    /// Source and target live over different algebras (distinct [`Arc`]s).
    /// The field comes from the algebra, so a shared algebra implies a
    /// shared field.
    DifferentAlgebras,
    /// `maps` needs one matrix per vertex.
    MapCountMismatch { expected: usize, got: usize },
    /// `maps[vertex]` must be `dim M_vertex × dim N_vertex`.
    MapShapeMismatch {
        vertex: u32,
        expected: (usize, usize),
        got: (usize, usize),
    },
    /// `maps[vertex]` holds an entry at `(row, col)` whose representative is not
    /// canonical for the modules' field, meaning it is not below the modulus.
    /// Such an entry comes from arithmetic over some other field.
    NonCanonicalEntry { vertex: u32, row: usize, col: usize },
    /// The square `f_{s(a)} · N(a) = M(a) · f_{t(a)}` fails at this arrow.
    SquareViolated { arrow: ArrowId },
    /// Composition `f.then(g)` requires the target of `f` and the source of `g`
    /// to be the same module in the sense of [`Module::ptr_eq`].
    EndpointMismatch,
}

impl fmt::Display for HomError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DifferentAlgebras => f.write_str("modules live over different algebras"),
            Self::MapCountMismatch { expected, got } => {
                write!(f, "morphism has {got} maps, quiver has {expected} vertices")
            }
            Self::MapShapeMismatch {
                vertex,
                expected,
                got,
            } => write!(
                f,
                "map at vertex {vertex} is {}x{}, expected {}x{}",
                got.0, got.1, expected.0, expected.1
            ),
            Self::NonCanonicalEntry { vertex, row, col } => write!(
                f,
                "map at vertex {vertex} has a non-canonical entry at ({row}, {col}) for the modules' field"
            ),
            Self::SquareViolated { arrow } => {
                write!(f, "commuting square fails at arrow {}", arrow.0)
            }
            Self::EndpointMismatch => {
                f.write_str("target of the first morphism is not the source of the second")
            }
        }
    }
}

impl std::error::Error for HomError {}

/// An A-linear map between right modules over the same algebra, carrying
/// its endpoints.
#[derive(Clone, Debug)]
pub struct Morphism {
    source: Module,
    target: Module,
    // One matrix per vertex, dim source_v × dim target_v, acting on row vectors.
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

fn check_parallel(m: &Module, n: &Module) -> Result<(), HomError> {
    if !Arc::ptr_eq(m.algebra(), n.algebra()) {
        return Err(HomError::DifferentAlgebras);
    }
    Ok(())
}

impl Morphism {
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
        }
        let field = m.field();
        for (v, map) in maps.iter().enumerate() {
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
        Ok(Morphism {
            source: source.clone(),
            target: target.clone(),
            maps,
        })
    }

    /// Builds a morphism `source -> target` from maps the caller has already
    /// proved A-linear, without the checks [`Morphism::new`] runs.
    ///
    /// The caller takes on every obligation `Morphism::new` discharges:
    /// `source` and `target` share one algebra, `maps` holds one matrix per
    /// vertex, `maps[v]` is `dim source_v x dim target_v`, every entry is a
    /// canonical representative for the field, and
    /// `maps[s(a)] · target(a) = source(a) · maps[t(a)]` at every arrow `a`.
    /// Break one and the value is not a morphism, and everything downstream
    /// of it is wrong rather than rejected.
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
        Morphism {
            source: source.clone(),
            target: target.clone(),
            maps,
        }
    }

    /// The source module.
    #[inline]
    pub fn source(&self) -> &Module {
        &self.source
    }

    /// The target module.
    #[inline]
    pub fn target(&self) -> &Module {
        &self.target
    }

    /// The matrix at vertex `v`. Panics if `v` is out of range.
    #[inline]
    pub fn map_at(&self, v: u32) -> &DenseMat {
        &self.maps[v as usize]
    }

    /// The composite "first `self`, then `g`": at each vertex the row-vector actions
    /// chain as `x ↦ (x · self_v) · g_v`, so the matrix is `self_v · g_v`. The result
    /// runs from the source of `self` to the target of `g`.
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
        Ok(Morphism {
            source: self.source.clone(),
            target: g.target.clone(),
            maps,
        })
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
        self.maps
            .iter()
            .all(|m| (0..m.rows()).all(|r| m.row(r).iter().all(|v| v.is_zero())))
    }
}

/// The identity morphism on `m`.
pub fn identity(m: &Module) -> Morphism {
    let maps = m
        .dim_vector()
        .iter()
        .map(|&d| DenseMat::identity(d))
        .collect();
    Morphism {
        source: m.clone(),
        target: m.clone(),
        maps,
    }
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
    Ok(Morphism {
        source: m.clone(),
        target: n.clone(),
        maps,
    })
}

/// The flat rows of `Hom_A(m, n)`: one row per basis element, the kernel of the
/// commuting-square linear system in the entries of the vertex matrices. For each
/// arrow `a` and each pair `(i, j)`,
/// `Σ_c f_{s(a)}[i][c] · N(a)[c][j] − Σ_r M(a)[i][r] · f_{t(a)}[r][j] = 0`.
///
/// Relations impose no further conditions: both modules already satisfy them, so any
/// solution is automatically `kQ/I`-linear.
///
/// A row is a basis element in flat coordinates. The unknown `f_v[r][c]` is
/// variable `offsets[v] + r * dim N_v + c`, so variables run vertex-major, then
/// row-major inside a vertex, which is the flattening
/// [`crate::homspace::HomSpace`] stores. Unflattening one row costs one
/// `Morphism`, so a caller that wants only a dimension pays for none.
///
/// The order of the rows is part of the contract. [`SparseMat::kernel_basis`] emits
/// one basis vector per free column of the reduced row echelon form, in increasing
/// column order. Two runs over the same pair of modules therefore return the same
/// rows in the same positions. [`crate::homspace::HomSpace`] coordinates and the AR
/// renderings committed under `tests/golden-ar` inherit this order, and
/// `tests/determinism_ar.rs` compares them byte for byte. Change the variable layout
/// or the free-column order and that gate fails.
pub(crate) fn hom_rows(m: &Module, n: &Module) -> Result<DenseMat, HomError> {
    hit(Site::Hom);
    check_parallel(m, n)?;
    let field = m.field();
    let (constraints, _) = square_constraints(m, n);
    let kernel = constraints.kernel_basis(&field);
    let mut rows = DenseMat::zero(kernel.rows(), constraints.cols());
    for r in 0..kernel.rows() {
        for &(idx, val) in kernel.row(r).entries() {
            rows.set(r, idx, val);
        }
    }
    Ok(rows)
}

/// A basis of `Hom_A(m, n)`, in the order `hom_rows` fixes.
///
/// It materializes every basis morphism. A caller that reads only a dimension
/// wants [`hom_dim`], and one that reads a few basis elements wants
/// [`HomSpace::basis_morphism`].
pub fn hom(m: &Module, n: &Module) -> Result<Vec<Morphism>, HomError> {
    Ok(HomSpace::new(m, n)?.into_basis())
}

/// The commuting-square system of `Hom_A(m, n)` and the variable offsets, one
/// per vertex.
///
/// The unknown `f_v[r][c]` is variable `offsets[v] + r * dim N_v + c`, and the
/// matrix has one column per unknown. Row `(a, i, j)` is entry `(i, j)` of
/// `f_{s(a)} · N(a) − M(a) · f_{t(a)}`. Rows that are identically zero are
/// dropped: they constrain nothing, and dropping them leaves the row space,
/// the rank, and the kernel unchanged.
///
/// Both callers rely on the column order, which is the order of the Hom basis
/// [`hom`] documents.
fn square_constraints(m: &Module, n: &Module) -> (SparseMat, Vec<usize>) {
    let field = m.field();
    let quiver = m.algebra().quiver();
    let num_vertices = quiver.num_vertices() as usize;
    let mut offsets = Vec::with_capacity(num_vertices);
    let mut total = 0usize;
    for v in 0..num_vertices {
        offsets.push(total);
        total += m.dim_vector()[v] * n.dim_vector()[v];
    }
    let mut rows = Vec::new();
    for idx in 0..quiver.num_arrows() {
        let arrow = ArrowId(idx as u32);
        let (u, v) = (quiver.source(arrow) as usize, quiver.target(arrow) as usize);
        let ma = m.map(arrow);
        let na = n.map(arrow);
        for i in 0..m.dim_vector()[u] {
            for j in 0..n.dim_vector()[v] {
                let mut entries = Vec::new();
                for c in 0..n.dim_vector()[u] {
                    let val = na.get(c, j);
                    if !val.is_zero() {
                        entries.push((offsets[u] + i * n.dim_vector()[u] + c, val));
                    }
                }
                for r in 0..m.dim_vector()[v] {
                    let val = ma.get(i, r);
                    if !val.is_zero() {
                        entries.push((offsets[v] + r * n.dim_vector()[v] + j, field.neg(val)));
                    }
                }
                let row = SparseRow::from_entries(entries, &field);
                if !row.is_zero() {
                    rows.push(row);
                }
            }
        }
    }
    (SparseMat::from_rows(rows, total), offsets)
}

/// `dim_k Hom_A(m, n)`; errors when the modules do not share one algebra, as
/// [`hom`].
///
/// The answer is `columns - rank` of the commuting-square system.
/// [`SparseMat::kernel_basis`] emits one row per free column, so the basis
/// [`hom`] returns has exactly that length. Rank needs the forward
/// elimination alone, where a basis needs the back substitution, the kernel
/// rows, and one `Morphism` per row.
pub fn hom_dim(m: &Module, n: &Module) -> Result<usize, HomError> {
    hit(Site::HomDim);
    check_parallel(m, n)?;
    let (constraints, _) = square_constraints(m, n);
    Ok(constraints.cols() - constraints.rank(&m.field()))
}

/// Coordinates of each row of `vectors` in the row basis `basis`: the matrix `X`
/// with `X · basis = vectors`.
///
/// # Panics
/// Panics when a row of `vectors` lies outside the row span of `basis`.
pub(crate) fn express_in_row_basis(
    basis: &DenseMat,
    vectors: &DenseMat,
    field: &PrimeField,
) -> DenseMat {
    hit(Site::ExpressInRowBasis);
    let bt = basis.transpose();
    let mut out = DenseMat::zero(vectors.rows(), basis.rows());
    for r in 0..vectors.rows() {
        let x = bt
            .solve(vectors.row(r), field)
            .expect("vector lies in the row span of the basis");
        for (c, &v) in x.iter().enumerate() {
            out.set(r, c, v);
        }
    }
    out
}

/// `X` with `a · X = rhs`, solved column by column.
///
/// # Panics
/// Panics when a column of `rhs` lies outside the column space of `a`.
fn solve_columns(a: &DenseMat, rhs: &DenseMat, field: &PrimeField) -> DenseMat {
    hit(Site::SolveColumns);
    let rt = rhs.transpose();
    let mut out = DenseMat::zero(a.cols(), rhs.cols());
    for j in 0..rhs.cols() {
        let x = a
            .solve(rt.row(j), field)
            .expect("column lies in the column space");
        for (i, &v) in x.iter().enumerate() {
            out.set(i, j, v);
        }
    }
    out
}

/// The submodule of `parent` spanned at each vertex by the rows of `bases[v]`,
/// together with its inclusion.
///
/// Write `M(a)` for the arrow matrix of `parent`. The rows of `bases[v]` must be
/// canonical for the parent's field and linearly independent, and their row
/// spaces must form an A-invariant family. The induced arrow map `S(a)` solves
/// `S(a) · bases[t(a)] = bases[s(a)] · M(a)`.
///
/// Independence is a precondition the caller carries, checked only under
/// `debug_assertions`. It is what makes `S(a)` the unique solution and what
/// carries the relations: from `S(a) · bases[t(a)] = bases[s(a)] · M(a)` at every
/// arrow, a relation `ρ` gives `S(ρ) · bases[t(ρ)] = bases[s(ρ)] · M(ρ) = 0`, and
/// only a full-rank `bases[t(ρ)]` cancels on the left to leave `S(ρ) = 0`. With
/// dependent rows the solve still succeeds and `S(a)` is any of several answers.
///
/// The inclusion is `bases` itself and skips the checks of [`Morphism::new`]. Its
/// square at `a` reads `bases[s(a)] · M(a) = S(a) · bases[t(a)]`, which is the
/// equation [`express_in_row_basis`] solved, and that solve panics rather than
/// return a vector outside the row span. The shapes are right because `bases[v]`
/// is `dims[v] x dim parent_v`, and the entries are the caller's own canonical
/// ones.
pub(crate) fn submodule_with_inclusion(
    parent: &Module,
    bases: Vec<DenseMat>,
) -> (Module, Morphism) {
    hit(Site::Submodule);
    let field = parent.field();
    let quiver = parent.algebra().quiver();
    debug_assert!(
        bases.iter().all(|b| b.rank(&field) == b.rows()),
        "submodule_with_inclusion: the spanning rows are not linearly independent"
    );
    let dims: Vec<usize> = bases.iter().map(DenseMat::rows).collect();
    let maps = (0..quiver.num_arrows())
        .map(|i| {
            let a = ArrowId(i as u32);
            let (u, v) = (quiver.source(a) as usize, quiver.target(a) as usize);
            let image = bases[u].mul(parent.map(a), &field);
            express_in_row_basis(&bases[v], &image, &field)
        })
        .collect();
    let sub = Module::new(parent.algebra().clone(), dims, maps)
        .expect("a submodule of a module is a module");
    let inclusion = Morphism::new_unchecked(&sub, parent, bases);
    (sub, inclusion)
}

/// The quotient of `parent` by the subspaces spanned at each vertex by the rows of
/// `bases[v]`, together with its projection.
///
/// Write `M(a)` for the arrow matrix of `parent`. The row spaces of `bases` must
/// form an A-invariant family. The projection matrix is
/// `Q_v = (right kernel of bases[v])ᵀ`: `x · Q_v = 0` exactly on the subspace, and
/// `Q_v` has full column rank, so `x ↦ x Q_v` is a surjection whose kernel is the
/// subspace. Invariance makes `M(a) · Q_{t(a)}` land in the column space of
/// `Q_{s(a)}`, and the induced map solves `Q_{s(a)} · C(a) = M(a) · Q_{t(a)}`.
///
/// Full column rank is not a caller precondition here: each column of `Q_v` is a
/// row of [`DenseMat::kernel_basis`], which carries a 1 in its own free column,
/// so the columns are independent. It is what makes `C(a)` unique and what carries
/// the relations, since only a full-column-rank `Q_{s(ρ)}` cancels on the right of
/// `Q_{s(ρ)} · C(ρ) = M(ρ) · Q_{t(ρ)} = 0`. A `debug_assert` holds
/// `kernel_basis` to it.
///
/// The projection is `projections` itself and skips the checks of
/// [`Morphism::new`]. Its square at `a` reads `Q_{s(a)} · C(a) = M(a) · Q_{t(a)}`,
/// which is the equation [`solve_columns`] solved, and that solve panics rather
/// than return a column outside the column space. The shapes are right because
/// `Q_v` is `dim parent_v x dims[v]`, and the entries come from `kernel_basis` and
/// `solve` over the parent's own field.
pub(crate) fn quotient_with_projection(parent: &Module, bases: &[DenseMat]) -> (Module, Morphism) {
    hit(Site::Quotient);
    let field = parent.field();
    let quiver = parent.algebra().quiver();
    let projections: Vec<DenseMat> = bases
        .iter()
        .map(|b| b.kernel_basis(&field).transpose())
        .collect();
    debug_assert!(
        projections.iter().all(|q| q.rank(&field) == q.cols()),
        "quotient_with_projection: the projection columns are not linearly independent"
    );
    let dims: Vec<usize> = projections.iter().map(DenseMat::cols).collect();
    let maps = (0..quiver.num_arrows())
        .map(|i| {
            let a = ArrowId(i as u32);
            let (u, v) = (quiver.source(a) as usize, quiver.target(a) as usize);
            let rhs = parent.map(a).mul(&projections[v], &field);
            solve_columns(&projections[u], &rhs, &field)
        })
        .collect();
    let quotient = Module::new(parent.algebra().clone(), dims, maps)
        .expect("a quotient of a module is a module");
    let projection = Morphism::new_unchecked(parent, &quotient, projections);
    (quotient, projection)
}

fn row_space_bases(f: &Morphism, field: &PrimeField, num_vertices: u32) -> Vec<DenseMat> {
    (0..num_vertices)
        .map(|v| f.map_at(v).row_space_basis(field))
        .collect()
}

/// The kernel of `f` with its inclusion into `f.source()`.
///
/// At each vertex the kernel of the row action `x ↦ x f_v` is the left null space of
/// `f_v`, that is, the right null space of `f_vᵀ`.
pub fn kernel(f: &Morphism) -> (Module, Morphism) {
    hit(Site::HomKernel);
    let m = f.source();
    let field = m.field();
    let bases: Vec<DenseMat> = (0..m.algebra().quiver().num_vertices())
        .map(|v| f.map_at(v).transpose().kernel_basis(&field))
        .collect();
    submodule_with_inclusion(m, bases)
}

/// The image of `f` with its inclusion into `f.target()`.
///
/// At each vertex the image of the row action is the row space of `f_v`.
pub fn image(f: &Morphism) -> (Module, Morphism) {
    hit(Site::HomImage);
    let n = f.target();
    let field = n.field();
    let bases = row_space_bases(f, &field, n.algebra().quiver().num_vertices());
    submodule_with_inclusion(n, bases)
}

/// The cokernel of `f` with the projection from `f.target()`.
///
/// At each vertex it is the quotient of `N_v` by the row space of `f_v`.
pub fn cokernel(f: &Morphism) -> (Module, Morphism) {
    hit(Site::HomCokernel);
    let n = f.target();
    let field = n.field();
    let bases = row_space_bases(f, &field, n.algebra().quiver().num_vertices());
    quotient_with_projection(n, &bases)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{an_with_relations, dual_numbers, linear_an};
    use crate::module::direct_sum;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    // dim Hom(P_v, M) = dim M_v: Yoneda for right modules, Hom(e_v A, M) ≅ M e_v.
    #[test]
    fn hom_from_projective_has_the_dimension_of_the_module_at_the_vertex() {
        let field = f5();
        for algebra in [
            linear_an(3, field),
            an_with_relations(3, &[(0, 2)], field).unwrap(),
            dual_numbers(field),
        ] {
            let n = algebra.quiver().num_vertices();
            let mut modules: Vec<Module> = Vec::new();
            for v in 0..n {
                modules.push(Module::simple(&algebra, v));
                modules.push(Module::projective(&algebra, v));
                modules.push(Module::injective(&algebra, v));
            }
            let parts: Vec<&Module> = modules.iter().take(3).collect();
            let (sum, _, _) = direct_sum(&parts);
            modules.push(sum);
            for v in 0..n {
                let pv = Module::projective(&algebra, v);
                for m in &modules {
                    assert_eq!(
                        hom(&pv, m).unwrap().len(),
                        m.dim_at(v),
                        "hom(P_{v}, M) with dim M = {:?}",
                        m.dim_vector()
                    );
                }
            }
        }
    }

    #[test]
    fn hom_between_simples_is_delta() {
        let field = f5();
        let algebra = linear_an(3, field);
        for i in 0..3 {
            for j in 0..3 {
                let si = Module::simple(&algebra, i);
                let sj = Module::simple(&algebra, j);
                assert_eq!(
                    hom_dim(&si, &sj).unwrap(),
                    usize::from(i == j),
                    "hom(S_{i}, S_{j})"
                );
            }
        }
    }

    // Right-module Yoneda gives Hom(P_v, M) ≅ M_v. For linearly oriented A_2 (arrow
    // 0 → 1), P_0 = e_0 A has dimension vector (1, 1) and P_1 has (0, 1), so
    // Hom(P_0, P_1) ≅ (P_1)_0 = 0 while Hom(P_1, P_0) ≅ (P_0)_1 = k: the nonzero map
    // sends e_1 to the path a, so it runs P_1 → P_0, opposite to the left-module
    // convention. Hence End(P_0 ⊕ P_1) = End(P_0) ⊕ End(P_1) ⊕ Hom(P_1, P_0) = k³.
    #[test]
    fn endomorphisms_of_p0_plus_p1_over_a2_have_dimension_3() {
        let field = f5();
        let algebra = linear_an(2, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        assert_eq!(hom_dim(&p0, &p1).unwrap(), 0);
        assert_eq!(hom_dim(&p1, &p0).unwrap(), 1);
        let (sum, _, _) = direct_sum(&[&p0, &p1]);
        assert_eq!(hom_dim(&sum, &sum).unwrap(), 3);
    }

    #[test]
    fn hom_rejects_modules_over_different_algebras() {
        let field = f5();
        let a = linear_an(3, field);
        let b = linear_an(3, field);
        let m = Module::simple(&a, 0);
        let n = Module::simple(&b, 0);
        assert_eq!(hom(&m, &n).unwrap_err(), HomError::DifferentAlgebras);
    }

    #[test]
    fn hom_rejects_modules_over_different_fields() {
        // The field lives on the algebra, so modules over different fields
        // always live over different algebra values.
        let a = linear_an(3, f5());
        let b = linear_an(3, PrimeField::new(7).unwrap());
        let m = Module::simple(&a, 0);
        let n = Module::simple(&b, 0);
        assert_eq!(hom(&m, &n).unwrap_err(), HomError::DifferentAlgebras);
    }

    #[test]
    fn then_rejects_mismatched_endpoints() {
        let field = f5();
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let s0 = Module::simple(&algebra, 0);
        let f = hom(&p0, &s0).unwrap().remove(0);
        // A separately constructed copy of S_0 is nominally a different module.
        let s0_copy = Module::simple(&algebra, 0);
        assert_eq!(
            f.then(&identity(&s0_copy)).unwrap_err(),
            HomError::EndpointMismatch
        );
        assert!(f.then(&identity(&s0)).is_ok());
    }

    #[test]
    fn morphism_equality_requires_pointer_identical_endpoints() {
        let field = f5();
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p0_copy = Module::projective(&algebra, 0);
        assert!(!p0.ptr_eq(&p0_copy));
        assert!(p0.ptr_eq(&p0.clone()));
        assert_ne!(identity(&p0), identity(&p0_copy));
        assert_eq!(identity(&p0), identity(&p0.clone()));
    }

    #[test]
    fn morphism_new_rejects_a_non_canonical_entry() {
        let algebra = linear_an(2, PrimeField::new(2).unwrap());
        let p0 = Module::projective(&algebra, 0);
        // The entry 3 comes from F_5; it is not a canonical F_2 representative.
        let bad = DenseMat::from_rows(&[vec![f5().elem(3)]]);
        let maps = vec![bad, DenseMat::identity(1)];
        assert_eq!(
            Morphism::new(&p0, &p0, maps).unwrap_err(),
            HomError::NonCanonicalEntry {
                vertex: 0,
                row: 0,
                col: 0,
            }
        );
    }

    #[test]
    fn morphism_new_rejects_a_noncommuting_square() {
        let field = f5();
        let algebra = linear_an(2, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        // The square at arrow 0 needs f_0 · N(a) = M(a) · f_1 = [1], but f_0 is 1x0,
        // so the left side is the 1x1 zero matrix.
        let maps = vec![DenseMat::zero(1, 0), DenseMat::identity(1)];
        assert_eq!(
            Morphism::new(&p0, &p1, maps).unwrap_err(),
            HomError::SquareViolated { arrow: ArrowId(0) }
        );
    }

    #[test]
    fn identity_is_neutral_for_composition() {
        let field = f5();
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let s0 = Module::simple(&algebra, 0);
        let f = hom(&p0, &s0).unwrap().remove(0);
        assert_eq!(identity(&p0).then(&f).unwrap(), f);
        assert_eq!(f.then(&identity(&s0)).unwrap(), f);
        assert!(zero_morphism(&p0, &s0).unwrap().is_zero());
        assert!(!f.is_zero());
    }

    #[test]
    fn the_nonzero_map_p0_to_i2_over_a3_is_an_isomorphism() {
        // Over linearly oriented A_3 both P_0 and I_2 are the unique uniserial with
        // dimension vector (1, 1, 1), so the one-dimensional Hom is spanned by an iso.
        let field = f5();
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let i2 = Module::injective(&algebra, 2);
        let basis = hom(&p0, &i2).unwrap();
        assert_eq!(basis.len(), 1);
        assert!(basis[0].is_isomorphism());
        assert!(!zero_morphism(&p0, &p0).unwrap().is_isomorphism());
        assert!(identity(&p0).is_isomorphism());
    }

    #[test]
    fn apply_maps_row_vectors_through_the_vertex_matrices() {
        let field = f5();
        let algebra = linear_an(2, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let f = hom(&p1, &p0).unwrap().remove(0);
        let element = vec![vec![], vec![field.elem(2)]];
        let image = f.apply(&element);
        // The output at vertex 0 lives in (P_0)_0, which is one-dimensional.
        assert_eq!(image[0], vec![field.zero()]);
        let expected = field.mul(field.elem(2), f.map_at(1).get(0, 0));
        assert_eq!(image[1], vec![expected]);
    }

    #[test]
    fn kernel_image_cokernel_satisfy_rank_nullity_and_compose_correctly() {
        let field = f5();
        let cases: Vec<(Module, Module)> = {
            let a3 = linear_an(3, field);
            let dn = dual_numbers(field);
            let p0 = Module::projective(&a3, 0);
            let p1 = Module::projective(&a3, 1);
            let s0 = Module::simple(&a3, 0);
            let i2 = Module::injective(&a3, 2);
            let (sum, _, _) = direct_sum(&[&p0, &p1]);
            let dp = Module::projective(&dn, 0);
            vec![
                (p0.clone(), s0),
                (p0.clone(), i2),
                (sum, p0),
                (dp.clone(), dp),
            ]
        };
        for (m, n) in &cases {
            for f in hom(m, n).unwrap() {
                let (ker, ker_incl) = kernel(&f);
                let (im, im_incl) = image(&f);
                let (coker, coker_proj) = cokernel(&f);
                for v in 0..m.algebra().quiver().num_vertices() {
                    assert_eq!(ker.dim_at(v) + im.dim_at(v), m.dim_at(v), "vertex {v}");
                    assert_eq!(im.dim_at(v) + coker.dim_at(v), n.dim_at(v), "vertex {v}");
                }
                assert_eq!(ker_incl.then(&f).unwrap(), zero_morphism(&ker, n).unwrap());
                assert_eq!(
                    f.then(&coker_proj).unwrap(),
                    zero_morphism(m, &coker).unwrap()
                );
                // The corestriction c: m → im recovers f as c.then(im_incl). This
                // certifies that im carries the image with its inclusion.
                let corestriction_maps = (0..m.algebra().quiver().num_vertices())
                    .map(|v| express_in_row_basis(im_incl.map_at(v), f.map_at(v), &field))
                    .collect();
                let corestriction = Morphism::new(m, &im, corestriction_maps).unwrap();
                assert_eq!(corestriction.then(&im_incl).unwrap(), f);
            }
        }
    }
}
