use crate::field::PrimeField;
use crate::homspace::HomSpace;
use crate::linalg::{DenseMat, SparseMat, SparseRow};
use crate::module::Module;
use crate::profile::{Site, hit};
use crate::quiver::ArrowId;

use super::core::{HomError, Morphism, check_parallel};

/// The flat rows of `Hom_A(m, n)`: one row per basis element, the kernel of the
/// commuting-square linear system in the entries of the vertex matrices. For each
/// arrow `a` and each pair `(i, j)`,
/// `Σ_c f_{s(a)}[i][c] · N(a)[c][j] − Σ_r M(a)[i][r] · f_{t(a)}[r][j] = 0`.
///
/// Relations impose no further conditions: both modules already satisfy them, so
/// any solution is `kQ/I`-linear.
///
/// A row is a basis element in flat coordinates. The unknown `f_v[r][c]` is
/// variable `offsets[v] + r * dim N_v + c`. Variables run vertex-major, then
/// row-major inside a vertex: the flattening [`crate::homspace::HomSpace`] stores.
///
/// The order of the rows is part of the contract. [`SparseMat::kernel_basis`]
/// emits one basis vector per free column of the reduced row echelon form, in
/// increasing column order. Two runs over the same pair of modules return the
/// same rows in the same positions. [`crate::homspace::HomSpace`] coordinates and
/// the AR renderings under `tests/golden-ar` inherit this order, and
/// `tests/determinism_ar.rs` compares them byte for byte. Change the variable
/// layout or the free-column order and that gate fails.
pub(crate) fn hom_rows(m: &Module, n: &Module) -> Result<DenseMat, HomError> {
    hit(Site::Hom);
    check_parallel(m, n)?;
    let field = m.field();
    Ok(square_constraints(m, n).kernel_basis(&field).to_dense())
}

/// A basis of `Hom_A(m, n)`, in the order `hom_rows` fixes.
///
/// Materializes every basis morphism. For a dimension only, use [`hom_dim`].
/// For a few basis elements, use [`HomSpace::basis_morphism`].
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
fn square_constraints(m: &Module, n: &Module) -> SparseMat {
    let field = m.field();
    let quiver = m.algebra().quiver();
    let mut total = 0usize;
    let mut offsets = Vec::with_capacity(m.dim_vector().len());
    for (&m_dim, &n_dim) in m.dim_vector().iter().zip(n.dim_vector()) {
        offsets.push(total);
        total += m_dim * n_dim;
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
    SparseMat::from_rows(rows, total)
}

/// `dim_k Hom_A(m, n)`; errors when the modules do not share one algebra, as
/// [`hom`].
///
/// The answer is `columns - rank` of the commuting-square system.
/// [`SparseMat::kernel_basis`] emits one row per free column, so the basis
/// [`hom`] returns has exactly that length.
pub fn hom_dim(m: &Module, n: &Module) -> Result<usize, HomError> {
    hit(Site::HomDim);
    check_parallel(m, n)?;
    let constraints = square_constraints(m, n);
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
    basis
        .transpose()
        .solve_many(&vectors.transpose(), field)
        .expect("vectors lie in the row span of the basis")
        .transpose()
}

/// `X` with `a · X = rhs`, solved column by column.
///
/// # Panics
/// Panics when a column of `rhs` lies outside the column space of `a`.
pub(super) fn solve_columns(a: &DenseMat, rhs: &DenseMat, field: &PrimeField) -> DenseMat {
    hit(Site::SolveColumns);
    a.solve_many(rhs, field)
        .expect("columns lie in the column space")
}
