use crate::field::PrimeField;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::profile::{Site, hit};
use crate::quiver::ArrowId;

use super::core::Morphism;
use super::linear::{express_in_row_basis, solve_columns};

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
    let bases = row_space_bases(f, &n.field(), n.algebra().quiver().num_vertices());
    submodule_with_inclusion(n, bases)
}

/// The cokernel of `f` with the projection from `f.target()`.
///
/// At each vertex it is the quotient of `N_v` by the row space of `f_v`.
pub fn cokernel(f: &Morphism) -> (Module, Morphism) {
    hit(Site::HomCokernel);
    let n = f.target();
    let bases = row_space_bases(f, &n.field(), n.algebra().quiver().num_vertices());
    quotient_with_projection(n, &bases)
}

/// Factors `map` through the monomorphism `mono`.
///
/// The caller must prove that `map` lands in the image of `mono`. The
/// factorization is unique because every vertex matrix of `mono` has full row
/// rank.
pub(crate) fn factor_through_monomorphism(mono: &Morphism, map: &Morphism) -> Morphism {
    assert!(
        mono.target().ptr_eq(map.target()),
        "factor_through_monomorphism: targets differ"
    );
    let field = mono.source().field();
    let maps = (0..mono.source().algebra().quiver().num_vertices())
        .map(|vertex| {
            let transposed_mono = mono.map_at(vertex).transpose();
            let value = map.map_at(vertex);
            if value.rows() == 0 {
                return DenseMat::zero(0, transposed_mono.cols());
            }
            transposed_mono
                .solve_many(&value.transpose(), &field)
                .expect("factor_through_monomorphism: map does not land in the monomorphism")
                .transpose()
        })
        .collect();
    Morphism::new(map.source(), mono.source(), maps)
        .expect("a factorization through a module monomorphism is A-linear")
}
