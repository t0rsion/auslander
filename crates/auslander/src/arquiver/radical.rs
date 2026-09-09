use crate::decompose::inverse_morphism;
use crate::endo::EndoAlgebra;
use crate::field::Fp;
use crate::hom::Morphism;
use crate::homspace::{HomQuotient, HomSpace, HomSpaceError, HomSubspace};
use crate::indec::IndecomposableModule;
use crate::iso::indecomposable_iso;
use crate::linalg::DenseMat;
use crate::module::Module;

use super::{ArQuiverError, IndecomposableCatalog};

/// The morphisms `f` in `space` with `f.then(u)` in the radical of `endo`.
///
/// `endo` must be the endomorphism algebra of the source module of `space`,
/// and `u` must run from the target module of `space` to that same source
/// module.
pub(crate) fn radical_against_iso(
    space: &HomSpace,
    endo: &EndoAlgebra,
    u: &Morphism,
) -> Result<HomSubspace, ArQuiverError> {
    let field = space.source().field();
    let radical = endo.radical_basis();
    let mut rows: Vec<Vec<Fp>> = Vec::with_capacity(space.dim() + radical.rows());
    for f in space.basis() {
        rows.push(endo.coords(&f.then(u)?));
    }
    for r in 0..radical.rows() {
        rows.push(radical.row(r).to_vec());
    }
    let stacked = DenseMat::from_rows_with_cols(&rows, endo.dim());
    // The stacked matrix holds one row per composite and then the radical
    // basis. A row (l | m) of its left null space says that the composite
    // combined by l equals the radical element combined by -m, so l runs
    // over the solutions of the radical condition.
    let kernel = stacked.left_kernel_basis(&field);
    let spanning: Vec<Morphism> = (0..kernel.rows())
        .map(|k| space.morphism(&kernel.row(k)[..space.dim()]))
        .collect();
    Ok(space.subspace(&spanning)?)
}

/// The radical `rad(X, Y)` of the module category between two certified
/// indecomposables, as a subspace of `Hom(X, Y)`.
///
/// Non-isomorphic endpoints give the whole Hom space. Isomorphic endpoints
/// give the maps `f` with `f.then(u)` in `rad End(X)`, where `u: Y -> X` is the
/// inverse of the first isomorphism `X -> Y` found by the deterministic scan of
/// the radical criterion. The subspace does not depend on that choice, as the
/// module documentation explains.
///
/// # Errors
/// [`ArQuiverError::Hom`] when the two modules do not share one algebra.
pub fn category_radical(
    x: &IndecomposableModule,
    y: &IndecomposableModule,
) -> Result<HomSubspace, ArQuiverError> {
    let space = HomSpace::new(x.module(), y.module())?;
    let Some(h) = indecomposable_iso(x.module(), y.module(), x.endo()) else {
        return Ok(space.full_subspace());
    };
    let u = inverse_morphism(&h).expect("the radical criterion returns an isomorphism");
    radical_against_iso(&space, x.endo(), &u)
}

/// The span of the composites `f.then(g)` over the given pairs of subspaces,
/// as a subspace of `Hom(source, target)`.
pub(crate) fn span_of_composites<'a>(
    source: &Module,
    target: &Module,
    factorizations: impl Iterator<Item = (&'a HomSubspace, &'a HomSubspace)>,
) -> Result<HomSubspace, ArQuiverError> {
    let mut composites = Vec::new();
    for (left, right) in factorizations {
        for i in 0..left.dim() {
            let f = left.basis_morphism(i);
            for j in 0..right.dim() {
                composites.push(f.then(&right.basis_morphism(j))?);
            }
        }
    }
    Ok(HomSubspace::spanned_by(source, target, &composites)?)
}

/// `rad^2(X, Y)`: the sum over the catalog entries `Z` of the composites of
/// `rad(X, Z)` with `rad(Z, Y)`, as a subspace of `Hom(X, Y)`.
///
/// The catalog is complete, so the sum is the whole square of the radical,
/// not a lower bound. The summation runs in catalog order; the result is a
/// span, so the order does not change it.
///
/// # Errors
/// [`ArQuiverError::Hom`] when `x`, `y` and the catalog do not share one
/// algebra.
pub fn radical_square_through_catalog(
    catalog: &IndecomposableCatalog,
    x: &IndecomposableModule,
    y: &IndecomposableModule,
) -> Result<HomSubspace, ArQuiverError> {
    let mut legs = Vec::with_capacity(catalog.len());
    for z in catalog.entries() {
        legs.push((category_radical(x, z)?, category_radical(z, y)?));
    }
    span_of_composites(
        x.module(),
        y.module(),
        legs.iter().map(|(left, right)| (left, right)),
    )
}

/// `Irr(X, Y) = rad(X, Y) / rad^2(X, Y)`, with the deterministic complement
/// representatives of [`HomQuotient`]. The nonzero elements are the classes
/// of the irreducible maps `X -> Y`.
///
/// # Errors
/// [`ArQuiverError::Hom`] when `x`, `y` and the catalog do not share one
/// algebra, and [`ArQuiverError::RadicalSquareNotContained`] when the square
/// leaves the radical, which is a crate defect.
pub fn irreducible_quotient(
    catalog: &IndecomposableCatalog,
    x: &IndecomposableModule,
    y: &IndecomposableModule,
) -> Result<HomQuotient, ArQuiverError> {
    let radical = category_radical(x, y)?;
    let square = radical_square_through_catalog(catalog, x, y)?;
    quotient_or_defect(&radical, &square)
}

pub(crate) fn quotient_or_defect(
    radical: &HomSubspace,
    square: &HomSubspace,
) -> Result<HomQuotient, ArQuiverError> {
    radical.quotient_by(square).map_err(|error| match error {
        HomSpaceError::NotContained => ArQuiverError::RadicalSquareNotContained {
            source: radical.source().dim_vector().to_vec(),
            target: radical.target().dim_vector().to_vec(),
        },
        other => ArQuiverError::Space(other),
    })
}
