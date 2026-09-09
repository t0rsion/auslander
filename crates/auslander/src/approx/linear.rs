use super::error::ApproxError;
use crate::decompose::add_morphisms;
use crate::endo::EndoAlgebra;
use crate::field::{Fp, PrimeField, unit_vector};
use crate::hom::{Morphism, identity, zero_morphism};
use crate::homspace::{HomSpace, row_times};
use crate::indec::IndecomposableModule;
use crate::linalg::DenseMat;
use crate::module::Module;

/// The RREF basis of `{y : sum_t y_t rows[t] = 0}`, one vector per row.
///
/// The caller passes `rows[t]` as the image of the `t`-th basis endomorphism
/// of `End(B)`, so a result row is a `K_f` element in `End(B)` coordinates.
/// `width` sizes the coordinate system of the images, and is required when
/// that system is empty.
pub(super) fn row_relations(rows: &[Vec<Fp>], width: usize, field: &PrimeField) -> DenseMat {
    DenseMat::from_rows_with_cols(rows, width)
        .transpose()
        .into_kernel_basis(field)
        .into_row_space_basis(field)
}

/// Solves many right-hand sides and reports the first one outside the image.
fn solve_many_or_index(
    system: &DenseMat,
    rhs: &DenseMat,
    field: &PrimeField,
    row: impl Fn(usize) -> Vec<Fp>,
) -> Result<Vec<Vec<Fp>>, usize> {
    let Some(x) = system.solve_many(rhs, field) else {
        return Err((0..rhs.cols())
            .position(|index| system.solve(&row(index), field).is_none())
            .expect("solve_many rejects only when some row lies outside"));
    };
    Ok(columns_of(&x))
}

/// Coordinates placing each row of `kernel` inside `rad End(B)`, or the index
/// of the first row that lies outside.
///
/// One [`DenseMat::solve_many`] covers every row. The failure path alone
/// repeats the solve to recover the first failing index.
pub(super) fn radical_coordinates(
    endo: &EndoAlgebra,
    kernel: &DenseMat,
) -> Result<Vec<Vec<Fp>>, usize> {
    let field = endo.field();
    let radical = endo.radical_basis().transpose();
    solve_many_or_index(&radical, &kernel.transpose(), &field, |r| {
        kernel.row(r).to_vec()
    })
}

/// The columns of `x`, one vector per column. [`DenseMat::solve_many`] puts
/// one solution in each column, and both callers want one solution per row.
fn columns_of(x: &DenseMat) -> Vec<Vec<Fp>> {
    (0..x.cols())
        .map(|j| (0..x.rows()).map(|i| x.get(i, j)).collect())
        .collect()
}

/// Coordinates writing each unit vector over the columns of `system`, or the
/// index of the first unit that lies outside the column space.
///
/// The unit vectors are the identity matrix, so one [`DenseMat::solve_many`]
/// replaces one `solve` per unit. The failure path alone repeats the solve
/// to recover the first failing index.
pub(super) fn unit_factorizations(
    system: &DenseMat,
    field: &PrimeField,
) -> Result<Vec<Vec<Fp>>, usize> {
    let dim = system.rows();
    solve_many_or_index(system, &DenseMat::identity(dim), field, |j| {
        unit_vector(dim, j)
    })
}

/// Whether `coords` against the radical basis reproduces `row`.
pub(super) fn radical_combination_matches(endo: &EndoAlgebra, coords: &[Fp], row: &[Fp]) -> bool {
    let radical = endo.radical_basis();
    verify_guard!(coords.len() == radical.rows() && row.len() == endo.dim());
    row_times(coords, radical, &endo.field()) == row
}

/// Whether the stored maps decompose `total` as the sum of the slot modules.
pub(super) fn decomposition_holds(
    total: &Module,
    summands: &[IndecomposableModule],
    slots: &[usize],
    inclusions: &[Morphism],
    projections: &[Morphism],
) -> bool {
    verify_guard!(inclusions.len() == slots.len() && projections.len() == slots.len());
    let_or_false!(Ok(mut sum) = zero_morphism(total, total));
    for (c, &i) in slots.iter().enumerate() {
        let part = summands[i].module();
        verify_guard!(inclusions[c].source().ptr_eq(part) && inclusions[c].target().ptr_eq(total));
        verify_guard!(
            projections[c].source().ptr_eq(total) && projections[c].target().ptr_eq(part)
        );
        for (d, incl) in inclusions.iter().enumerate() {
            let_or_false!(Ok(composite) = incl.then(&projections[c]));
            if c == d {
                if composite != identity(part) {
                    return false;
                }
            } else if !composite.is_zero() {
                return false;
            }
        }
        let_or_false!(Ok(idempotent) = projections[c].then(&inclusions[c]));
        sum = add_morphisms(&sum, &idempotent);
    }
    sum == identity(total)
}

/// The coordinates of `first.then(second)` in `space`.
pub(super) fn compose_into(
    space: &HomSpace,
    first: &Morphism,
    second: &Morphism,
) -> Result<Vec<Fp>, ApproxError> {
    let composite = first.then(second).map_err(ApproxError::Hom)?;
    space.coords(&composite).map_err(ApproxError::HomSpace)
}

pub(super) fn composition_rows(
    map: &Morphism,
    endo: &EndoAlgebra,
    space: &HomSpace,
) -> Result<Vec<Vec<Fp>>, ApproxError> {
    endo.basis()
        .iter()
        .map(|e| compose_into(space, map, e))
        .collect()
}
