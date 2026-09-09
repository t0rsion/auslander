use std::sync::Arc;

use crate::algebra::Algebra;
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;

use super::outcome::{HochschildCohomology, HochschildDegree, IncompleteHochschildCohomology};

pub(super) fn row_times(row: &[Fp], matrix: &DenseMat, field: &PrimeField) -> Vec<Fp> {
    let mut output = vec![field.zero(); matrix.cols()];
    for (source, &coefficient) in row.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        for (target, value) in output.iter_mut().enumerate() {
            *value = field.add(*value, field.mul(coefficient, matrix.get(source, target)));
        }
    }
    output
}

pub(super) fn same_degree(left: &HochschildDegree, right: &HochschildDegree) -> bool {
    let (left, right) = (&left.0, &right.0);
    same_algebra(&left.algebra, &right.algebra)
        && left.degree == right.degree
        && left.limits == right.limits
        && left.layout.coordinates == right.layout.coordinates
        && left.layout.offsets == right.layout.offsets
        && left.differential == right.differential
        && left.cocycles == right.cocycles
        && left.coboundaries == right.coboundaries
        && left.complement == right.complement
}

pub(super) fn same_complete(left: &HochschildCohomology, right: &HochschildCohomology) -> bool {
    same_algebra(&left.algebra, &right.algebra)
        && left.requested_degree == right.requested_degree
        && left.limits == right.limits
        && left.diagnostics == right.diagnostics
        && same_degrees(&left.degrees, &right.degrees)
}

pub(super) fn same_cut(
    left: &IncompleteHochschildCohomology,
    right: &IncompleteHochschildCohomology,
) -> bool {
    same_algebra(&left.algebra, &right.algebra)
        && left.requested_degree == right.requested_degree
        && left.limits == right.limits
        && left.diagnostics == right.diagnostics
        && same_degrees(&left.degrees, &right.degrees)
}

fn same_degrees(left: &[HochschildDegree], right: &[HochschildDegree]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(a, b)| same_degree(a, b))
}

fn same_algebra(left: &Arc<Algebra>, right: &Arc<Algebra>) -> bool {
    Arc::ptr_eq(left, right)
        || (left.field() == right.field()
            && left.quiver() == right.quiver()
            && left.basis() == right.basis()
            && (0..left.dim())
                .all(|p| (0..left.dim()).all(|q| left.mul_basis(p, q) == right.mul_basis(p, q))))
}
