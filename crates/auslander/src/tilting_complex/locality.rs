use super::*;
use crate::field::{Fp, PrimeField};

fn product(
    end: &HomotopyHomQuotient,
    left: &[Fp],
    right: &[Fp],
    meter: &mut WorkMeter,
) -> Result<Vec<Fp>, Interrupt> {
    meter.charge()?;
    let map = end.representative(left).then(&end.representative(right))?;
    Ok(end.reduce(&map)?.0)
}

fn power(
    end: &HomotopyHomQuotient,
    base: &[Fp],
    mut exponent: u64,
    one: &[Fp],
    meter: &mut WorkMeter,
) -> Result<Vec<Fp>, Interrupt> {
    let (mut result, mut base) = (one.to_vec(), base.to_vec());
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = product(end, &result, &base, meter)?;
        }
        exponent >>= 1;
        if exponent > 0 {
            base = product(end, &base, &base, meter)?;
        }
    }
    Ok(result)
}

/// Applies a residue map to quotient coordinates.
pub(super) fn residue_of(field: PrimeField, residue: &[Fp], coordinates: &[Fp]) -> Fp {
    let terms = residue.iter().zip(coordinates);
    terms.fold(field.zero(), |sum, (a, b)| {
        field.add(sum, field.mul(*a, *b))
    })
}

/// The residue map `End_K(X) → k` in quotient coordinates, when `End_K(X)` is
/// local with residue field `k`.
///
/// Acceptance is a proof. Write `N` for the kernel of the returned map. The
/// map sends the identity to a nonzero scalar, so `N` is a hyperplane that
/// misses the identity, and the check below finds a power `N^m = 0`. An
/// element outside `N` is then a nonzero scalar plus a nilpotent element, so it
/// is a unit. Every element of `N` is nilpotent. The non-units form the
/// subspace `N`, so the ring is local with radical `N` and residue field `k`.
///
/// The candidate map comes from the Frobenius: `x^q = λ·1` for the least power
/// `q` of `p` with `q ≥ dim`. In a local ring with residue field `k`, write
/// `x = λ + r` with `r` in the radical. Then `x^q = λ^q + r^q = λ`, so every
/// such ring is accepted. Returns `None` when the ring is zero, not local, or
/// local with a larger residue field.
pub(super) fn local_residue(
    end: &HomotopyHomQuotient,
    meter: &mut WorkMeter,
) -> Result<Option<Vec<Fp>>, Interrupt> {
    let field = end.source().terms()[0].field();
    let dim = end.dim();
    let one = end.reduce(&ChainMap::identity(end.source()))?.0;
    let mut exponent = 1u64;
    while (exponent as usize) < dim {
        exponent = exponent.saturating_mul(field.modulus());
    }
    let identity_line = DenseMat::from_rows(std::slice::from_ref(&one)).transpose();
    let mut residue = Vec::with_capacity(dim);
    for index in 0..dim {
        let mut unit = vec![field.zero(); dim];
        unit[index] = field.one();
        let value = power(end, &unit, exponent, &one, meter)?;
        let Some(scalar) = identity_line.solve(&value, &field) else {
            return Ok(None);
        };
        residue.push(scalar[0]);
    }
    if residue_of(field, &residue, &one).is_zero() {
        return Ok(None);
    }
    let radical = DenseMat::from_rows(std::slice::from_ref(&residue)).kernel_basis(&field);
    let mut ideal_power = radical.clone();
    for _ in 0..dim {
        let pairs = (0..ideal_power.rows())
            .flat_map(|left| (0..radical.rows()).map(move |right| (left, right)));
        let rows = pairs
            .map(|(left, right)| product(end, ideal_power.row(left), radical.row(right), meter))
            .collect::<Result<Vec<_>, _>>()?;
        ideal_power = DenseMat::from_rows_with_cols(&rows, dim).row_space_basis(&field);
    }
    Ok((ideal_power.rows() == 0).then_some(residue))
}
