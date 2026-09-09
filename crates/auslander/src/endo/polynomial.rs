use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;

use super::core::EndoAlgebra;
use super::helpers::SplitMix64;

pub(super) fn independent_fixed_element<'a>(
    fixed: &'a DenseMat,
    one: &[Fp],
    field: &PrimeField,
) -> Option<&'a [Fp]> {
    for row in 0..fixed.rows() {
        let mut stacked = DenseMat::zero(2, one.len());
        for (column, &coefficient) in one.iter().enumerate() {
            stacked.set(0, column, coefficient);
            stacked.set(1, column, fixed.get(row, column));
        }
        if stacked.rank(field) == 2 {
            return Some(fixed.row(row));
        }
    }
    None
}

fn multiply_by_linear(poly: &[Fp], root: Fp, field: &PrimeField) -> Vec<Fp> {
    let mut next = vec![Fp::ZERO; poly.len() + 1];
    for (degree, &coefficient) in poly.iter().enumerate() {
        next[degree + 1] = field.add(next[degree + 1], coefficient);
        next[degree] = field.sub(next[degree], field.mul(root, coefficient));
    }
    next
}

pub(super) fn lagrange_projector(roots: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let denominator = roots[1..].iter().fold(Fp::ONE, |acc, &root| {
        field.mul(acc, field.sub(roots[0], root))
    });
    let mut projector = vec![field.inv(denominator)];
    for &root in &roots[1..] {
        projector = multiply_by_linear(&projector, root, field);
    }
    projector
}

fn nontrivial(value: &[Fp], one: &[Fp]) -> bool {
    value.iter().any(|coefficient| !coefficient.is_zero()) && value != one
}

pub(super) fn valid_idempotent(
    value: &[Fp],
    one: &[Fp],
    multiply: impl Fn(&[Fp]) -> Vec<Fp>,
) -> bool {
    multiply(value) == value && nontrivial(value, one)
}

fn newton_idempotent_step(endo: &EndoAlgebra, value: &mut [Fp], square: &[Fp]) {
    let field = endo.field();
    let cube = endo.multiply(square, value);
    for (index, output) in value.iter_mut().enumerate() {
        let three = field.add(field.add(square[index], square[index]), square[index]);
        let two = field.add(cube[index], cube[index]);
        *output = field.sub(three, two);
    }
}

pub(super) fn newton_idempotent_lift(endo: &EndoAlgebra, mut value: Vec<Fp>) -> Option<Vec<Fp>> {
    for _ in 0..64 {
        let square = endo.multiply(&value, &value);
        if square == value {
            return nontrivial(&value, endo.one()).then_some(value);
        }
        newton_idempotent_step(endo, &mut value, &square);
    }
    None
}

/// Multiplies two polynomials over the field.
pub(super) fn poly_mul(a: &[Fp], b: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let mut out = vec![Fp::ZERO; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        if x.is_zero() {
            continue;
        }
        for (j, &y) in b.iter().enumerate() {
            let t = field.mul(x, y);
            out[i + j] = field.add(out[i + j], t);
        }
    }
    out
}

fn poly_trim(mut a: Vec<Fp>) -> Vec<Fp> {
    while a.last().is_some_and(|c| c.is_zero()) {
        a.pop();
    }
    a
}

fn poly_eval(a: &[Fp], x: Fp, field: &PrimeField) -> Fp {
    let mut acc = Fp::ZERO;
    for &c in a.iter().rev() {
        acc = field.add(field.mul(acc, x), c);
    }
    acc
}

// Division by monic b (ascending coefficients, b nonempty).
fn poly_division(a: &[Fp], b: &[Fp], field: &PrimeField, quotient: bool) -> Vec<Fp> {
    let mut r = a.to_vec();
    let db = b.len() - 1;
    let mut out = if quotient {
        vec![Fp::ZERO; a.len() - db]
    } else {
        Vec::new()
    };
    while r.len() > db {
        let lead = *r.last().expect("r is longer than b");
        let shift = r.len() - 1 - db;
        if quotient {
            out[shift] = lead;
        }
        if !lead.is_zero() {
            for (i, &c) in b.iter().enumerate() {
                let t = field.mul(lead, c);
                r[shift + i] = field.sub(r[shift + i], t);
            }
        }
        r.pop();
    }
    if quotient { out } else { poly_trim(r) }
}

// Remainder of a modulo monic b.
fn poly_rem(a: &[Fp], b: &[Fp], field: &PrimeField) -> Vec<Fp> {
    poly_division(a, b, field, false)
}

// Quotient of a by monic b, assuming b divides a exactly.
fn poly_quotient(a: &[Fp], b: &[Fp], field: &PrimeField) -> Vec<Fp> {
    poly_division(a, b, field, true)
}

// Monic gcd; zero polynomials are empty vectors.
fn poly_gcd(a: &[Fp], b: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let (mut x, mut y) = (poly_trim(a.to_vec()), poly_trim(b.to_vec()));
    while !y.is_empty() {
        let lead_inv = field.inv(*y.last().expect("y is nonzero"));
        let monic: Vec<Fp> = y.iter().map(|&c| field.mul(c, lead_inv)).collect();
        y = poly_rem(&x, &monic, field);
        x = monic;
    }
    let lead_inv = field.inv(*x.last().expect("gcd of nonzero inputs is nonzero"));
    x.iter().map(|&c| field.mul(c, lead_inv)).collect()
}

fn poly_powmod(base: &[Fp], exp: u64, modulus: &[Fp], field: &PrimeField) -> Vec<Fp> {
    binary_power!(
        poly_rem(base, modulus, field),
        vec![Fp::ONE],
        exp,
        |left, right| poly_rem(&poly_mul(left, right, field), modulus, field)
    )
}

fn poly_derivative(a: &[Fp], field: &PrimeField) -> Vec<Fp> {
    let mut out = Vec::with_capacity(a.len().saturating_sub(1));
    for (k, &c) in a.iter().enumerate().skip(1) {
        out.push(field.mul(c, field.elem(k as i64)));
    }
    poly_trim(out)
}

fn poly_mulmod(a: &[Fp], b: &[Fp], modulus: &[Fp], field: &PrimeField) -> Vec<Fp> {
    poly_rem(&poly_mul(a, b, field), modulus, field)
}

fn berlekamp_fixed_space(poly: &[Fp], field: &PrimeField) -> DenseMat {
    let n = poly.len() - 1;
    // Row i is x^(i p) mod poly, so right multiplication maps a coefficient row to its pth power.
    let mut frobenius = DenseMat::zero(n, n);
    let step = poly_powmod(&[Fp::ZERO, Fp::ONE], field.modulus(), poly, field);
    let mut current = vec![Fp::ONE];
    for row in 0..n {
        for (column, &coefficient) in current.iter().enumerate() {
            frobenius.set(row, column, coefficient);
        }
        current = poly_mulmod(&current, &step, poly, field);
    }
    for diagonal in 0..n {
        frobenius.set(
            diagonal,
            diagonal,
            field.sub(frobenius.get(diagonal, diagonal), Fp::ONE),
        );
    }
    frobenius.left_kernel_basis(field)
}

fn squarefree_berlekamp_input(poly: &[Fp], field: &PrimeField) -> bool {
    if poly.len() < 3 {
        return false;
    }
    let derivative = poly_derivative(poly, field);
    !derivative.is_empty() && poly_gcd(poly, &derivative, field).len() == 1
}

fn berlekamp_candidate(poly: &[Fp], field: &PrimeField) -> Option<(usize, Vec<Fp>)> {
    let n = poly.len() - 1;
    if !squarefree_berlekamp_input(poly, field) {
        return None;
    }
    let fixed = berlekamp_fixed_space(poly, field);
    // Constants span the fixed space exactly when poly is irreducible.
    for row in 0..fixed.rows() {
        let candidate = poly_trim(fixed.row(row).to_vec());
        if candidate.len() > 1 {
            return Some((n, candidate));
        }
    }
    None
}

fn linear_shift_factor(
    poly: &[Fp],
    candidate: &[Fp],
    shift: Fp,
    degree: usize,
    field: &PrimeField,
) -> Option<(Vec<Fp>, Vec<Fp>)> {
    let mut shifted = candidate.to_vec();
    shifted[0] = field.sub(shifted[0], shift);
    let factor = poly_gcd(poly, &poly_trim(shifted), field);
    (factor.len() > 1 && factor.len() <= degree)
        .then(|| (factor.clone(), poly_quotient(poly, &factor, field)))
}

fn scanned_berlekamp_split(
    poly: &[Fp],
    candidate: &[Fp],
    degree: usize,
    field: &PrimeField,
) -> Option<(Vec<Fp>, Vec<Fp>)> {
    for shift in 0..field.modulus() as i64 {
        if let Some(split) = linear_shift_factor(poly, candidate, field.elem(shift), degree, field)
        {
            return Some(split);
        }
    }
    None
}

fn quadratic_shift_factor(
    poly: &[Fp],
    shifted: &[Fp],
    degree: usize,
    field: &PrimeField,
) -> Option<(Vec<Fp>, Vec<Fp>)> {
    let mut powered = poly_powmod(shifted, (field.modulus() - 1) / 2, poly, field);
    if powered.is_empty() {
        powered.push(Fp::ZERO);
    }
    powered[0] = field.sub(powered[0], Fp::ONE);
    let factor = poly_gcd(poly, &poly_trim(powered), field);
    (factor.len() > 1 && factor.len() <= degree)
        .then(|| (factor.clone(), poly_quotient(poly, &factor, field)))
}

fn random_berlekamp_attempt(
    poly: &[Fp],
    candidate: &[Fp],
    degree: usize,
    shift: Fp,
    field: &PrimeField,
) -> Option<(Vec<Fp>, Vec<Fp>)> {
    if let Some(split) = linear_shift_factor(poly, candidate, shift, degree, field) {
        return Some(split);
    }
    let mut shifted = candidate.to_vec();
    shifted[0] = field.sub(shifted[0], shift);
    quadratic_shift_factor(poly, &poly_trim(shifted), degree, field)
}

fn random_berlekamp_split(
    poly: &[Fp],
    candidate: &[Fp],
    degree: usize,
    field: &PrimeField,
    rng: &mut SplitMix64,
) -> Option<(Vec<Fp>, Vec<Fp>)> {
    for _ in 0..64 {
        let shift = field.elem(rng.below(field.modulus()) as i64);
        if let Some(split) = random_berlekamp_attempt(poly, candidate, degree, shift, field) {
            return Some(split);
        }
    }
    None
}

/// A factorization `poly = g·h` into coprime nonconstant factors, or `None`
/// when none was found: `poly` irreducible, `poly` not squarefree, or an
/// unlucky streak in the Berlekamp element search.
///
/// Berlekamp rather than distinct-degree factorization, because the factors
/// that matter here can share a degree. `End(W ⊕ W)` for `End(W) = F_{p^d}` is
/// `M_2(F_{p^d})`. A typical successful draw there has two eigenvalues that are
/// not Frobenius conjugate but both generate `F_{p^d}`. They contribute two
/// distinct irreducible factors of degree `d`. Grouping factors by degree
/// returns the whole polynomial and splits nothing. The Berlekamp subalgebra
/// `{v : v^p ≡ v mod poly}` has dimension equal to the number of distinct
/// irreducible factors, and any non-scalar element of it separates them.
///
/// A non-squarefree argument returns `None` rather than being handled: callers
/// draw again, and a fresh element of a semisimple algebra has a squarefree
/// minimal polynomial with high probability.
pub(super) fn coprime_split(
    poly: &[Fp],
    field: &PrimeField,
    rng: &mut SplitMix64,
) -> Option<(Vec<Fp>, Vec<Fp>)> {
    let (degree, candidate) = berlekamp_candidate(poly, field)?;
    if field.modulus() <= 4096 {
        scanned_berlekamp_split(poly, &candidate, degree, field)
    } else {
        random_berlekamp_split(poly, &candidate, degree, field, rng)
    }
}

fn scanned_squarefree_roots(poly: &[Fp], field: &PrimeField) -> Option<Vec<Fp>> {
    let roots: Vec<Fp> = (0..field.modulus() as i64)
        .map(|value| field.elem(value))
        .filter(|&value| poly_eval(poly, value, field).is_zero())
        .collect();
    (roots.len() == poly.len() - 1).then_some(roots)
}

fn squarefree_root_factor(
    poly: &[Fp],
    field: &PrimeField,
    rng: &mut SplitMix64,
) -> Option<(Vec<Fp>, Vec<Fp>)> {
    let degree = poly.len() - 1;
    let delta = field.elem(rng.below(field.modulus()) as i64);
    let mut shifted = poly_powmod(&[delta, Fp::ONE], (field.modulus() - 1) / 2, poly, field);
    if shifted.is_empty() {
        shifted.push(Fp::ZERO);
    }
    shifted[0] = field.sub(shifted[0], Fp::ONE);
    let shifted = poly_trim(shifted);
    if shifted.is_empty() {
        return None;
    }
    let factor = poly_gcd(poly, &shifted, field);
    if factor.len() == 1 || factor.len() - 1 == degree {
        return None;
    }
    let quotient = poly_quotient(poly, &factor, field);
    Some((factor, quotient))
}

fn random_squarefree_roots(
    poly: &[Fp],
    field: &PrimeField,
    rng: &mut SplitMix64,
) -> Option<Vec<Fp>> {
    for _ in 0..64 {
        let Some((factor, quotient)) = squarefree_root_factor(poly, field, rng) else {
            continue;
        };
        let mut roots = split_squarefree_roots(&factor, field, rng)?;
        roots.extend(split_squarefree_roots(&quotient, field, rng)?);
        return Some(roots);
    }
    None
}

/// The roots of a monic polynomial known to split into distinct linear factors
/// over F_p: a full scan of the field for `p ≤ 4096`, otherwise seeded
/// Cantor-Zassenhaus splitting with `gcd(m, (x + δ)^{(p−1)/2} − 1)` and 64 draws.
///
/// The caller guarantees the input splits, so `None` means a failed coin-flip
/// streak on the large-`p` path, never a wrong answer. The scan path returns
/// `None` only if it finds fewer roots than the degree, which means the
/// guarantee was broken.
pub(super) fn split_squarefree_roots(
    poly: &[Fp],
    field: &PrimeField,
    rng: &mut SplitMix64,
) -> Option<Vec<Fp>> {
    let degree = poly.len() - 1;
    if field.modulus() <= 4096 {
        return scanned_squarefree_roots(poly, field);
    }
    match degree {
        0 => Some(Vec::new()),
        1 => Some(vec![field.neg(poly[0])]),
        _ => random_squarefree_roots(poly, field, rng),
    }
}
