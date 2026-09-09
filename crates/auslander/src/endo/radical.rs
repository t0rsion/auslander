use crate::field::{Fp, PrimeField};
use crate::hom::Morphism;
use crate::linalg::DenseMat;

use super::core::EndoAlgebra;
use super::polynomial::poly_mul;

fn swap_similarity(matrix: &mut DenseMat, left: usize, right: usize) {
    for column in 0..matrix.cols() {
        let (x, y) = (matrix.get(left, column), matrix.get(right, column));
        matrix.set(left, column, y);
        matrix.set(right, column, x);
    }
    for row in 0..matrix.rows() {
        let (x, y) = (matrix.get(row, left), matrix.get(row, right));
        matrix.set(row, left, y);
        matrix.set(row, right, x);
    }
}

fn clear_hessenberg_entry(matrix: &mut DenseMat, column: usize, row: usize, field: &PrimeField) {
    let pivot_inverse = field.inv(matrix.get(column + 1, column));
    let scale = field.mul(matrix.get(row, column), pivot_inverse);
    if scale.is_zero() {
        return;
    }
    for target_column in 0..matrix.cols() {
        let term = field.mul(scale, matrix.get(column + 1, target_column));
        matrix.set(
            row,
            target_column,
            field.sub(matrix.get(row, target_column), term),
        );
    }
    for target_row in 0..matrix.rows() {
        let term = field.mul(scale, matrix.get(target_row, row));
        matrix.set(
            target_row,
            column + 1,
            field.add(matrix.get(target_row, column + 1), term),
        );
    }
}

fn upper_hessenberg(matrix: &DenseMat, field: &PrimeField) -> DenseMat {
    let n = matrix.rows();
    let mut result = matrix.clone();
    for column in 0..n.saturating_sub(2) {
        let Some(pivot) = ((column + 1)..n).find(|&row| !result.get(row, column).is_zero()) else {
            continue;
        };
        if pivot != column + 1 {
            swap_similarity(&mut result, pivot, column + 1);
        }
        for row in (column + 2)..n {
            clear_hessenberg_entry(&mut result, column, row, field);
        }
    }
    result
}

fn subtract_hessenberg_terms(
    next: &mut [Fp],
    matrix: &DenseMat,
    polynomials: &[Vec<Fp>],
    size: usize,
    field: &PrimeField,
) {
    let mut subdiagonal = Fp::ONE;
    for index in (1..size).rev() {
        subdiagonal = field.mul(subdiagonal, matrix.get(index, index - 1));
        if subdiagonal.is_zero() {
            break;
        }
        let scale = field.mul(matrix.get(index - 1, size - 1), subdiagonal);
        if scale.is_zero() {
            continue;
        }
        for (degree, &coefficient) in polynomials[index - 1].iter().enumerate() {
            next[degree] = field.sub(next[degree], field.mul(scale, coefficient));
        }
    }
}

/// Coefficients of `det(X·I − a)` in ascending powers of `X` (length
/// `n + 1`, leading coefficient 1): Hessenberg reduction by similarity, then
/// the leading-minor recurrence, both valid over any field.
pub(super) fn char_poly(a: &DenseMat, field: &PrimeField) -> Vec<Fp> {
    let n = a.rows();
    assert_eq!(a.cols(), n, "char_poly: matrix is not square");
    let matrix = upper_hessenberg(a, field);
    let mut polynomials = vec![vec![Fp::ONE]];
    for size in 1..=n {
        let previous = &polynomials[size - 1];
        let diagonal = matrix.get(size - 1, size - 1);
        let mut next = vec![Fp::ZERO; previous.len() + 1];
        for (degree, &coefficient) in previous.iter().enumerate() {
            next[degree + 1] = field.add(next[degree + 1], coefficient);
            next[degree] = field.sub(next[degree], field.mul(diagonal, coefficient));
        }
        subtract_hessenberg_terms(&mut next, &matrix, &polynomials, size, field);
        polynomials.push(next);
    }
    polynomials.pop().expect("polys holds p_0..p_n")
}

/// Characteristic polynomial of `f` acting on `⊕_v M_v` (ascending powers):
/// the product of the vertex-block characteristic polynomials.
pub(super) fn morphism_char_poly(f: &Morphism, field: &PrimeField) -> Vec<Fp> {
    let mut acc = vec![Fp::ONE];
    for v in 0..f.source().algebra().quiver().num_vertices() {
        acc = poly_mul(&acc, &char_poly(f.map_at(v), field), field);
    }
    acc
}

/// The first chain round in closed form: `−tr(b_k·b_j)` over the basis.
///
/// The round starts from the whole algebra, so its generators are the basis
/// itself, and its coefficient `c_1` of a product is minus the trace of that
/// product on `⊕_v M_v`. Since `tr(A·B)` sums `A[r][s]·B[s][r]`, the whole Gram
/// matrix is one product of the flattened basis with its blockwise transpose:
/// no composition, no characteristic polynomial, no `Morphism` allocated.
pub(super) fn trace_form(e: &EndoAlgebra) -> DenseMat {
    let field = e.field;
    let mut transposed = DenseMat::zero(e.dim(), e.flat.cols());
    let mut offset = 0;
    for &d in e.module.dim_vector() {
        for r in 0..d {
            for c in 0..d {
                for k in 0..e.dim() {
                    transposed.set(k, offset + r * d + c, e.flat.get(k, offset + c * d + r));
                }
            }
        }
        offset += d * d;
    }
    let mut gram = transposed.mul(&e.flat.transpose(), &field);
    for r in 0..gram.rows() {
        for c in 0..gram.cols() {
            gram.set(r, c, field.neg(gram.get(r, c)));
        }
    }
    gram
}

/// The Friedl-Rónyai chain: `B_{-1} = End(M)` and, for `p^i ≤ n = dim_k M`,
/// `B_i = {x ∈ B_{i-1} : c_{p^i}(x·y) = 0 for all y ∈ B_{i-1}}` where `c_j` is
/// the degree-`n − j` characteristic-polynomial coefficient on `⊕_v M_v`. The
/// last chain member is exactly the radical.
///
/// The bound `p^i ≤ dim_k M` is the one for a subalgebra of `End(V)`: Cohen,
/// Ivanyos and Wales, "Finding the radical of an algebra of linear
/// transformations", J. Pure Appl. Algebra 117/118 (1997). Rónyai works from
/// structure constants, so his bound is over `dim_k End(M)`, usually the larger
/// of the two. Running to that bound instead changes nothing: after the rounds
/// below, `x·y` is nilpotent for `x` and `y` in the chain member, so every
/// coefficient a later round reads is zero and every later kernel is the whole
/// member.
pub(super) fn ronyai_radical(e: &EndoAlgebra) -> DenseMat {
    let field = e.field;
    let n = e.module.total_dim();
    if e.dim() == 0 {
        return DenseMat::zero(0, 0);
    }
    let p = field.modulus();
    let mut cur = trace_form(e).kernel_basis(&field);
    let mut power = 1u64;
    while power * p <= n as u64 && cur.rows() > 0 {
        power *= p;
        let gens: Vec<Morphism> = (0..cur.rows()).map(|r| e.morphism(cur.row(r))).collect();
        let mut cond = DenseMat::zero(gens.len(), gens.len());
        for (j, gj) in gens.iter().enumerate() {
            for (k, gk) in gens.iter().enumerate() {
                let product = gj.then(gk).expect("endomorphisms compose");
                let cp = morphism_char_poly(&product, &field);
                cond.set(k, j, cp[n - power as usize]);
            }
        }
        cur = cond.kernel_basis(&field).mul(&cur, &field);
    }
    cur.row_space_basis(&field)
}
