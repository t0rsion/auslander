//! Exact integer matrix invariants with checked `i128` arithmetic.
//!
//! Every function returns [`Overflow`] when one intermediate value leaves
//! `i128`. A result is never wrapped or rounded. Matrices are square and given
//! as rows.

/// An intermediate value left the `i128` range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Overflow;

pub(crate) type Checked<T> = Result<T, Overflow>;

fn mul(left: i128, right: i128) -> Checked<i128> {
    left.checked_mul(right).ok_or(Overflow)
}

fn sub(left: i128, right: i128) -> Checked<i128> {
    left.checked_sub(right).ok_or(Overflow)
}

fn add(left: i128, right: i128) -> Checked<i128> {
    left.checked_add(right).ok_or(Overflow)
}

/// `left / right` for a quotient known to be exact.
fn exact_div(left: i128, right: i128) -> Checked<i128> {
    debug_assert_eq!(left.checked_rem(right), Some(0));
    left.checked_div(right).ok_or(Overflow)
}

/// The determinant by fraction-free Bareiss elimination.
///
/// Each Bareiss quotient is exact, so the result is exact whenever every
/// intermediate product fits in `i128`.
pub(crate) fn determinant(matrix: &[Vec<i128>]) -> Checked<i128> {
    let mut rows = matrix.to_vec();
    let n = rows.len();
    let mut sign = 1;
    let mut previous = 1;
    for k in 0..n {
        let Some(pivot) = (k..n).find(|&row| rows[row][k] != 0) else {
            return Ok(0);
        };
        if pivot != k {
            rows.swap(pivot, k);
            sign = -sign;
        }
        bareiss_step(&mut rows, k, previous)?;
        previous = rows[k][k];
    }
    mul(sign, rows.last().map_or(1, |row| row[n - 1]))
}

fn bareiss_step(rows: &mut [Vec<i128>], k: usize, previous: i128) -> Checked<()> {
    let (upper, lower) = rows.split_at_mut(k + 1);
    let pivot_row = &upper[k];
    for row in lower {
        for column in k + 1..pivot_row.len() {
            let cross = sub(
                mul(row[column], pivot_row[k])?,
                mul(row[k], pivot_row[column])?,
            )?;
            row[column] = exact_div(cross, previous)?;
        }
    }
    Ok(())
}

/// The invariant factors `d_1 | d_2 | ... | d_n` of the Smith normal form.
///
/// Entries are nonnegative, and zero factors come last. The diagonalization
/// keeps the smallest nonzero entry as pivot, so every pass that leaves a
/// remainder strictly lowers the pivot and the loop ends.
pub(crate) fn invariant_factors(matrix: &[Vec<i128>]) -> Checked<Vec<i128>> {
    let mut rows = matrix.to_vec();
    let diagonal = (0..rows.len())
        .map(|k| clear_cross(&mut rows, k))
        .collect::<Checked<Vec<_>>>()?;
    divisibility_chain(diagonal)
}

/// Clears row `k` and column `k` off the diagonal and returns `|a_kk|`.
fn clear_cross(rows: &mut [Vec<i128>], k: usize) -> Checked<i128> {
    loop {
        let Some((row, column)) = smallest_entry(rows, k) else {
            return Ok(0);
        };
        rows.swap(k, row);
        for entries in rows.iter_mut() {
            entries.swap(k, column);
        }
        if !reduce_cross(rows, k)? {
            return rows[k][k].checked_abs().ok_or(Overflow);
        }
    }
}

fn smallest_entry(rows: &[Vec<i128>], k: usize) -> Option<(usize, usize)> {
    (k..rows.len())
        .flat_map(|row| (k..rows.len()).map(move |column| (row, column)))
        .filter(|&(row, column)| rows[row][column] != 0)
        .min_by_key(|&(row, column)| rows[row][column].unsigned_abs())
}

/// Reduces column `k`, then row `k`, by the pivot `a_kk`.
///
/// Returns whether a nonzero remainder is left in the cross.
fn reduce_cross(rows: &mut [Vec<i128>], k: usize) -> Checked<bool> {
    Ok(reduce_column(rows, k)? | reduce_row(rows, k)?)
}

fn reduce_column(rows: &mut [Vec<i128>], k: usize) -> Checked<bool> {
    let (upper, lower) = rows.split_at_mut(k + 1);
    let pivot_row = &upper[k];
    let mut remainder = false;
    for row in lower {
        let quotient = row[k].checked_div(pivot_row[k]).ok_or(Overflow)?;
        for (entry, &above) in row[k..].iter_mut().zip(&pivot_row[k..]) {
            *entry = sub(*entry, mul(quotient, above)?)?;
        }
        remainder |= row[k] != 0;
    }
    Ok(remainder)
}

fn reduce_row(rows: &mut [Vec<i128>], k: usize) -> Checked<bool> {
    let mut remainder = false;
    for column in k + 1..rows.len() {
        let quotient = rows[k][column].checked_div(rows[k][k]).ok_or(Overflow)?;
        for entries in rows[k..].iter_mut() {
            entries[column] = sub(entries[column], mul(quotient, entries[k])?)?;
        }
        remainder |= rows[k][column] != 0;
    }
    Ok(remainder)
}

/// Rewrites a nonnegative diagonal into a divisibility chain.
///
/// Replacing `(d_i, d_j)` by `(gcd, lcm)` keeps the diagonal matrix
/// equivalent. After pass `i`, `d_i` divides every later entry. A later pass
/// replaces two multiples of `d_i` by their gcd and lcm, which are again
/// multiples of `d_i`, so the chain holds.
fn divisibility_chain(mut diagonal: Vec<i128>) -> Checked<Vec<i128>> {
    for first in 0..diagonal.len() {
        for second in first + 1..diagonal.len() {
            let divisor = gcd(diagonal[first], diagonal[second]);
            if divisor != 0 {
                diagonal[second] = mul(diagonal[first] / divisor, diagonal[second])?;
                diagonal[first] = divisor;
            }
        }
    }
    Ok(diagonal)
}

fn gcd(mut left: i128, mut right: i128) -> i128 {
    while right != 0 {
        (left, right) = (right, left % right);
    }
    left
}

/// The coefficients of `det(xC + C^T)` in `Z[x]`, constant term first.
///
/// Trailing zero coefficients are dropped, so the zero polynomial is empty.
///
/// The method evaluates at `x = 0, 1, ..., n` and interpolates. It reuses
/// [`determinant`], and every Newton divided difference at consecutive integer
/// nodes of an integer polynomial is an integer, so each division is exact.
/// Bareiss over `Z[x]` would need exact polynomial division instead.
pub(crate) fn pencil(matrix: &[Vec<i128>]) -> Checked<Vec<i128>> {
    let n = matrix.len();
    let mut differences = (0..=n)
        .map(|point| determinant(&with_transpose(matrix, point as i128, 1)?))
        .collect::<Checked<Vec<_>>>()?;
    for order in 1..=n {
        for node in (order..=n).rev() {
            let step = sub(differences[node], differences[node - 1])?;
            differences[node] = exact_div(step, order as i128)?;
        }
    }
    let mut coefficients = newton_to_monomial(&differences)?;
    while coefficients.last() == Some(&0) {
        coefficients.pop();
    }
    Ok(coefficients)
}

/// `scale · C + transpose_scale · C^T` with checked entries.
pub(crate) fn with_transpose(
    matrix: &[Vec<i128>],
    scale: i128,
    transpose_scale: i128,
) -> Checked<Vec<Vec<i128>>> {
    (0..matrix.len())
        .map(|row| {
            (0..matrix.len())
                .map(|column| {
                    add(
                        mul(scale, matrix[row][column])?,
                        mul(transpose_scale, matrix[column][row])?,
                    )
                })
                .collect()
        })
        .collect()
}

/// Expands `sum_k a_k x (x - 1) ... (x - k + 1)` by Horner's rule.
fn newton_to_monomial(newton: &[i128]) -> Checked<Vec<i128>> {
    let mut coefficients = vec![newton[newton.len() - 1]];
    for node in (0..newton.len() - 1).rev() {
        let mut next = vec![0; coefficients.len() + 1];
        for (degree, &value) in coefficients.iter().enumerate() {
            next[degree + 1] = add(next[degree + 1], value)?;
            next[degree] = sub(next[degree], mul(node as i128, value)?)?;
        }
        next[0] = add(next[0], newton[node])?;
        coefficients = next;
    }
    Ok(coefficients)
}
