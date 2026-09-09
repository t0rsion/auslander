use crate::field::{Fp, PrimeField};

/// Merges two sorted sparse term lists as `left + scale * right`.
pub(crate) fn merge_scaled_terms<T: Clone>(
    left: &[T],
    right: &[T],
    (scale, field): (Fp, &PrimeField),
    order: impl Fn(&T, &T) -> std::cmp::Ordering,
    coefficient: impl Fn(&T) -> Fp,
    with_coefficient: impl Fn(&T, Fp) -> T,
    out: &mut Vec<T>,
) {
    out.clear();
    out.reserve(left.len() + right.len());
    let mut i = 0;
    let mut j = 0;
    while i < left.len() && j < right.len() {
        match order(&left[i], &right[j]) {
            std::cmp::Ordering::Less => {
                out.push(left[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                let value = field.mul(scale, coefficient(&right[j]));
                if !value.is_zero() {
                    out.push(with_coefficient(&right[j], value));
                }
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                let value = field.add(
                    coefficient(&left[i]),
                    field.mul(scale, coefficient(&right[j])),
                );
                if !value.is_zero() {
                    out.push(with_coefficient(&left[i], value));
                }
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&left[i..]);
    for term in &right[j..] {
        let value = field.mul(scale, coefficient(term));
        if !value.is_zero() {
            out.push(with_coefficient(term, value));
        }
    }
}
