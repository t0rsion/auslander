use std::cmp::Ordering;
use std::collections::BTreeMap;

use crate::certificate::RelationData;
use crate::field::{Fp, PrimeField};
use crate::order::word_cmp;
use crate::quiver::{ArrowId, PathWord, Quiver};

use super::types::TermDefect;

pub(super) type Poly = BTreeMap<Vec<u32>, Fp>;

pub(super) fn ids(word: &[u32]) -> Vec<ArrowId> {
    word.iter().copied().map(ArrowId).collect()
}

pub(super) fn concatenate(parts: &[&[u32]]) -> Vec<u32> {
    parts.iter().flat_map(|part| part.iter()).copied().collect()
}

pub(super) fn cmp_words(a: &[u32], b: &[u32]) -> Ordering {
    word_cmp(&ids(a), &ids(b))
}

pub(super) fn is_suffix(needle: &[u32], hay: &[u32]) -> bool {
    needle.len() <= hay.len() && hay[hay.len() - needle.len()..] == *needle
}

pub(super) fn find_factor(hay: &[u32], needle: &[u32]) -> Option<usize> {
    if needle.is_empty() || needle.len() > hay.len() {
        return None;
    }
    (0..=hay.len() - needle.len()).find(|&at| hay[at..at + needle.len()] == *needle)
}

pub(super) fn poly_add(field: PrimeField, poly: &mut Poly, word: Vec<u32>, value: Fp) {
    use std::collections::btree_map::Entry;
    match poly.entry(word) {
        Entry::Vacant(entry) => {
            if !value.is_zero() {
                entry.insert(value);
            }
        }
        Entry::Occupied(mut entry) => {
            let sum = field.add(*entry.get(), value);
            if sum.is_zero() {
                entry.remove();
            } else {
                *entry.get_mut() = sum;
            }
        }
    }
}

/// Caller guarantees the data is validated: distinct words, canonical
/// nonzero coefficients.
pub(super) fn poly_from_data(field: PrimeField, data: &RelationData) -> Poly {
    let mut poly = Poly::new();
    for (coeff, word) in data {
        poly_add(field, &mut poly, word.clone(), field.elem(*coeff as i64));
    }
    poly
}

pub(super) fn poly_neg(field: PrimeField, poly: &Poly) -> Poly {
    poly.iter()
        .map(|(word, coeff)| (word.clone(), field.neg(*coeff)))
        .collect()
}

pub(super) fn first_difference(a: &Poly, b: &Poly) -> Vec<u32> {
    a.iter()
        .find(|(word, coeff)| b.get(*word) != Some(*coeff))
        .map(|(word, _)| word.clone())
        .or_else(|| b.keys().find(|word| !a.contains_key(*word)).cloned())
        .unwrap_or_default()
}

pub(super) fn first_mismatch<T: Clone + Eq>(
    mut expected: impl Iterator<Item = T>,
    found: &[T],
) -> Option<(usize, Option<T>, Option<T>)> {
    (0..)
        .map(|position| (position, expected.next(), found.get(position).cloned()))
        .take_while(|(_, expected, found)| expected.is_some() || found.is_some())
        .find(|(_, expected, found)| expected != found)
}

fn validated_relation_path(
    quiver: &Quiver,
    modulus: u64,
    index: usize,
    coeff: u64,
    word: &[u32],
) -> Result<PathWord, (usize, TermDefect)> {
    if coeff == 0 {
        return Err((index, TermDefect::ZeroCoefficient));
    }
    if coeff >= modulus {
        return Err((index, TermDefect::NonCanonicalCoefficient { coeff }));
    }
    if word.len() < 2 {
        return Err((index, TermDefect::WordTooShort { len: word.len() }));
    }
    PathWord::from_arrows(quiver, &ids(word))
        .map_err(|error| (index, TermDefect::InvalidWord(error)))
}

fn validate_term_endpoints(
    index: usize,
    path: &PathWord,
    endpoints: &mut Option<(u32, u32)>,
) -> Result<(), (usize, TermDefect)> {
    let Some((source, target)) = *endpoints else {
        *endpoints = Some((path.source(), path.target()));
        return Ok(());
    };
    if path.source() != source {
        return Err((index, TermDefect::MixedSource));
    }
    if path.target() != target {
        return Err((index, TermDefect::MixedTarget));
    }
    Ok(())
}

fn validate_relation_term(
    quiver: &Quiver,
    modulus: u64,
    data: &RelationData,
    endpoints: &mut Option<(u32, u32)>,
    index: usize,
) -> Result<(), (usize, TermDefect)> {
    let (coeff, word) = &data[index];
    let path = validated_relation_path(quiver, modulus, index, *coeff, word)?;
    validate_term_endpoints(index, &path, endpoints)?;
    if index > 0 && cmp_words(&data[index - 1].1, word) != Ordering::Greater {
        return Err((index, TermDefect::NotDescending));
    }
    Ok(())
}

pub(super) fn validate_relation_data(
    quiver: &Quiver,
    modulus: u64,
    data: &RelationData,
) -> Result<(), (usize, TermDefect)> {
    if data.is_empty() {
        return Err((0, TermDefect::Empty));
    }
    let mut endpoints = None;
    for index in 0..data.len() {
        validate_relation_term(quiver, modulus, data, &mut endpoints, index)?;
    }
    Ok(())
}
