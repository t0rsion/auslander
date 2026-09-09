use super::types::{BasisElem, Exhausted, Origin, Poly, Word};
use crate::certificate::RelationData;
use crate::field::{Fp, PrimeField};
use crate::linalg::merge_scaled_terms;
use crate::order::word_cmp;
use crate::quiver::ArrowId;
use crate::relation::Relation;
use std::collections::BTreeSet;
pub(super) fn lead_word(elem: &BasisElem) -> &Word {
    &elem.poly.terms[0].1
}

fn concat2(a: &[ArrowId], b: &[ArrowId]) -> Word {
    a.iter().chain(b).copied().collect()
}

fn concat3(a: &[ArrowId], b: &[ArrowId], c: &[ArrowId]) -> Word {
    a.iter().chain(b).chain(c).copied().collect()
}

pub(super) fn raw_word(word: &[ArrowId]) -> Vec<u32> {
    word.iter().map(|a| a.0).collect()
}

pub(super) fn poly_from_relation(relation: &Relation) -> Poly {
    Poly {
        terms: relation
            .terms()
            .iter()
            .map(|(c, w)| (*c, w.arrows().to_vec()))
            .collect(),
    }
}

pub(super) fn poly_data(poly: &Poly) -> RelationData {
    poly.terms
        .iter()
        .map(|(c, w)| (c.raw(), raw_word(w)))
        .collect()
}

/// `base + c · left · src · right`, merged into strictly descending order.
/// Concatenation with a fixed context preserves the order on both sides,
/// so the mapped terms of `src` stay descending.
pub(super) fn add_scaled(
    field: PrimeField,
    base: &Poly,
    c: Fp,
    left: &[ArrowId],
    src: &Poly,
    right: &[ArrowId],
) -> Poly {
    let addend: Vec<(Fp, Word)> = src
        .terms
        .iter()
        .map(|(k, w)| (*k, concat3(left, w, right)))
        .collect();
    let mut merged = Vec::new();
    merge_scaled_terms(
        &base.terms,
        &addend,
        (c, &field),
        |a, b| word_cmp(&b.1, &a.1),
        |term| term.0,
        |term, value| (value, term.1.clone()),
        &mut merged,
    );
    Poly { terms: merged }
}

/// `target += c · left · src · right` on provenance, dropping zero sums.
/// Stops at the first insertion that puts `target` past `max` terms.
pub(super) fn origin_add_scaled(
    field: PrimeField,
    max: usize,
    target: &mut Origin,
    c: Fp,
    left: &[ArrowId],
    src: &Origin,
    right: &[ArrowId],
) -> Result<(), Exhausted> {
    for ((index, l, r), k) in src {
        let key = (*index, concat2(left, l), concat2(r, right));
        let current = target.get(&key).copied().unwrap_or(field.zero());
        let sum = field.add(current, field.mul(c, *k));
        if sum.is_zero() {
            target.remove(&key);
        } else {
            target.insert(key, sum);
            if target.len() > max {
                return Err(Exhausted::Origin);
            }
        }
    }
    Ok(())
}

pub(super) fn make_monic(field: PrimeField, poly: &mut Poly, origin: &mut Origin) {
    let lead_coeff = poly.terms[0].0;
    if lead_coeff == field.one() {
        return;
    }
    let inv = field.inv(lead_coeff);
    for (c, _) in &mut poly.terms {
        *c = field.mul(inv, *c);
    }
    for c in origin.values_mut() {
        *c = field.mul(inv, *c);
    }
}

/// Leftmost occurrence of `pattern` inside `word`.
pub(super) fn find_factor(word: &[ArrowId], pattern: &[ArrowId]) -> Option<usize> {
    if pattern.len() > word.len() {
        return None;
    }
    (0..=word.len() - pattern.len()).find(|&start| word[start..start + pattern.len()] == *pattern)
}

/// The next reduction target: `(term index, basis index, position)` for
/// the largest reducible word, the lowest reducing basis index, and its
/// leftmost occurrence. `skip` excludes one basis element.
pub(super) fn find_reduction(
    basis: &[BasisElem],
    skip: Option<usize>,
    poly: &Poly,
) -> Option<(usize, usize, usize)> {
    for (term_index, (_, word)) in poly.terms.iter().enumerate() {
        for (basis_index, elem) in basis.iter().enumerate() {
            if skip == Some(basis_index) {
                continue;
            }
            if let Some(position) = find_factor(word, lead_word(elem)) {
                return Some((term_index, basis_index, position));
            }
        }
    }
    None
}

pub(super) const KIND_OVERLAP: u8 = 0;
const KIND_INCLUSION: u8 = 1;

/// Canonical ambiguity key `(i, j, kind, offset)`. Overlap sorts before
/// inclusion.
pub(super) type AmbKey = (usize, usize, u8, usize);

/// All ambiguities of the ordered pair `(i, j)` with leading words
/// `li`, `lj`. Overlap: a proper nonempty suffix of `li` equals a proper
/// nonempty prefix of `lj`; `offset` is where `lj` starts inside the
/// superposition word. Inclusion: `lj` is a proper factor of `li` at
/// `offset`.
pub(super) fn pair_ambiguities(
    i: usize,
    j: usize,
    li: &[ArrowId],
    lj: &[ArrowId],
    out: &mut BTreeSet<AmbKey>,
) {
    for k in 1..li.len().min(lj.len()) {
        if li[li.len() - k..] == lj[..k] {
            out.insert((i, j, KIND_OVERLAP, li.len() - k));
        }
    }
    if lj.len() < li.len() {
        for offset in 0..=li.len() - lj.len() {
            if li[offset..offset + lj.len()] == *lj {
                out.insert((i, j, KIND_INCLUSION, offset));
            }
        }
    }
}

pub(super) fn superposition_len(basis: &[BasisElem], key: AmbKey) -> usize {
    let (i, j, kind, offset) = key;
    if kind == KIND_OVERLAP {
        offset + lead_word(&basis[j]).len()
    } else {
        lead_word(&basis[i]).len()
    }
}
