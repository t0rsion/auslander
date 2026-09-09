use std::cmp::Ordering;

use crate::certificate::{AmbiguityKind, Certificate, RelationData, TraceStep};
use crate::field::{Fp, PrimeField};
use crate::quiver::{PathWord, Quiver};

use super::common::{
    Poly, cmp_words, concatenate, ids, poly_add, poly_from_data, poly_neg, validate_relation_data,
};
use super::types::{TraceSite, VerifyError};

fn replay(
    field: PrimeField,
    quiver: &Quiver,
    basis: &[RelationData],
    site: TraceSite,
    mut poly: Poly,
    steps: &[TraceStep],
) -> Result<(), VerifyError> {
    for (step_index, step) in steps.iter().enumerate() {
        let Some(element) = basis.get(step.basis_index) else {
            return Err(VerifyError::TraceStepBasisIndex {
                site,
                step: step_index,
                basis_index: step.basis_index,
                basis: basis.len(),
            });
        };
        let lead = &element[0].1;
        let factored = concatenate(&[&step.left, lead, &step.right]);
        if step.word != factored {
            return Err(VerifyError::TraceStepWord {
                site,
                step: step_index,
            });
        }
        PathWord::from_arrows(quiver, &ids(&step.word)).map_err(|error| {
            VerifyError::TraceStepPath {
                site,
                step: step_index,
                error,
            }
        })?;
        let Some(&current) = poly.get(&step.word) else {
            return Err(VerifyError::TraceStepAbsent {
                site,
                step: step_index,
                word: step.word.clone(),
            });
        };
        if step.coeff != current.raw() {
            return Err(VerifyError::TraceStepCoefficient {
                site,
                step: step_index,
                expected: current.raw(),
                found: step.coeff,
            });
        }
        for (term, (coeff, word)) in element.iter().enumerate() {
            let expanded = concatenate(&[&step.left, word, &step.right]);
            PathWord::from_arrows(quiver, &ids(&expanded)).map_err(|error| {
                VerifyError::TraceStepPath {
                    site,
                    step: step_index,
                    error,
                }
            })?;
            // The sealed order is compatible with concatenation, so this
            // branch cannot fire once the factorization check above and the
            // basis checks pass. The check guards the definition, not a
            // known failure mode.
            if term > 0 && cmp_words(&expanded, &step.word) != Ordering::Less {
                return Err(VerifyError::TraceStepAscending {
                    site,
                    step: step_index,
                    word: expanded,
                });
            }
            let delta = field.neg(field.mul(current, field.elem(*coeff as i64)));
            poly_add(field, &mut poly, expanded, delta);
        }
    }
    if let Some(word) = poly.keys().max_by(|a, b| cmp_words(a, b)) {
        return Err(VerifyError::TraceRemainder {
            site,
            word: word.clone(),
        });
    }
    Ok(())
}

pub(super) fn check_membership(
    field: PrimeField,
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    if certificate.membership.len() != certificate.input_relations.len() {
        return Err(VerifyError::MembershipCount {
            inputs: certificate.input_relations.len(),
            traces: certificate.membership.len(),
        });
    }
    for (input, trace) in certificate.membership.iter().enumerate() {
        if trace.start != certificate.input_relations[input] {
            return Err(VerifyError::MembershipStart { input });
        }
        replay(
            field,
            quiver,
            &certificate.basis,
            TraceSite::Membership { input },
            poly_from_data(field, &trace.start),
            &trace.steps,
        )?;
    }
    Ok(())
}

fn kind_tag(kind: AmbiguityKind) -> u8 {
    u8::from(matches!(kind, AmbiguityKind::Inclusion))
}

fn tag_kind(tag: u8) -> AmbiguityKind {
    match tag {
        0 => AmbiguityKind::Overlap,
        _ => AmbiguityKind::Inclusion,
    }
}

type AmbKey = (usize, usize, u8, usize);

/// All ambiguity keys of the ordered pair `(i, j)`, in canonical order:
/// overlap keys by ascending offset, then inclusion keys by ascending
/// offset.
fn pair_ambiguity_keys(i: usize, j: usize, leads: &[&Vec<u32>], out: &mut Vec<AmbKey>) {
    let lead_i = leads[i];
    let lead_j = leads[j];
    for offset in 1..lead_i.len() {
        let shared = lead_i.len() - offset;
        if shared < lead_j.len() && lead_i[offset..] == lead_j[..shared] {
            out.push((i, j, kind_tag(AmbiguityKind::Overlap), offset));
        }
    }
    if i != j && lead_j.len() < lead_i.len() {
        for offset in 0..=lead_i.len() - lead_j.len() {
            if lead_i[offset..offset + lead_j.len()] == **lead_j {
                out.push((i, j, kind_tag(AmbiguityKind::Inclusion), offset));
            }
        }
    }
}

/// Yields every ambiguity key of `leads` in canonical order without
/// materializing the full set: memory stays bounded by one pair's keys.
struct AmbiguityKeyGen<'a> {
    leads: &'a [&'a Vec<u32>],
    i: usize,
    j: usize,
    buffer: Vec<AmbKey>,
    buffer_at: usize,
}

impl<'a> AmbiguityKeyGen<'a> {
    fn new(leads: &'a [&'a Vec<u32>]) -> AmbiguityKeyGen<'a> {
        AmbiguityKeyGen {
            leads,
            i: 0,
            j: 0,
            buffer: Vec::new(),
            buffer_at: 0,
        }
    }

    fn next(&mut self) -> Option<AmbKey> {
        loop {
            if self.buffer_at < self.buffer.len() {
                self.buffer_at += 1;
                return Some(self.buffer[self.buffer_at - 1]);
            }
            if self.i >= self.leads.len() {
                return None;
            }
            self.buffer.clear();
            self.buffer_at = 0;
            pair_ambiguity_keys(self.i, self.j, self.leads, &mut self.buffer);
            self.j += 1;
            if self.j == self.leads.len() {
                self.j = 0;
                self.i += 1;
            }
        }
    }
}

/// Whether `(i, j, kind, offset)` names an ambiguity of `leads`. The test
/// reads the two leading words directly, so it stays independent of the
/// enumeration order that [`AmbiguityKeyGen`] follows.
fn is_ambiguity(leads: &[&Vec<u32>], key: AmbKey) -> bool {
    let (i, j, kind, offset) = key;
    let_or_false!((Some(lead_i), Some(lead_j)) = (leads.get(i), leads.get(j)));
    if kind == kind_tag(AmbiguityKind::Overlap) {
        verify_guard!(offset > 0 && offset < lead_i.len());
        let shared = lead_i.len() - offset;
        shared < lead_j.len() && lead_i[offset..] == lead_j[..shared]
    } else {
        i != j
            && lead_j.len() < lead_i.len()
            && offset <= lead_i.len() - lead_j.len()
            && lead_i[offset..offset + lead_j.len()] == **lead_j
    }
}

/// Caller guarantees `(i, j, kind, offset)` is an enumerated ambiguity of
/// the validated basis, so every concatenation composes.
fn composition(
    field: PrimeField,
    basis: &[RelationData],
    i: usize,
    j: usize,
    kind: AmbiguityKind,
    offset: usize,
) -> Poly {
    let lead_i = &basis[i][0].1;
    let lead_j = &basis[j][0].1;
    let mut poly = Poly::new();
    let mut add = |relation: &RelationData, parts: &[&[u32]], scale: Fp| {
        for (coeff, word) in relation {
            poly_add(
                field,
                &mut poly,
                concatenate(&[parts[0], word, parts[1]]),
                field.mul(scale, field.elem(*coeff as i64)),
            );
        }
    };
    match kind {
        AmbiguityKind::Overlap => {
            let left = &lead_i[..offset];
            let tail = &lead_j[lead_i.len() - offset..];
            add(&basis[i], &[&[][..], tail], field.one());
            add(&basis[j], &[left, &[][..]], field.neg(field.one()));
        }
        AmbiguityKind::Inclusion => {
            let left = &lead_i[..offset];
            let tail = &lead_i[offset + lead_j.len()..];
            add(&basis[i], &[&[][..], &[][..]], field.one());
            add(&basis[j], &[left, tail], field.neg(field.one()));
        }
    }
    poly
}

/// Lockstep comparison of the listed keys against the lazy canonical
/// enumeration. A listed key that differs from the expected one splits
/// three ways. A key that is not an ambiguity of the basis is extra. A
/// genuine key above the expected one skips it, so the list is out of
/// order. A genuine key below the expected one was already consumed in
/// lockstep, so it is a duplicate. Keys the list never reaches are
/// missing.
fn check_ambiguity_keys(certificate: &Certificate) -> Result<(), VerifyError> {
    let leads: Vec<&Vec<u32>> = certificate.basis.iter().map(|g| &g[0].1).collect();
    let mut generator = AmbiguityKeyGen::new(&leads);
    let mut next_expected = generator.next();
    for (index, entry) in certificate.ambiguities.iter().enumerate() {
        let found = (entry.i, entry.j, kind_tag(entry.kind), entry.offset);
        match next_expected {
            Some(expected) if expected == found => {
                next_expected = generator.next();
            }
            _ => {
                if !is_ambiguity(&leads, found) {
                    return Err(VerifyError::AmbiguityExtra {
                        i: entry.i,
                        j: entry.j,
                        kind: entry.kind,
                        offset: entry.offset,
                    });
                }
                match next_expected {
                    Some(expected) if found > expected => {
                        return Err(VerifyError::AmbiguityOrder {
                            index,
                            i: expected.0,
                            j: expected.1,
                            kind: tag_kind(expected.2),
                            offset: expected.3,
                        });
                    }
                    _ => {
                        return Err(VerifyError::AmbiguityDuplicate {
                            i: entry.i,
                            j: entry.j,
                            kind: entry.kind,
                            offset: entry.offset,
                        });
                    }
                }
            }
        }
    }
    if let Some((i, j, tag, offset)) = next_expected {
        return Err(VerifyError::AmbiguityMissing {
            i,
            j,
            kind: tag_kind(tag),
            offset,
        });
    }
    Ok(())
}

pub(super) fn check_ambiguities(
    field: PrimeField,
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    check_ambiguity_keys(certificate)?;
    for (index, entry) in certificate.ambiguities.iter().enumerate() {
        if !entry.trace.start.is_empty() {
            validate_relation_data(quiver, field.modulus(), &entry.trace.start).map_err(
                |(term, defect)| VerifyError::AmbiguityStart {
                    index,
                    term,
                    defect,
                },
            )?;
        }
        let start = poly_from_data(field, &entry.trace.start);
        let composed = composition(
            field,
            &certificate.basis,
            entry.i,
            entry.j,
            entry.kind,
            entry.offset,
        );
        if start != composed && start != poly_neg(field, &composed) {
            return Err(VerifyError::AmbiguityStartMismatch { index });
        }
        replay(
            field,
            quiver,
            &certificate.basis,
            TraceSite::Ambiguity { index },
            start,
            &entry.trace.steps,
        )?;
    }
    Ok(())
}
