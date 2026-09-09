use crate::certificate::{Certificate, RelationData};
use crate::field::PrimeField;
use crate::quiver::{PathWord, Quiver};

use super::common::{
    Poly, concatenate, find_factor, first_difference, ids, poly_add, poly_from_data,
    validate_relation_data,
};
use super::types::VerifyError;

pub(super) fn check_basis(
    quiver: &Quiver,
    modulus: u64,
    basis: &[RelationData],
) -> Result<(), VerifyError> {
    for (index, element) in basis.iter().enumerate() {
        validate_relation_data(quiver, modulus, element).map_err(|(term, defect)| {
            VerifyError::BasisRelation {
                index,
                term,
                defect,
            }
        })?;
        if element[0].0 != 1 {
            return Err(VerifyError::BasisNotMonic {
                index,
                coeff: element[0].0,
            });
        }
    }
    for (lead_index, leader) in basis.iter().enumerate() {
        let lead = &leader[0].1;
        for (element, other) in basis.iter().enumerate() {
            for (term, (_, word)) in other.iter().enumerate() {
                if element == lead_index && term == 0 {
                    continue;
                }
                if let Some(position) = find_factor(word, lead) {
                    return Err(VerifyError::BasisNotReduced {
                        lead: lead_index,
                        element,
                        term,
                        position,
                    });
                }
            }
        }
    }
    Ok(())
}

pub(super) fn check_origin(
    field: PrimeField,
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    if certificate.origin.len() != certificate.basis.len() {
        return Err(VerifyError::OriginCount {
            basis: certificate.basis.len(),
            origin: certificate.origin.len(),
        });
    }
    for (element, terms) in certificate.origin.iter().enumerate() {
        let mut sum = Poly::new();
        for (term_index, origin_term) in terms.iter().enumerate() {
            if origin_term.coeff == 0 || origin_term.coeff >= field.modulus() {
                return Err(VerifyError::OriginCoefficient {
                    element,
                    term: term_index,
                    coeff: origin_term.coeff,
                });
            }
            let Some(relation) = certificate.input_relations.get(origin_term.input_index) else {
                return Err(VerifyError::OriginInputIndex {
                    element,
                    term: term_index,
                    input_index: origin_term.input_index,
                    inputs: certificate.input_relations.len(),
                });
            };
            let scale = field.elem(origin_term.coeff as i64);
            for (coeff, word) in relation {
                let expanded = concatenate(&[&origin_term.left, word, &origin_term.right]);
                PathWord::from_arrows(quiver, &ids(&expanded)).map_err(|error| {
                    VerifyError::OriginNotComposable {
                        element,
                        term: term_index,
                        error,
                    }
                })?;
                let value = field.mul(scale, field.elem(*coeff as i64));
                poly_add(field, &mut sum, expanded, value);
            }
        }
        let target = poly_from_data(field, &certificate.basis[element]);
        if sum != target {
            return Err(VerifyError::OriginMismatch {
                element,
                word: first_difference(&sum, &target),
            });
        }
    }
    Ok(())
}
