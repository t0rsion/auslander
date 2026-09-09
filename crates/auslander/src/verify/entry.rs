use crate::certificate::{CERT_SCHEMA, Certificate};
use crate::field::PrimeField;
use crate::order::ORDER_ID;
use crate::quiver::{PathWord, Quiver};

use super::automaton::check_finiteness_and_normal_words;
use super::common::{ids, validate_relation_data};
use super::shape::{check_basis, check_origin};
use super::trace::{check_ambiguities, check_membership};
use super::types::{VerifiedCompletion, VerifyError};

fn validate_header(certificate: &Certificate) -> Result<PrimeField, VerifyError> {
    if certificate.schema != CERT_SCHEMA {
        return Err(VerifyError::Schema {
            found: certificate.schema.clone(),
        });
    }
    if certificate.order != ORDER_ID {
        return Err(VerifyError::Order {
            found: certificate.order.clone(),
        });
    }
    PrimeField::new(certificate.field).map_err(VerifyError::Field)
}

fn validated_quiver(certificate: &Certificate) -> Result<Quiver, VerifyError> {
    if certificate.automaton.states.len() < certificate.quiver.vertices as usize {
        return Err(VerifyError::AutomatonStateCount {
            vertices: certificate.quiver.vertices,
            states: certificate.automaton.states.len(),
        });
    }
    Quiver::new(certificate.quiver.vertices, &certificate.quiver.arrows)
        .map_err(VerifyError::Quiver)
}

fn check_relations(
    field: PrimeField,
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    for (index, relation) in certificate.input_relations.iter().enumerate() {
        validate_relation_data(quiver, field.modulus(), relation).map_err(|(term, defect)| {
            VerifyError::InputRelation {
                index,
                term,
                defect,
            }
        })?;
    }
    check_basis(quiver, field.modulus(), &certificate.basis)
}

fn check_witnesses(
    field: PrimeField,
    quiver: &Quiver,
    certificate: &Certificate,
) -> Result<(), VerifyError> {
    check_origin(field, quiver, certificate)?;
    check_membership(field, quiver, certificate)?;
    check_ambiguities(field, quiver, certificate)?;
    check_finiteness_and_normal_words(quiver, certificate)
}

fn verified_parts(certificate: &Certificate) -> Result<(PrimeField, Quiver), VerifyError> {
    let field = validate_header(certificate)?;
    let quiver = validated_quiver(certificate)?;
    check_relations(field, &quiver, certificate)?;
    check_witnesses(field, &quiver, certificate)?;
    Ok((field, quiver))
}

/// Parses certificate bytes and verifies the parsed certificate.
///
/// This is the entry point for untrusted bytes. Parsing is strict:
/// [`Certificate::from_json`] rejects an unknown field, a missing field,
/// a wrong JSON type, and trailing input, each as [`VerifyError::Parse`].
/// Everything after the parse is [`verify_certificate`].
pub fn verify(bytes: &str) -> Result<VerifiedCompletion, VerifyError> {
    verify_certificate(Certificate::from_json(bytes).map_err(VerifyError::Parse)?)
}

/// Verifies a parsed certificate and returns the trust token.
///
/// The checks read `certificate` and nothing else, so a caller that
/// already holds a typed certificate skips the serialization round trip.
/// Byte-level input goes through [`verify`], which adds the strict parse.
///
/// Checks run in this order. The first failure returns its typed error:
///
/// 1. Schema, order, field.
/// 2. The automaton declares at least one state per vertex. This binds
///    the declared vertex count to serialized data before the quiver is
///    built, so allocation stays proportional to the certificate size.
/// 3. Quiver.
/// 4. Input relations: valid uniform descending relation data.
/// 5. Basis: the same relation checks, monic, fully reduced.
/// 6. Origin: each basis element expands from the input relations.
/// 7. Membership: each input relation reduces to zero by the basis.
/// 8. Ambiguities: the list equals the lazy re-enumeration in canonical
///    key order, and every composition reduces to zero.
/// 9. Automaton: the certificate's states and transitions equal the
///    verifier's own automaton in canonical order.
/// 10. Finiteness: the claim matches the verifier's own cycle decision.
///     A finite claim requires the normal words to match the lazy
///     enumeration in lockstep. An infinite claim requires a fully
///     verified witness and an empty normal-word list, and returns
///     [`VerifyError::InfiniteDimensional`] with the certificate's
///     witness.
pub fn verify_certificate(certificate: Certificate) -> Result<VerifiedCompletion, VerifyError> {
    let (field, quiver) = verified_parts(&certificate)?;
    let basis = certificate
        .basis
        .iter()
        .map(|element| {
            element
                .iter()
                .map(|(coeff, word)| {
                    let path = PathWord::from_arrows(&quiver, &ids(word))
                        .expect("basis words were validated");
                    (field.elem(*coeff as i64), path)
                })
                .collect()
        })
        .collect();
    let normal_words = certificate
        .normal_words
        .iter()
        .enumerate()
        .map(|(index, word)| {
            if index < quiver.num_vertices() as usize {
                PathWord::trivial(&quiver, index as u32).expect("vertex index is in range")
            } else {
                PathWord::from_arrows(&quiver, &ids(word))
                    .expect("normal words matched the enumeration")
            }
        })
        .collect();
    Ok(VerifiedCompletion {
        certificate,
        quiver,
        field,
        basis,
        normal_words,
    })
}
