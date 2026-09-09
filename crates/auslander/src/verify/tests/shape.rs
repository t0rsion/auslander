use super::super::{TermDefect, VerifyError};
use super::check;
use super::fixtures::{square_certificate, x3_certificate};
use crate::field::FieldError;
use crate::quiver::QuiverError;

#[test]
fn wrong_schema_rejected() {
    let mut tampered = square_certificate();
    tampered.schema = "wrong".to_string();
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::Schema {
            found: "wrong".to_string(),
        }
    );
}

#[test]
fn non_prime_field_rejected() {
    let mut tampered = square_certificate();
    tampered.field = 6;
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::Field(FieldError::NotPrime(6))
    );
}

#[test]
fn arrow_endpoint_out_of_range_rejected() {
    let mut tampered = square_certificate();
    tampered.quiver.arrows[3] = (2, 7);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::Quiver(QuiverError::EndpointOutOfRange {
            arrow: 3,
            vertex: 7,
            num_vertices: 4,
        })
    );
}

#[test]
fn non_canonical_coefficient_rejected() {
    let mut tampered = square_certificate();
    tampered.input_relations[0][0].0 = 9;
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::InputRelation {
            index: 0,
            term: 0,
            defect: TermDefect::NonCanonicalCoefficient { coeff: 9 },
        }
    );
}

#[test]
fn non_monic_basis_rejected() {
    let mut tampered = square_certificate();
    tampered.basis[0][0].0 = 2;
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::BasisNotMonic { index: 0, coeff: 2 }
    );
}

#[test]
fn non_reduced_basis_rejected() {
    let mut tampered = x3_certificate();
    tampered.basis.push(vec![(1, vec![0, 0, 0, 0])]);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::BasisNotReduced {
            lead: 0,
            element: 1,
            term: 0,
            position: 0,
        }
    );
}
