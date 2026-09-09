use super::super::VerifyError;
use super::check;
use super::empty_trace;
use super::fixtures::{square_certificate, x3_certificate};
use crate::certificate::{AmbiguityEntry, AmbiguityKind};

#[test]
fn missing_ambiguity_rejected() {
    let mut tampered = x3_certificate();
    tampered.ambiguities.remove(1);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AmbiguityMissing {
            i: 0,
            j: 0,
            kind: AmbiguityKind::Overlap,
            offset: 2,
        }
    );
}

#[test]
fn extra_ambiguity_rejected() {
    let mut tampered = square_certificate();
    tampered.ambiguities.push(AmbiguityEntry {
        i: 0,
        j: 0,
        kind: AmbiguityKind::Overlap,
        offset: 1,
        trace: empty_trace(),
    });
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AmbiguityExtra {
            i: 0,
            j: 0,
            kind: AmbiguityKind::Overlap,
            offset: 1,
        }
    );
}

#[test]
fn duplicated_ambiguity_rejected() {
    let mut tampered = x3_certificate();
    let entry = tampered.ambiguities[0].clone();
    tampered.ambiguities.push(entry);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AmbiguityDuplicate {
            i: 0,
            j: 0,
            kind: AmbiguityKind::Overlap,
            offset: 1,
        }
    );
}

#[test]
fn wrong_ambiguity_offset_rejected() {
    let mut tampered = x3_certificate();
    tampered.ambiguities[1].offset = 0;
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AmbiguityExtra {
            i: 0,
            j: 0,
            kind: AmbiguityKind::Overlap,
            offset: 0,
        }
    );
}

#[test]
fn ambiguities_out_of_order_rejected() {
    let mut tampered = x3_certificate();
    tampered.ambiguities.swap(0, 1);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AmbiguityOrder {
            index: 0,
            i: 0,
            j: 0,
            kind: AmbiguityKind::Overlap,
            offset: 1,
        }
    );
}
