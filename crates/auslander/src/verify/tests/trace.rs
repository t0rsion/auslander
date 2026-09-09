use super::super::{TraceSite, VerifyError};
use super::check;
use super::fixtures::{square_certificate, x3_certificate};
use crate::certificate::TraceStep;
use crate::quiver::QuiverError;

#[test]
fn origin_expanding_to_wrong_value_rejected() {
    let mut tampered = square_certificate();
    tampered.origin[0][0].coeff = 3;
    assert!(matches!(
        check(&tampered).unwrap_err(),
        VerifyError::OriginMismatch { element: 0, .. }
    ));
}

#[test]
fn origin_with_non_composable_concatenation_rejected() {
    let mut tampered = square_certificate();
    tampered.origin[0][0].left = vec![1];
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::OriginNotComposable {
            element: 0,
            term: 0,
            error: QuiverError::NotComposable { position: 0 },
        }
    );
}

#[test]
fn membership_trace_with_dropped_step_rejected() {
    let mut tampered = square_certificate();
    tampered.membership[0].steps.clear();
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::TraceRemainder {
            site: TraceSite::Membership { input: 0 },
            word: vec![2, 3],
        }
    );
}

/// Forged contexts cannot make a step ascend. The step word must
/// equal `left · leading word · right`, and the sealed order is
/// compatible with concatenation. A forged context instead names a
/// word the polynomial does not contain.
#[test]
fn membership_step_with_forged_context_rejected() {
    let mut tampered = x3_certificate();
    tampered.membership[0].steps[0] = TraceStep {
        word: vec![0, 0, 0, 0],
        basis_index: 0,
        left: vec![0],
        right: vec![],
        coeff: 1,
    };
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::TraceStepAbsent {
            site: TraceSite::Membership { input: 0 },
            step: 0,
            word: vec![0, 0, 0, 0],
        }
    );
}

#[test]
fn membership_step_naming_absent_word_rejected() {
    let mut tampered = square_certificate();
    let step = tampered.membership[0].steps[0].clone();
    tampered.membership[0].steps.push(step);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::TraceStepAbsent {
            site: TraceSite::Membership { input: 0 },
            step: 1,
            word: vec![2, 3],
        }
    );
}

#[test]
fn membership_step_with_non_eliminating_coefficient_rejected() {
    let mut tampered = square_certificate();
    tampered.membership[0].steps[0].coeff = 3;
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::TraceStepCoefficient {
            site: TraceSite::Membership { input: 0 },
            step: 0,
            expected: 4,
            found: 3,
        }
    );
}
