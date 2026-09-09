use super::super::VerifyError;
use super::check;
use super::fixtures::{square_certificate, x3_certificate};

#[test]
fn automaton_false_edge_rejected() {
    let mut tampered = square_certificate();
    tampered.automaton.transitions[3] = (4, 3, 3);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AutomatonTransitions {
            position: 3,
            expected: Some((2, 3, 3)),
            found: Some((4, 3, 3)),
        }
    );
}

#[test]
fn automaton_missing_state_rejected() {
    let mut tampered = x3_certificate();
    tampered.automaton.states.pop();
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AutomatonStates {
            position: 2,
            expected: Some(vec![0, 0]),
            found: None,
        }
    );
}

#[test]
fn automaton_reordered_states_rejected() {
    let mut tampered = x3_certificate();
    tampered.automaton.states.swap(1, 2);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AutomatonStates {
            position: 1,
            expected: Some(vec![0]),
            found: Some(vec![0, 0]),
        }
    );
}

#[test]
fn automaton_duplicate_transition_rejected() {
    let mut tampered = x3_certificate();
    tampered.automaton.transitions.insert(1, (0, 0, 1));
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AutomatonTransitions {
            position: 1,
            expected: Some((1, 0, 2)),
            found: Some((0, 0, 1)),
        }
    );
}

#[test]
fn automaton_out_of_order_transitions_rejected() {
    let mut tampered = x3_certificate();
    tampered.automaton.transitions.swap(0, 1);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::AutomatonTransitions {
            position: 0,
            expected: Some((0, 0, 1)),
            found: Some((1, 0, 2)),
        }
    );
}
