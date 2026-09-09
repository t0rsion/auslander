use super::super::*;
use super::common::*;

use super::super::contracts::{basic_blocker, mutation_blocker, support_blocker};
use crate::algebra::linear_an;
use crate::ar::TauError;
use crate::basic::BasicError;
use crate::indec::IndecError;
use crate::module::Module;
use crate::mutation::MutationError;
use crate::supporttau::SupportTauError;
use crate::taurigid::TauRigidError;

/// A Hom system wider than `max_matrix_entries` stops the walk before the
/// allocation.
#[test]
fn a_matrix_budget_stops_the_walk_before_allocating() {
    let limits = MutationGraphLimits {
        max_matrix_entries: 1,
        ..MutationGraphLimits::default()
    };
    let outcome = support_tau_tilting_graph(&linear_an(3, f2()), &limits)
        .expect("A_3 walks without a defect");
    let graph = outcome.incomplete().expect("the budget stops the walk");
    match graph.reason() {
        IncompleteReason::BudgetExhausted(diagnostics) => {
            assert_eq!(diagnostics.limit(), GraphLimit::MatrixEntries);
        }
        IncompleteReason::CertificationBlocked(blocker) => {
            panic!("a matrix budget is no blocked certification: {blocker}")
        }
    }
}

/// A work-unit budget below the first step stops the walk with the typed
/// limit.
#[test]
fn a_work_unit_budget_stops_the_walk() {
    let limits = MutationGraphLimits {
        max_work_units: 1,
        ..MutationGraphLimits::default()
    };
    let outcome = support_tau_tilting_graph(&linear_an(3, f2()), &limits)
        .expect("A_3 walks without a defect");
    let graph = outcome.incomplete().expect("the budget stops the walk");
    match graph.reason() {
        IncompleteReason::BudgetExhausted(diagnostics) => {
            assert_eq!(diagnostics.limit(), GraphLimit::WorkUnits);
            assert_eq!(diagnostics.vertices_found(), 1);
            assert_eq!(diagnostics.verified_slots(), 0);
        }
        IncompleteReason::CertificationBlocked(blocker) => {
            panic!("a work budget is no blocked certification: {blocker}")
        }
    }
}

/// A closed walk never charges more work units than its budget.
///
/// The one-vertex algebra is the minimal case. `(A, 0)` has one slot and
/// its left mutation lands on `(0, A)`, which has no slot at all, so the
/// charges the walk makes after the slot precheck (the fingerprint, the
/// isomorphism test, the new vertex) had no later precheck to catch them.
/// Every budget from one unit up to the true count must truncate.
#[test]
fn a_closed_walk_never_charges_more_than_its_budget() {
    let algebra = semisimple(1, f2());
    let spent = walk(&algebra).work_units();
    for max_work_units in 1..spent {
        let limits = MutationGraphLimits {
            max_work_units,
            ..MutationGraphLimits::default()
        };
        let outcome = support_tau_tilting_graph(&algebra, &limits)
            .expect("the one-vertex walk runs without a defect");
        match outcome {
            SupportTauTiltingGraphOutcome::Closed(graph) => panic!(
                "a budget of {max_work_units} closed at {} units",
                graph.work_units()
            ),
            SupportTauTiltingGraphOutcome::Incomplete(graph) => match graph.reason() {
                IncompleteReason::BudgetExhausted(diagnostics) => {
                    assert_eq!(diagnostics.limit(), GraphLimit::WorkUnits);
                }
                IncompleteReason::CertificationBlocked(blocker) => {
                    panic!("a work budget is no blocked certification: {blocker}")
                }
            },
        }
    }
    // The true count still closes, so the gate is not off by one.
    let limits = MutationGraphLimits {
        max_work_units: spent,
        ..MutationGraphLimits::default()
    };
    let outcome = support_tau_tilting_graph(&algebra, &limits)
        .expect("the one-vertex walk runs without a defect");
    assert_eq!(
        outcome
            .closed()
            .expect("the true count closes")
            .work_units(),
        spent
    );
}

/// A mutation budget stops the walk when the next edge would exceed it.
#[test]
fn a_mutation_budget_stops_the_walk() {
    let limits = MutationGraphLimits {
        max_directed_mutations: 2,
        ..MutationGraphLimits::default()
    };
    let outcome = support_tau_tilting_graph(&linear_an(3, f2()), &limits)
        .expect("A_3 walks without a defect");
    let graph = outcome.incomplete().expect("the budget stops the walk");
    assert_eq!(graph.verified_mutations().len(), 2);
    match graph.reason() {
        IncompleteReason::BudgetExhausted(diagnostics) => {
            assert_eq!(diagnostics.limit(), GraphLimit::DirectedMutations);
        }
        IncompleteReason::CertificationBlocked(blocker) => {
            panic!("a mutation budget is no blocked certification: {blocker}")
        }
    }
}

/// An undetermined split or an undecided `tau` cross-check reads as a
/// blocked certification, and a rejected input does not.
///
/// No fixture in the suite produces either, since every split and every
/// `tau` cross-check the walk runs certifies. The classification is tested
/// here on constructed errors so the branch is covered: a blocked
/// certification must reach [`IncompleteReason::CertificationBlocked`] and
/// never [`IncompleteReason::BudgetExhausted`].
#[test]
fn blocked_certifications_never_read_as_budget_exhaustion() {
    let algebra = linear_an(2, f2());
    let blocked = BasicError::CertificationBlocked {
        reason: "a summand stayed undetermined after 8 split attempts".to_string(),
    };
    assert!(basic_blocker(&blocked).is_some());
    assert!(mutation_blocker(&MutationError::Basic(blocked.clone())).is_some());
    assert!(support_blocker(&SupportTauError::Basic(blocked)).is_some());
    assert!(
        mutation_blocker(&MutationError::Indec(IndecError::Undetermined {
            attempts: 8
        }))
        .is_some()
    );
    let undecided = SupportTauError::TauRigid(TauRigidError::Tau(TauError::AgreementUnknown {
        nakayama_kernel: Module::zero(&algebra),
        transpose_dual: Module::zero(&algebra),
        reason: "an undetermined summand".to_string(),
    }));
    assert!(support_blocker(&undecided).is_some());
    assert!(mutation_blocker(&MutationError::SupportTau(undecided)).is_some());
    // A rejected slot index is bad input, not a blocked certification.
    assert!(
        mutation_blocker(&MutationError::SlotOutOfRange {
            slot: 4,
            summands: 2
        })
        .is_none()
    );
    assert!(
        basic_blocker(&BasicError::NotBasic {
            first: 0,
            second: 1
        })
        .is_none()
    );
}
