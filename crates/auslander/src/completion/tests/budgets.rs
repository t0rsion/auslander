use super::*;

#[test]
fn tight_basis_budget_truncates() {
    let limits = CompletionLimits {
        max_basis: 2,
        ..CompletionLimits::default()
    };
    assert_eq!(
        truncated(&overlap_example(), &limits),
        TruncationDiagnostics {
            basis_len: 2,
            pending_ambiguities: 2,
            steps_used: 1,
            reason: TruncationReason::BasisBudget,
        }
    );
}

#[test]
fn tight_word_len_budget_truncates() {
    let limits = CompletionLimits {
        max_word_len: 3,
        ..CompletionLimits::default()
    };
    assert_eq!(
        truncated(&overlap_example(), &limits),
        TruncationDiagnostics {
            basis_len: 3,
            pending_ambiguities: 4,
            steps_used: 1,
            reason: TruncationReason::WordLenBudget,
        }
    );
}

#[test]
fn tight_step_budget_truncates() {
    let limits = CompletionLimits {
        max_steps: 1,
        ..CompletionLimits::default()
    };
    assert_eq!(
        truncated(&overlap_example(), &limits),
        TruncationDiagnostics {
            basis_len: 3,
            pending_ambiguities: 4,
            steps_used: 1,
            reason: TruncationReason::StepBudget,
        }
    );
}

/// One reduction step adds the whole origin of the basis element it
/// uses, so provenance grows faster than the step count. The first
/// budget below stops the seed of `r0`, the second the third
/// provenance term of `xxx`.
#[test]
fn tight_origin_budget_truncates() {
    let none = CompletionLimits {
        max_origin_terms: 0,
        ..CompletionLimits::default()
    };
    assert_eq!(
        truncated(&overlap_example(), &none),
        TruncationDiagnostics {
            basis_len: 0,
            pending_ambiguities: 0,
            steps_used: 0,
            reason: TruncationReason::OriginBudget,
        }
    );
    let two = CompletionLimits {
        max_origin_terms: 2,
        ..CompletionLimits::default()
    };
    assert_eq!(
        truncated(&overlap_example(), &two),
        TruncationDiagnostics {
            basis_len: 2,
            pending_ambiguities: 2,
            steps_used: 1,
            reason: TruncationReason::OriginBudget,
        }
    );
}

/// One vertex, three loops, every length-2 word forbidden. Each of the
/// 9 leading words overlaps 3 others, so the eager enumeration builds
/// 27 keys. Every composition of a monomial ideal is exactly zero, so
/// the drain charges no reduction steps and `max_steps` never fires:
/// only `max_ambiguities` bounds the queue.
#[test]
fn tight_ambiguity_budget_truncates() {
    let quiver = Quiver::new(1, &[(0, 0), (0, 0), (0, 0)]).unwrap();
    let field = f(2);
    let relations = (0..3)
        .flat_map(|p| (0..3).map(move |q| (p, q)))
        .map(|(p, q)| rel(&quiver, field, &[(1, &[p, q])]))
        .collect();
    let presentation = Presentation::new(quiver, field, relations).unwrap();
    let limits = CompletionLimits {
        max_ambiguities: 4,
        ..CompletionLimits::default()
    };
    assert_eq!(
        truncated(&presentation, &limits),
        TruncationDiagnostics {
            basis_len: 9,
            pending_ambiguities: 5,
            steps_used: 0,
            reason: TruncationReason::AmbiguityBudget,
        }
    );
}
