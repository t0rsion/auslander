use super::*;
use std::collections::BTreeSet;

#[test]
fn identical_input_gives_identical_bytes() {
    let p = overlap_example();
    let first = completed(&p).to_canonical_json();
    let second = completed(&p).to_canonical_json();
    assert_eq!(first, second);
}

#[test]
fn input_order_does_not_change_the_basis() {
    let straight = completed(&overlap_example());
    let swapped = completed(&overlap_example_swapped());
    let a: BTreeSet<RelationData> = straight.basis.iter().cloned().collect();
    let b: BTreeSet<RelationData> = swapped.basis.iter().cloned().collect();
    assert_eq!(a, b);
}

#[test]
fn free_loop_reports_empty_normal_words() {
    let c = completed(&one_loop_free());
    assert!(c.input_relations.is_empty());
    assert!(c.basis.is_empty());
    assert!(c.origin.is_empty());
    assert!(c.membership.is_empty());
    assert!(c.ambiguities.is_empty());
    // One free loop has infinitely many normal words. Per the
    // module contract the list stays empty and the finiteness section
    // carries the witness.
    assert_eq!(c.normal_words, Vec::<Vec<u32>>::new());
    assert_eq!(
        c.automaton,
        AutomatonData {
            states: vec![vec![]],
            transitions: vec![(0, 0, 0)],
        }
    );
    assert_eq!(
        c.finiteness,
        FinitenessData::Infinite {
            prefix: vec![],
            cycle: vec![0],
        }
    );
}

/// Every layer has two parallel arrows, so the path count doubles per
/// layer and the finite language has more than 2^40 words. The work
/// budget must stop emission before the list is materialized.
#[test]
fn huge_finite_language_truncates_instead_of_exhausting_memory() {
    let layers = 40u32;
    let mut arrows = Vec::new();
    for v in 0..layers {
        arrows.push((v, v + 1));
        arrows.push((v, v + 1));
    }
    let quiver = Quiver::new(layers + 1, &arrows).unwrap();
    let presentation = Presentation::new(quiver, f(2), Vec::new()).unwrap();
    let limits = CompletionLimits {
        max_steps: 10_000,
        ..CompletionLimits::default()
    };
    let started = std::time::Instant::now();
    let diagnostics = truncated(&presentation, &limits);
    assert_eq!(diagnostics.reason, TruncationReason::StepBudget);
    assert_eq!(diagnostics.steps_used, 10_000);
    assert_eq!(diagnostics.pending_ambiguities, 0);
    assert!(
        started.elapsed() < std::time::Duration::from_secs(5),
        "truncation must be fast"
    );
}
