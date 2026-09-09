use super::super::{CycleWitness, VerifyError, WitnessDefect};
use super::check;
use super::fixtures::{loop_certificate, two_loop_certificate, x3_certificate};
use crate::certificate::{AutomatonData, CERT_SCHEMA, Certificate, FinitenessData, QuiverData};
use crate::order::ORDER_ID;

#[test]
fn false_finite_claim_on_an_infinite_language_rejected() {
    let mut tampered = loop_certificate();
    tampered.finiteness = FinitenessData::Finite;
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::FinitenessClaim {
            claimed_finite: true,
        }
    );
}

#[test]
fn false_infinite_claim_on_a_finite_language_rejected() {
    let mut tampered = x3_certificate();
    tampered.normal_words.clear();
    tampered.finiteness = FinitenessData::Infinite {
        prefix: vec![],
        cycle: vec![0],
    };
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::FinitenessClaim {
            claimed_finite: false,
        }
    );
}

#[test]
fn honest_infinite_certificate_yields_its_own_witness() {
    assert_eq!(
        check(&two_loop_certificate()).unwrap_err(),
        VerifyError::InfiniteDimensional {
            witness: CycleWitness {
                prefix: vec![],
                cycle: vec![0],
            },
        }
    );
}

#[test]
fn forged_witness_with_bad_prefix_rejected() {
    let mut tampered = two_loop_certificate();
    tampered.finiteness = FinitenessData::Infinite {
        prefix: vec![7],
        cycle: vec![0],
    };
    assert!(matches!(
        check(&tampered).unwrap_err(),
        VerifyError::InfiniteWitness {
            defect: WitnessDefect::NotAPath(_),
        }
    ));
}

#[test]
fn forged_witness_with_bad_cycle_rejected() {
    let mut tampered = two_loop_certificate();
    tampered.finiteness = FinitenessData::Infinite {
        prefix: vec![],
        cycle: vec![1],
    };
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::InfiniteWitness {
            defect: WitnessDefect::ContainsLeadingWord {
                lead: 0,
                position: 0,
            },
        }
    );
}

#[test]
fn forged_witness_with_empty_cycle_rejected() {
    let mut tampered = two_loop_certificate();
    tampered.finiteness = FinitenessData::Infinite {
        prefix: vec![0],
        cycle: vec![],
    };
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::InfiniteWitness {
            defect: WitnessDefect::EmptyCycle,
        }
    );
}

#[test]
fn forged_witness_with_non_returning_cycle_rejected() {
    let mut tampered = two_loop_certificate();
    tampered.finiteness = FinitenessData::Infinite {
        prefix: vec![1],
        cycle: vec![0],
    };
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::InfiniteWitness {
            defect: WitnessDefect::CycleDoesNotReturn {
                reached: 1,
                back: 0,
            },
        }
    );
}

#[test]
fn infinite_claim_with_nonempty_normal_words_rejected() {
    let mut tampered = two_loop_certificate();
    tampered.normal_words.push(vec![]);
    assert_eq!(
        check(&tampered).unwrap_err(),
        VerifyError::NormalWords {
            position: 0,
            expected: None,
            found: Some(vec![]),
        }
    );
}

#[test]
fn huge_declared_vertex_count_rejected_before_allocation() {
    let started = std::time::Instant::now();
    let certificate = Certificate {
        schema: CERT_SCHEMA.to_string(),
        field: 5,
        quiver: QuiverData {
            vertices: 4_294_967_295,
            arrows: vec![],
        },
        order: ORDER_ID.to_string(),
        input_relations: vec![],
        basis: vec![],
        origin: vec![],
        membership: vec![],
        ambiguities: vec![],
        normal_words: vec![],
        automaton: AutomatonData {
            states: vec![],
            transitions: vec![],
        },
        finiteness: FinitenessData::Finite,
    };
    assert_eq!(
        check(&certificate).unwrap_err(),
        VerifyError::AutomatonStateCount {
            vertices: 4_294_967_295,
            states: 0,
        }
    );
    assert!(
        started.elapsed() < std::time::Duration::from_secs(5),
        "the rejection must not allocate per declared vertex"
    );
}

/// Forty layers of two parallel arrows and no relations give a finite
/// language with more than 2^40 words. The lockstep comparison must
/// reject the empty normal-word list at position 0 without
/// enumerating the language.
#[test]
fn huge_finite_language_certificate_rejected_fast() {
    let layers = 40u32;
    let mut arrows = Vec::new();
    let mut transitions = Vec::new();
    for v in 0..layers {
        arrows.push((v, v + 1));
        arrows.push((v, v + 1));
        transitions.push((v as usize, 2 * v, (v + 1) as usize));
        transitions.push((v as usize, 2 * v + 1, (v + 1) as usize));
    }
    let certificate = Certificate {
        schema: CERT_SCHEMA.to_string(),
        field: 2,
        quiver: QuiverData {
            vertices: layers + 1,
            arrows,
        },
        order: ORDER_ID.to_string(),
        input_relations: vec![],
        basis: vec![],
        origin: vec![],
        membership: vec![],
        ambiguities: vec![],
        normal_words: vec![],
        automaton: AutomatonData {
            states: vec![vec![]; (layers + 1) as usize],
            transitions,
        },
        finiteness: FinitenessData::Finite,
    };
    let started = std::time::Instant::now();
    assert_eq!(
        check(&certificate).unwrap_err(),
        VerifyError::NormalWords {
            position: 0,
            expected: Some(vec![]),
            found: None,
        }
    );
    assert!(
        started.elapsed() < std::time::Duration::from_secs(5),
        "the lockstep comparison must fail fast"
    );
}

/// The zero-vertex quiver is legal, its language is finite, and the
/// empty normal-word list is the enumeration.
#[test]
fn zero_vertex_certificate_accepted() {
    let certificate = Certificate {
        schema: CERT_SCHEMA.to_string(),
        field: 5,
        quiver: QuiverData {
            vertices: 0,
            arrows: vec![],
        },
        order: ORDER_ID.to_string(),
        input_relations: vec![],
        basis: vec![],
        origin: vec![],
        membership: vec![],
        ambiguities: vec![],
        normal_words: vec![],
        automaton: AutomatonData {
            states: vec![],
            transitions: vec![],
        },
        finiteness: FinitenessData::Finite,
    };
    let verified = check(&certificate).unwrap();
    assert_eq!(verified.normal_words().len(), 0);
}
