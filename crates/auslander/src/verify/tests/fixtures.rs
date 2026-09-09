use super::empty_trace;
use crate::certificate::{
    AmbiguityEntry, AmbiguityKind, AutomatonData, CERT_SCHEMA, Certificate, FinitenessData,
    OriginTerm, QuiverData, Trace, TraceStep,
};
use crate::order::ORDER_ID;

/// k[x]/(x^3) over F_5: one loop, one monomial relation. Both
/// self-overlap compositions are exactly zero, so their traces are
/// empty.
pub(super) fn x3_certificate() -> Certificate {
    Certificate {
        schema: CERT_SCHEMA.to_string(),
        field: 5,
        quiver: QuiverData {
            vertices: 1,
            arrows: vec![(0, 0)],
        },
        order: ORDER_ID.to_string(),
        input_relations: vec![vec![(1, vec![0, 0, 0])]],
        basis: vec![vec![(1, vec![0, 0, 0])]],
        origin: vec![vec![OriginTerm {
            coeff: 1,
            left: vec![],
            input_index: 0,
            right: vec![],
        }]],
        membership: vec![Trace {
            start: vec![(1, vec![0, 0, 0])],
            steps: vec![TraceStep {
                word: vec![0, 0, 0],
                basis_index: 0,
                left: vec![],
                right: vec![],
                coeff: 1,
            }],
        }],
        ambiguities: vec![
            AmbiguityEntry {
                i: 0,
                j: 0,
                kind: AmbiguityKind::Overlap,
                offset: 1,
                trace: empty_trace(),
            },
            AmbiguityEntry {
                i: 0,
                j: 0,
                kind: AmbiguityKind::Overlap,
                offset: 2,
                trace: empty_trace(),
            },
        ],
        normal_words: vec![vec![], vec![0], vec![0, 0]],
        automaton: AutomatonData {
            states: vec![vec![], vec![0], vec![0, 0]],
            transitions: vec![(0, 0, 1), (1, 0, 2)],
        },
        finiteness: FinitenessData::Finite,
    }
}

/// The commutative square over F_5. Arrows: a = 0, b = 1, c = 2,
/// d = 3. The input is ab - cd. The word cd = [2, 3] is the larger
/// one, so the input stores as 4·[2, 3] + 1·[0, 1] and the monic
/// basis element is 1·[2, 3] + 4·[0, 1]. The origin scales the input
/// by 4. The membership trace eliminates [2, 3] with coefficient 4 in
/// one step.
pub(super) fn square_certificate() -> Certificate {
    Certificate {
        schema: CERT_SCHEMA.to_string(),
        field: 5,
        quiver: QuiverData {
            vertices: 4,
            arrows: vec![(0, 1), (1, 3), (0, 2), (2, 3)],
        },
        order: ORDER_ID.to_string(),
        input_relations: vec![vec![(4, vec![2, 3]), (1, vec![0, 1])]],
        basis: vec![vec![(1, vec![2, 3]), (4, vec![0, 1])]],
        origin: vec![vec![OriginTerm {
            coeff: 4,
            left: vec![],
            input_index: 0,
            right: vec![],
        }]],
        membership: vec![Trace {
            start: vec![(4, vec![2, 3]), (1, vec![0, 1])],
            steps: vec![TraceStep {
                word: vec![2, 3],
                basis_index: 0,
                left: vec![],
                right: vec![],
                coeff: 4,
            }],
        }],
        ambiguities: vec![],
        normal_words: vec![
            vec![],
            vec![],
            vec![],
            vec![],
            vec![0],
            vec![2],
            vec![1],
            vec![3],
            vec![0, 1],
        ],
        // States: the four vertices, then the prefix [2] of the leading
        // word cd. Reading c enters the prefix state; d from there
        // completes cd, so that transition is absent.
        automaton: AutomatonData {
            states: vec![vec![], vec![], vec![], vec![], vec![2]],
            transitions: vec![(0, 0, 1), (0, 2, 4), (1, 1, 3), (2, 3, 3)],
        },
        finiteness: FinitenessData::Finite,
    }
}

/// One loop, no relations: the normal-word language is infinite.
pub(super) fn loop_certificate() -> Certificate {
    Certificate {
        schema: CERT_SCHEMA.to_string(),
        field: 5,
        quiver: QuiverData {
            vertices: 1,
            arrows: vec![(0, 0)],
        },
        order: ORDER_ID.to_string(),
        input_relations: vec![],
        basis: vec![],
        origin: vec![],
        membership: vec![],
        ambiguities: vec![],
        normal_words: vec![],
        automaton: AutomatonData {
            states: vec![vec![]],
            transitions: vec![(0, 0, 0)],
        },
        finiteness: FinitenessData::Infinite {
            prefix: vec![],
            cycle: vec![0],
        },
    }
}

/// Two loops x = 0 and y = 1 over F_2 with the single relation y².
/// The normal-word language is infinite; the automaton has the vertex
/// state and the prefix state [1], and the witness loops on x.
pub(super) fn two_loop_certificate() -> Certificate {
    Certificate {
        schema: CERT_SCHEMA.to_string(),
        field: 2,
        quiver: QuiverData {
            vertices: 1,
            arrows: vec![(0, 0), (0, 0)],
        },
        order: ORDER_ID.to_string(),
        input_relations: vec![vec![(1, vec![1, 1])]],
        basis: vec![vec![(1, vec![1, 1])]],
        origin: vec![vec![OriginTerm {
            coeff: 1,
            left: vec![],
            input_index: 0,
            right: vec![],
        }]],
        membership: vec![Trace {
            start: vec![(1, vec![1, 1])],
            steps: vec![TraceStep {
                word: vec![1, 1],
                basis_index: 0,
                left: vec![],
                right: vec![],
                coeff: 1,
            }],
        }],
        ambiguities: vec![AmbiguityEntry {
            i: 0,
            j: 0,
            kind: AmbiguityKind::Overlap,
            offset: 1,
            trace: empty_trace(),
        }],
        normal_words: vec![],
        automaton: AutomatonData {
            states: vec![vec![], vec![1]],
            transitions: vec![(0, 0, 0), (0, 1, 1), (1, 0, 0)],
        },
        finiteness: FinitenessData::Infinite {
            prefix: vec![],
            cycle: vec![0],
        },
    }
}
