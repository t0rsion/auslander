use super::*;
use crate::certificate::{CERT_SCHEMA, QuiverData};

#[test]
fn monomial_x_cubed_is_a_no_op() {
    let c = completed(&x_cubed());
    assert_eq!(c.schema, CERT_SCHEMA);
    assert_eq!(c.field, 5);
    assert_eq!(c.order, ORDER_ID);
    assert_eq!(
        c.quiver,
        QuiverData {
            vertices: 1,
            arrows: vec![(0, 0)],
        }
    );
    assert_eq!(c.input_relations, vec![vec![(1, vec![0, 0, 0])]]);
    assert_eq!(c.basis, vec![vec![(1, vec![0, 0, 0])]]);
    assert_eq!(
        c.origin,
        vec![vec![OriginTerm {
            coeff: 1,
            left: vec![],
            input_index: 0,
            right: vec![],
        }]]
    );
    assert_eq!(
        c.membership,
        vec![Trace {
            start: vec![(1, vec![0, 0, 0])],
            steps: vec![TraceStep {
                word: vec![0, 0, 0],
                basis_index: 0,
                left: vec![],
                right: vec![],
                coeff: 1,
            }],
        }]
    );
    // Self-overlaps of xxx: the shared part is xx (offset 1) or x
    // (offset 2). Both compositions are zero, so the traces are
    // empty.
    assert_eq!(c.ambiguities.len(), 2);
    for (entry, offset) in c.ambiguities.iter().zip([1usize, 2]) {
        assert_eq!(
            (entry.i, entry.j, entry.kind, entry.offset),
            (0, 0, AmbiguityKind::Overlap, offset)
        );
        assert_eq!(
            entry.trace,
            Trace {
                start: vec![],
                steps: vec![],
            }
        );
    }
    assert_eq!(c.normal_words, vec![vec![], vec![0], vec![0, 0]]);
    // States: the vertex, then the proper prefixes x and xx of the
    // leading word xxx. Reading x from a state advances one prefix;
    // xx has no transition because xxx is forbidden.
    assert_eq!(
        c.automaton,
        AutomatonData {
            states: vec![vec![], vec![0], vec![0, 0]],
            transitions: vec![(0, 0, 1), (1, 0, 2)],
        }
    );
    assert_eq!(c.finiteness, FinitenessData::Finite);
}

#[test]
fn commutative_square_rewrites_cd_to_ab() {
    let c = completed(&commutative_square());
    // Input ab - cd is stored descending as 4·cd + ab. Monic scaling
    // by inv(4) = 4 gives cd + 4·ab, the rule cd -> ab.
    assert_eq!(
        c.input_relations,
        vec![vec![(4, vec![2, 3]), (1, vec![0, 1])]]
    );
    assert_eq!(c.basis, vec![vec![(1, vec![2, 3]), (4, vec![0, 1])]]);
    assert_eq!(
        c.origin,
        vec![vec![OriginTerm {
            coeff: 4,
            left: vec![],
            input_index: 0,
            right: vec![],
        }]]
    );
    assert_eq!(
        c.membership,
        vec![Trace {
            start: vec![(4, vec![2, 3]), (1, vec![0, 1])],
            steps: vec![TraceStep {
                word: vec![2, 3],
                basis_index: 0,
                left: vec![],
                right: vec![],
                coeff: 4,
            }],
        }]
    );
    assert!(c.ambiguities.is_empty());
    // Fixed basis order: e_0..e_3, then length 1 by (source, word):
    // a (source 0), c (source 0), b (source 1), d (source 2), then ab.
    assert_eq!(
        c.normal_words,
        vec![
            vec![],
            vec![],
            vec![],
            vec![],
            vec![0],
            vec![2],
            vec![1],
            vec![3],
            vec![0, 1],
        ]
    );
    assert_eq!(c.normal_words.len(), 9);
}

/// Hand computation for `overlap_example` (F_2, x = 0, y = 1):
/// seeds g0 = yx + xx, g1 = yy. The only initial ambiguities are the
/// overlap of yy with yx (suffix y = prefix y) and the self-overlap
/// of yy. The first composition is g1·x - y·g0 = yyx - yyx - yxx =
/// yxx. Reduction by g0 at position 0 leaves xxx. That word is
/// irreducible, so g2 = xxx joins the basis. All later compositions
/// reduce to zero, and interreduction changes nothing. The reduced
/// basis is {yx + xx, yy, xxx} and the normal words are
/// {e, x, y, xx, xy, xxy}.
#[test]
fn overlap_completion_adds_xxx() {
    let c = completed(&overlap_example());
    assert_eq!(
        c.basis,
        vec![
            vec![(1, vec![1, 0]), (1, vec![0, 0])],
            vec![(1, vec![1, 1])],
            vec![(1, vec![0, 0, 0])],
        ]
    );
    assert_eq!(
        c.origin[0],
        vec![OriginTerm {
            coeff: 1,
            left: vec![],
            input_index: 0,
            right: vec![],
        }]
    );
    assert_eq!(
        c.origin[1],
        vec![OriginTerm {
            coeff: 1,
            left: vec![],
            input_index: 1,
            right: vec![],
        }]
    );
    // g2 = xxx arises as g1·x - y·g0 - (reduction by g0·x):
    // xxx = r0·x + y·r0 + r1·x over F_2.
    assert_eq!(
        c.origin[2],
        vec![
            OriginTerm {
                coeff: 1,
                left: vec![],
                input_index: 0,
                right: vec![0],
            },
            OriginTerm {
                coeff: 1,
                left: vec![1],
                input_index: 0,
                right: vec![],
            },
            OriginTerm {
                coeff: 1,
                left: vec![],
                input_index: 1,
                right: vec![0],
            },
        ]
    );
    let keys: Vec<_> = c
        .ambiguities
        .iter()
        .map(|e| (e.i, e.j, e.kind, e.offset))
        .collect();
    assert_eq!(
        keys,
        vec![
            (0, 2, AmbiguityKind::Overlap, 1),
            (1, 0, AmbiguityKind::Overlap, 1),
            (1, 1, AmbiguityKind::Overlap, 1),
            (2, 2, AmbiguityKind::Overlap, 1),
            (2, 2, AmbiguityKind::Overlap, 2),
        ]
    );
    // (0, 2): g0·xx - y·g2 = xxxx, one reduction by g2.
    assert_eq!(c.ambiguities[0].trace.start, vec![(1, vec![0, 0, 0, 0])]);
    assert_eq!(
        c.ambiguities[0].trace.steps,
        vec![TraceStep {
            word: vec![0, 0, 0, 0],
            basis_index: 2,
            left: vec![],
            right: vec![0],
            coeff: 1,
        }]
    );
    // (1, 0): g1·x - y·g0 = yxx. Reduce by g0·x to xxx, then by g2.
    assert_eq!(c.ambiguities[1].trace.start, vec![(1, vec![1, 0, 0])]);
    assert_eq!(
        c.ambiguities[1].trace.steps,
        vec![
            TraceStep {
                word: vec![1, 0, 0],
                basis_index: 0,
                left: vec![],
                right: vec![0],
                coeff: 1,
            },
            TraceStep {
                word: vec![0, 0, 0],
                basis_index: 2,
                left: vec![],
                right: vec![],
                coeff: 1,
            },
        ]
    );
    for entry in &c.ambiguities[2..] {
        assert_eq!(
            entry.trace,
            Trace {
                start: vec![],
                steps: vec![],
            }
        );
    }
    assert_eq!(
        c.normal_words,
        vec![
            vec![],
            vec![0],
            vec![1],
            vec![0, 0],
            vec![0, 1],
            vec![0, 0, 1],
        ]
    );
}

/// Hand computation for `inclusion_example` (F_2, one loop x):
/// x⁴ + x² sits inside x⁵ as an inclusion. The overlap of x⁵ with
/// x⁴ + x² at offset 2 gives x⁶ - x²·(x⁴ + x²) = x⁴, which reduces
/// by x⁴ + x² to x². With x² in the basis every other composition
/// reduces to zero. Interreduction drops x⁵ and x⁴ + x², and
/// completion re-runs on {x²} without change.
#[test]
fn inclusion_collapses_to_x_squared() {
    let c = completed(&inclusion_example());
    assert_eq!(c.basis, vec![vec![(1, vec![0, 0])]]);
    assert_eq!(c.normal_words, vec![vec![], vec![0]]);
    let keys: Vec<_> = c
        .ambiguities
        .iter()
        .map(|e| (e.i, e.j, e.kind, e.offset))
        .collect();
    assert_eq!(keys, vec![(0, 0, AmbiguityKind::Overlap, 1)]);
    assert_eq!(
        c.ambiguities[0].trace,
        Trace {
            start: vec![],
            steps: vec![],
        }
    );
    assert_eq!(
        c.membership,
        vec![
            Trace {
                start: vec![(1, vec![0, 0, 0, 0, 0])],
                steps: vec![TraceStep {
                    word: vec![0, 0, 0, 0, 0],
                    basis_index: 0,
                    left: vec![],
                    right: vec![0, 0, 0],
                    coeff: 1,
                }],
            },
            Trace {
                start: vec![(1, vec![0, 0, 0, 0]), (1, vec![0, 0])],
                steps: vec![
                    TraceStep {
                        word: vec![0, 0, 0, 0],
                        basis_index: 0,
                        left: vec![],
                        right: vec![0, 0],
                        coeff: 1,
                    },
                    TraceStep {
                        word: vec![0, 0],
                        basis_index: 0,
                        left: vec![],
                        right: vec![],
                        coeff: 1,
                    },
                ],
            },
        ]
    );
}

#[test]
fn inhomogeneous_relation_completes_without_ambiguities() {
    let c = completed(&inhomogeneous());
    assert_eq!(
        c.input_relations,
        vec![vec![(1, vec![2, 3, 4]), (4, vec![0, 1])]]
    );
    assert_eq!(c.basis, vec![vec![(1, vec![2, 3, 4]), (4, vec![0, 1])]]);
    assert!(c.ambiguities.is_empty());
    assert_eq!(
        c.membership,
        vec![Trace {
            start: vec![(1, vec![2, 3, 4]), (4, vec![0, 1])],
            steps: vec![TraceStep {
                word: vec![2, 3, 4],
                basis_index: 0,
                left: vec![],
                right: vec![],
                coeff: 1,
            }],
        }]
    );
    // e_0..e_4, then a, c, b, d, e by (source, word), then ab, cd,
    // de. The word cde and its extensions are excluded.
    assert_eq!(
        c.normal_words,
        vec![
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![0],
            vec![2],
            vec![1],
            vec![3],
            vec![4],
            vec![0, 1],
            vec![2, 3],
            vec![3, 4],
        ]
    );
    assert_eq!(c.normal_words.len(), 13);
}
