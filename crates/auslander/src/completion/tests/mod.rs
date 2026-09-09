mod budgets;
mod certificates;
mod determinism;
mod invariants;

use crate::certificate::{
    AmbiguityKind, AutomatonData, Certificate, FinitenessData, OriginTerm, RelationData, Trace,
    TraceStep,
};
use crate::field::{Fp, PrimeField};
use crate::order::ORDER_ID;
use crate::quiver::{ArrowId, Quiver};
use crate::relation::{Presentation, Relation};
use std::collections::BTreeMap;

use super::*;

fn f(p: u64) -> PrimeField {
    PrimeField::new(p).unwrap()
}

fn ids(raw: &[u32]) -> Vec<ArrowId> {
    raw.iter().copied().map(ArrowId).collect()
}

fn rel(quiver: &Quiver, field: PrimeField, terms: &[(i64, &[u32])]) -> Relation {
    Relation::new(
        quiver,
        field,
        terms
            .iter()
            .map(|(c, w)| (field.elem(*c), ids(w)))
            .collect(),
    )
    .unwrap()
}

fn completed(presentation: &Presentation) -> Certificate {
    match complete(presentation, &CompletionLimits::default()) {
        Outcome::Complete(certificate) => certificate,
        Outcome::Truncated(diagnostics) => panic!("unexpected truncation: {diagnostics:?}"),
    }
}

fn truncated(presentation: &Presentation, limits: &CompletionLimits) -> TruncationDiagnostics {
    match complete(presentation, limits) {
        Outcome::Complete(_) => panic!("expected truncation"),
        Outcome::Truncated(diagnostics) => diagnostics,
    }
}

fn x_cubed() -> Presentation {
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let field = f(5);
    let r = rel(&quiver, field, &[(1, &[0, 0, 0])]);
    Presentation::new(quiver, field, vec![r]).unwrap()
}

fn commutative_square() -> Presentation {
    let quiver = Quiver::new(4, &[(0, 1), (1, 3), (0, 2), (2, 3)]).unwrap();
    let field = f(5);
    let r = rel(&quiver, field, &[(1, &[0, 1]), (-1, &[2, 3])]);
    Presentation::new(quiver, field, vec![r]).unwrap()
}

/// One vertex, loops x = 0 and y = 1, over F_2. Relations
/// r0 = yx - x² and r1 = y².
fn overlap_example() -> Presentation {
    let quiver = Quiver::new(1, &[(0, 0), (0, 0)]).unwrap();
    let field = f(2);
    let r0 = rel(&quiver, field, &[(1, &[1, 0]), (-1, &[0, 0])]);
    let r1 = rel(&quiver, field, &[(1, &[1, 1])]);
    Presentation::new(quiver, field, vec![r0, r1]).unwrap()
}

fn overlap_example_swapped() -> Presentation {
    let quiver = Quiver::new(1, &[(0, 0), (0, 0)]).unwrap();
    let field = f(2);
    let r0 = rel(&quiver, field, &[(1, &[1, 0]), (-1, &[0, 0])]);
    let r1 = rel(&quiver, field, &[(1, &[1, 1])]);
    Presentation::new(quiver, field, vec![r1, r0]).unwrap()
}

/// Arrows a: 0->1 (0), b: 1->3 (1), c: 0->2 (2), d: 2->4 (3),
/// e: 4->3 (4). The relation cde - ab mixes word lengths 3 and 2.
fn inhomogeneous() -> Presentation {
    let quiver = Quiver::new(5, &[(0, 1), (1, 3), (0, 2), (2, 4), (4, 3)]).unwrap();
    let field = f(5);
    let r = rel(&quiver, field, &[(1, &[2, 3, 4]), (-1, &[0, 1])]);
    Presentation::new(quiver, field, vec![r]).unwrap()
}

/// One loop x over F_2. Relations r0 = x⁵ and r1 = x⁴ + x². The ideal
/// is (x²): the inclusion of x⁴ in x⁵ and the overlaps produce x³ and
/// x². Interreduction drops everything else.
fn inclusion_example() -> Presentation {
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    let field = f(2);
    let r0 = rel(&quiver, field, &[(1, &[0, 0, 0, 0, 0])]);
    let r1 = rel(&quiver, field, &[(1, &[0, 0, 0, 0]), (1, &[0, 0])]);
    Presentation::new(quiver, field, vec![r0, r1]).unwrap()
}

fn one_loop_free() -> Presentation {
    let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
    Presentation::new(quiver, f(2), Vec::new()).unwrap()
}

fn all_examples() -> Vec<Presentation> {
    vec![
        x_cubed(),
        commutative_square(),
        overlap_example(),
        overlap_example_swapped(),
        inhomogeneous(),
        inclusion_example(),
        one_loop_free(),
    ]
}

/// Naive expansion of one origin: `Σ coeff · left · r_i · right`,
/// collected per word, zeros dropped, sorted descending.
fn expand_origin(
    field: PrimeField,
    inputs: &[RelationData],
    origin: &[OriginTerm],
) -> RelationData {
    let mut acc: BTreeMap<Vec<u32>, Fp> = BTreeMap::new();
    for term in origin {
        let c = field.elem(term.coeff as i64);
        for (rc, rw) in &inputs[term.input_index] {
            let mut word = term.left.clone();
            word.extend_from_slice(rw);
            word.extend_from_slice(&term.right);
            let add = field.mul(c, field.elem(*rc as i64));
            let sum = field.add(acc.get(&word).copied().unwrap_or(field.zero()), add);
            if sum.is_zero() {
                acc.remove(&word);
            } else {
                acc.insert(word, sum);
            }
        }
    }
    let mut expanded: Vec<(u64, Vec<u32>)> = acc.into_iter().map(|(w, c)| (c.raw(), w)).collect();
    expanded.sort_by(|(_, a), (_, b)| b.len().cmp(&a.len()).then(b.cmp(a)));
    expanded
}

/// Replays a trace with its own arithmetic: checks every step's word
/// decomposition and that the final value is zero.
fn assert_trace_reduces_to_zero(field: PrimeField, basis: &[RelationData], trace: &Trace) {
    let mut acc: BTreeMap<Vec<u32>, Fp> = BTreeMap::new();
    for (c, w) in &trace.start {
        assert!(acc.insert(w.clone(), field.elem(*c as i64)).is_none());
    }
    for step in &trace.steps {
        let elem = &basis[step.basis_index];
        let mut recomposed = step.left.clone();
        recomposed.extend_from_slice(&elem[0].1);
        recomposed.extend_from_slice(&step.right);
        assert_eq!(step.word, recomposed);
        let c = field.elem(step.coeff as i64);
        for (bc, bw) in elem {
            let mut word = step.left.clone();
            word.extend_from_slice(bw);
            word.extend_from_slice(&step.right);
            let sub = field.mul(c, field.elem(*bc as i64));
            let sum = field.sub(acc.get(&word).copied().unwrap_or(field.zero()), sub);
            if sum.is_zero() {
                acc.remove(&word);
            } else {
                acc.insert(word, sum);
            }
        }
    }
    assert!(acc.is_empty(), "trace does not end at zero: {acc:?}");
}
