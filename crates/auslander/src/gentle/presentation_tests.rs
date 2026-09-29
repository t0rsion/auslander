use std::sync::Arc;

use super::*;
use crate::algebra::{Algebra, monomial_algebra, path_algebra};
use crate::field::PrimeField;
use crate::monomial::MonomialIdeal;
use crate::quiver::{ArrowId, Quiver};

fn f3() -> PrimeField {
    PrimeField::new(3).unwrap()
}

pub(super) fn bound(
    vertices: u32,
    arrows: &[(u32, u32)],
    relations: &[(u32, u32)],
) -> Arc<Algebra> {
    let quiver = Quiver::new(vertices, arrows).unwrap();
    let words = relations
        .iter()
        .map(|&(first, second)| vec![ArrowId(first), ArrowId(second)])
        .collect();
    monomial_algebra(&MonomialIdeal::new(quiver, words).unwrap(), f3()).unwrap()
}

fn aag(algebra: &Arc<Algebra>) -> Vec<(usize, usize)> {
    GentlePresentation::new(algebra)
        .unwrap()
        .aag_function()
        .pairs()
        .to_vec()
}

fn sorted(mut pairs: Vec<(usize, usize)>) -> Vec<(usize, usize)> {
    pairs.sort_unstable();
    pairs
}

/// `Ã_{p,q}`: one cycle, `p` arrows on one side and `q` on the other, no relations.
fn affine_a(p: u32, q: u32) -> Arc<Algebra> {
    let mut arrows: Vec<(u32, u32)> = (0..p).map(|i| (i, i + 1)).collect();
    let mut previous = 0;
    for step in 1..q {
        arrows.push((previous, p + step));
        previous = p + step;
    }
    arrows.push((previous, p));
    bound(p + q, &arrows, &[])
}

/// `Λ(r, n, m)` of Bobiński, Geiss, and Skowroński: the oriented cycle
/// `α_i: i → i + 1 mod n`, the relations `α_j·α_{j+1}` for the last `r`
/// arrows `α_j`, and a tail of `m` arrows into vertex 0.
fn lambda(r: u32, n: u32, m: u32) -> Arc<Algebra> {
    let mut arrows: Vec<(u32, u32)> = (0..n).map(|i| (i, (i + 1) % n)).collect();
    arrows.extend((1..=m).map(|j| (n + j - 1, if j == 1 { 0 } else { n + j - 2 })));
    let relations: Vec<(u32, u32)> = (n - r..n).map(|j| (j, (j + 1) % n)).collect();
    bound(n + m, &arrows, &relations)
}

#[test]
fn linear_a_n_has_the_function_of_its_derived_class() {
    for n in 1..=6u32 {
        let algebra = crate::algebra::linear_an(n as usize, f3());
        let presentation = GentlePresentation::new(&algebra).unwrap();
        let n = n as usize;
        assert_eq!(presentation.aag_function().pairs(), [(n + 1, n - 1)]);
        assert_eq!(
            presentation.aag_function().to_string(),
            format!("[({}, {})]", n + 1, n - 1)
        );
        assert_eq!(presentation.genus(), 0);
    }
}

// Avella-Alaminos and Geiss, section 7, case (2): a hereditary algebra of type
// Ã_{p,q} has φ = [(p, p), (q, q)].
#[test]
fn affine_a_has_one_pair_per_side() {
    for (p, q) in [(1, 1), (1, 2), (2, 2), (1, 3), (2, 3)] {
        let (p_len, q_len) = (p as usize, q as usize);
        assert_eq!(
            aag(&affine_a(p, q)),
            sorted(vec![(p_len, p_len), (q_len, q_len)])
        );
    }
}

// Avella-Alaminos and Geiss, section 7, case (3): φ_{Λ(r,n,m)} =
// [(r + m, m), (n - r, n)]. With r = n the second pair is a full relation cycle.
#[test]
fn discrete_derived_lambda_algebras_match_the_paper() {
    for (r, n, m) in [
        (1, 1, 0),
        (1, 1, 2),
        (1, 2, 0),
        (2, 2, 0),
        (1, 3, 1),
        (2, 3, 2),
        (3, 3, 1),
    ] {
        let expected = sorted(vec![
            ((r + m) as usize, m as usize),
            ((n - r) as usize, n as usize),
        ]);
        assert_eq!(aag(&lambda(r, n, m)), expected, "Λ({r}, {n}, {m})");
    }
    let dual = GentlePresentation::new(&crate::algebra::dual_numbers(f3())).unwrap();
    assert_eq!(dual.aag_function().to_string(), "[(0, 1), (1, 0)]");
    assert_eq!(dual.full_relation_cycles(), [vec![ArrowId(0)]]);
}

// Avella-Alaminos and Geiss, Example 7: φ_A = [(3, 2), (2, 4), (2, 3)]. Vertices
// a..h are 0..7 and arrow α_i is ArrowId(i - 1). The paper's relation α_4α_2
// is α_2·α_4 here.
#[test]
fn example_seven_of_the_paper() {
    let arrows = [
        (0, 4),
        (4, 5),
        (5, 6),
        (5, 0),
        (0, 1),
        (1, 2),
        (2, 7),
        (4, 3),
        (6, 7),
    ];
    let algebra = bound(8, &arrows, &[(1, 3), (3, 0), (0, 7), (4, 5)]);
    let presentation = GentlePresentation::new(&algebra).unwrap();
    assert_eq!(
        presentation.aag_function().pairs(),
        [(2, 3), (2, 4), (3, 2)]
    );
    assert_eq!(presentation.permitted_threads().len(), 7);
    assert_eq!(presentation.genus(), 0);
    let long = presentation
        .permitted_threads()
        .iter()
        .find(|thread| thread.length() == 4)
        .unwrap();
    assert_eq!(
        long.arrows(),
        [ArrowId(0), ArrowId(1), ArrowId(2), ArrowId(8)]
    );
}

#[test]
fn recognition_accepts_loops_parallel_arrows_and_full_relation_cycles() {
    let kronecker = GentlePresentation::new(&crate::algebra::kronecker(2, f3())).unwrap();
    assert_eq!(kronecker.aag_function().pairs(), [(1, 1), (1, 1)]);
    let cycle = crate::algebra::radical_square_zero_cycle(3, f3());
    let cycle = GentlePresentation::new(&cycle).unwrap();
    assert_eq!(cycle.aag_function().pairs(), [(0, 3), (3, 0)]);
    assert_eq!(cycle.full_relation_cycles().len(), 1);
    assert!(
        cycle
            .forbidden_threads()
            .iter()
            .all(GentleThread::is_trivial)
    );
    let two_loops = bound(2, &[(0, 0), (0, 1), (1, 1)], &[(0, 0), (2, 2)]);
    let two_loops = GentlePresentation::new(&two_loops).unwrap();
    assert_eq!(two_loops.aag_function().pairs(), [(0, 1), (0, 1), (1, 1)]);
    assert_eq!(two_loops.genus(), 0);
}

// Arrows a: 0 → 1, b: 1 → 0, c: 0 → 1 with relations c·b and b·a. The one
// permitted thread a·b·c and the one forbidden thread c·b·a close one orbit, so
// φ = [(1, 3)] and g = (2 - 1 - 1 + 2) / 2 = 1.
#[test]
fn a_two_vertex_presentation_has_genus_one() {
    let algebra = bound(2, &[(0, 1), (1, 0), (0, 1)], &[(2, 1), (1, 0)]);
    let presentation = GentlePresentation::new(&algebra).unwrap();
    assert_eq!(presentation.aag_function().pairs(), [(1, 3)]);
    assert_eq!(presentation.permitted_threads().len(), 1);
    assert_eq!(presentation.genus(), 1);
}

#[test]
fn recognition_errors_are_typed() {
    let square = crate::algebra::commutative_square(f3());
    assert_eq!(
        GentlePresentation::new(&square).unwrap_err(),
        GentleError::NonMonomial {
            relation: 0,
            terms: 2
        }
    );
    let long = crate::algebra::an_with_relations(4, &[(0, 3)], f3()).unwrap();
    assert_eq!(
        GentlePresentation::new(&long).unwrap_err(),
        GentleError::NonQuadratic {
            relation: 0,
            length: 3
        }
    );
    let disconnected = path_algebra(Quiver::new(2, &[]).unwrap(), f3()).unwrap();
    assert_eq!(
        GentlePresentation::new(&disconnected).unwrap_err(),
        GentleError::Disconnected {
            vertices: 2,
            reachable: 1
        }
    );
    let star = bound(4, &[(1, 0), (2, 0), (3, 0)], &[]);
    assert_eq!(
        GentlePresentation::new(&star).unwrap_err(),
        GentleError::IncomingDegree {
            vertex: 0,
            count: 3
        }
    );
    let fork = bound(3, &[(0, 1), (1, 1), (1, 2)], &[(1, 1)]);
    assert_eq!(
        GentlePresentation::new(&fork).unwrap_err(),
        GentleError::MultiplePermittedSuccessors {
            arrow: ArrowId(0),
            count: 2
        }
    );
    let doubly = bound(3, &[(0, 1), (1, 2), (1, 2)], &[(0, 1), (0, 2)]);
    assert_eq!(
        GentlePresentation::new(&doubly).unwrap_err(),
        GentleError::MultipleForbiddenSuccessors {
            arrow: ArrowId(0),
            count: 2
        }
    );
}

/// The algebra of the quiver with no vertex is `0`. Both routes reject it
/// before any other check.
#[test]
fn the_empty_quiver_is_rejected_by_both_routes() {
    let zero = path_algebra(Quiver::new(0, &[]).unwrap(), f3()).unwrap();
    assert_eq!(zero.dim(), 0);
    assert_eq!(
        GentlePresentation::new(&zero).unwrap_err(),
        GentleError::EmptyQuiver
    );
    assert_eq!(
        crate::gentle::gentle_tree_strings(&zero).unwrap_err(),
        GentleError::EmptyQuiver
    );
}

#[test]
fn the_tree_route_keeps_its_first_error_when_general_checks_also_fail() {
    // A loop at a vertex with three incoming arrows: general recognition
    // reports the degree, the tree route still reports the loop first.
    let algebra = bound(3, &[(0, 0), (1, 0), (2, 0)], &[(0, 0)]);
    assert_eq!(
        GentlePresentation::new(&algebra).unwrap_err(),
        GentleError::IncomingDegree {
            vertex: 0,
            count: 3
        }
    );
    assert_eq!(
        gentle_tree_strings(&algebra).unwrap_err(),
        GentleError::Loop {
            arrow: ArrowId(0),
            vertex: 0
        }
    );
}
