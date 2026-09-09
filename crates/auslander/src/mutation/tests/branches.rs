use super::fixtures::{
    assert_target, d4, f5, fields, left, no_left, pair_of, regular_pair, semisimple,
};
use crate::algebra::{linear_an, truncated_poly};
use crate::module::Module;
use crate::mutation::{ExchangeShape, MutationError, SlotOutcome, mutate_at, mutate_at_with_cache};
use crate::taurigid::TauCache;

// The pentagon of A_2, computed by hand.
// Vertices in crate indexing (0-based, arrow 0 -> 1):
//
//   v1 = (P_0 + P_1, 0)      P_0 = (1,1), P_1 = (0,1) = S_1
//   v2 = (P_0 + S_0, 0)      S_0 = (1,0)
//   v3 = (S_0, P_1)
//   v4 = (P_1, P_0)
//   v5 = (0, P_0 + P_1)
//
// Left mutations, one line per slot:
//
//   v1 at P_0: U = P_1, Fac U = add P_1, so P_0 is outside it. supp U =
//     {1} is smaller than supp M = {0,1}, so the slot moves to the
//     projective part at vertex 0 and the target is v4. Hom(P_0, P_1) = 0,
//     so the approximation is the zero map into the zero module.
//   v1 at P_1: U = P_0. Every quotient of a sum of copies of P_0 has top a
//     sum of S_0, and top P_1 = S_1, so P_1 is outside Fac U. supp U =
//     {0,1} = supp M, so the cokernel carries the exchange: the minimal
//     left add(P_0)-approximation is the socle inclusion P_1 -> P_0 and
//     coker is S_0. Target v2.
//   v2 at P_0: U = S_0, and P_0 is outside add S_0 = Fac S_0. supp U = {0}
//     is smaller than {0,1}, so vertex 1 joins the projective part and the
//     target is v3. The approximation P_0 -> S_0 is onto with kernel P_1,
//     which the construction never touches.
//   v2 at S_0: S_0 = top P_0 lies in Fac P_0, so there is no left mutation.
//   v3 at S_0: U = 0 and Fac 0 = {0}, so S_0 is outside it. supp U = {} is
//     smaller than {0}, so vertex 0 joins the projective part: target v5.
//   v4 at P_1: as v3, with vertex 1: target v5.
//   v5 has no module summand, so it has no slot.
#[test]
fn a2_pentagon_slot_by_slot() {
    for field in fields() {
        let algebra = linear_an(2, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let s0 = Module::simple(&algebra, 0);

        let v1 = pair_of(&algebra, &[&p0, &p1], &[]);
        let v2 = pair_of(&algebra, &[&p0, &s0], &[]);
        let v3 = pair_of(&algebra, &[&s0], &[1]);
        let v4 = pair_of(&algebra, &[&p1], &[0]);
        let v5 = pair_of(&algebra, &[], &[0, 1]);

        let at_p0 = left(&v1, &[1, 1]);
        assert_target(&at_p0, &[&[0, 1]], &[0]);
        assert_eq!(
            *at_p0.shape(),
            ExchangeShape::MovesToProjective { vertex: 0 }
        );
        assert!(at_p0.witness().approximation().map().target().is_zero());

        let at_p1 = left(&v1, &[0, 1]);
        assert_target(&at_p1, &[&[1, 1], &[1, 0]], &[]);
        assert_eq!(
            *at_p1.shape(),
            ExchangeShape::ReplacedByModule { multiplicity: 1 }
        );
        assert_eq!(
            at_p1.witness().replacement().map(|y| y.dim_vector()),
            Some([1, 0].as_slice())
        );

        let v2_at_p0 = left(&v2, &[1, 1]);
        assert_target(&v2_at_p0, &[&[1, 0]], &[1]);
        assert_eq!(
            *v2_at_p0.shape(),
            ExchangeShape::MovesToProjective { vertex: 1 }
        );

        let fac = no_left(&v2, &[1, 0]);
        assert_eq!(fac.image_dims(), [1, 0]);
        assert_eq!(fac.maps().len(), 1);

        let v3_at_s0 = left(&v3, &[1, 0]);
        assert_target(&v3_at_s0, &[], &[0, 1]);
        assert_eq!(
            *v3_at_s0.shape(),
            ExchangeShape::MovesToProjective { vertex: 0 }
        );

        let v4_at_p1 = left(&v4, &[0, 1]);
        assert_target(&v4_at_p1, &[], &[0, 1]);
        assert_eq!(
            *v4_at_p1.shape(),
            ExchangeShape::MovesToProjective { vertex: 1 }
        );

        assert_eq!(v5.module().len(), 0);
        assert!(matches!(
            mutate_at(&v5, 0),
            Err(MutationError::SlotOutOfRange {
                slot: 0,
                summands: 0
            })
        ));
    }
}

// The semisimple algebra on two vertices, spike section 3.1. Every module
// is projective, so tau is zero and a pair is any assignment of P_0 and P_1 to
// the module part or the projective part: four vertices. Fac U is
// add U here, so no module summand ever lies in Fac of the rest and every
// slot mutates. Each mutation moves its summand to the projective part,
// which makes the graph the 2-cube.
#[test]
fn semisimple_two_vertex_cube() {
    for field in fields() {
        let algebra = semisimple(2, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);

        let top = pair_of(&algebra, &[&p0, &p1], &[]);
        let left_side = pair_of(&algebra, &[&p1], &[0]);
        let right_side = pair_of(&algebra, &[&p0], &[1]);
        let bottom = pair_of(&algebra, &[], &[0, 1]);

        let drop_p0 = left(&top, &[1, 0]);
        assert_target(&drop_p0, &[&[0, 1]], &[0]);
        assert_eq!(
            *drop_p0.shape(),
            ExchangeShape::MovesToProjective { vertex: 0 }
        );

        let drop_p1 = left(&top, &[0, 1]);
        assert_target(&drop_p1, &[&[1, 0]], &[1]);

        let down_left = left(&left_side, &[0, 1]);
        assert_target(&down_left, &[], &[0, 1]);

        let down_right = left(&right_side, &[1, 0]);
        assert_target(&down_right, &[], &[0, 1]);

        assert_eq!(bottom.module().len(), 0);
    }
}

// Ten of the 21 edges of linear_an(3), spike section 3.3, with the
// vertices named as in its table. Crate indexing is 0-based, so the
// interval [i,j] of the spike is [i-1,j-1] here:
//
//   P_0 = (1,1,1)   P_1 = (0,1,1)   P_2 = (0,0,1)
//   S_0 = (1,0,0)   S_1 = (0,1,0)   I_1 = (1,1,0)
//
//   A = (P_0 + S_0 + P_2, 0)   B = (A, 0)          C = (P_0 + P_1 + S_1, 0)
//   E = (P_0 + I_1 + S_0, 0)   G = (P_1 + P_2, P_0)
//   H = (S_0 + P_2, P_1)       K = (P_2, P_0 + P_1)
//   M = (S_0, P_1 + P_2)       N = (0, A)
//
// Quotients of an interval module [a,b] are the intervals [a,c], so Fac
// membership is a finite check by hand. Hom([a,b],[c,d]) is nonzero
// exactly when c <= a <= d <= b, which fixes the approximations.
//
//   B at P_2: U = P_0 + P_1, whose quotients are [0,0], [0,1], [0,2],
//     [1,1], [1,2]; P_2 = [2,2] is not among them. supp U = {0,1,2} is all
//     of supp M, so the exchange runs through the cokernel. Hom(P_2, P_0)
//     factors through Hom(P_2, P_1) . Hom(P_1, P_0), so the only generator
//     is P_2 -> P_1 and coker is S_1. Target C.
//   B at P_1: U = P_0 + P_2. Hom(P_0, P_1) = 0 and the image of
//     Hom(P_2, P_1) is P_2, so the trace is P_2 and P_1 is outside Fac U.
//     supp U is everything, the generator is P_1 -> P_0, and coker is S_0.
//     Target A.
//   B at P_0: U = P_1 + P_2 has support {1,2}, so P_0 is outside Fac U and
//     vertex 0 moves to the projective part. Target G.
//   A at P_2: U = P_0 + S_0. Hom(P_2, S_0) = 0 and Hom(P_2, P_0) is the
//     socle inclusion, which is the one generator; coker is I_1. Target E.
//   A at S_0: S_0 = top P_0 lies in Fac U, so no left mutation.
//   A at P_0: U = S_0 + P_2 has support {0,2}, so vertex 1 moves to the
//     projective part. Target H.
//   H at P_2: U = S_0 has support {0}, so vertex 2 moves across. Target M.
//   H at S_0: U = P_2 has support {2}, so vertex 0 moves across. Target K.
//   K at P_2 and M at S_0: U = 0 in both, so the one support vertex moves
//     across. Both land on N.
#[test]
fn linear_an_3_pinned_edges() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let p2 = Module::projective(&algebra, 2);
        let s0 = Module::simple(&algebra, 0);
        // I_1 is the interval module (1,1,0), which the targets below
        // reach as a cokernel rather than as a fixture.
        assert_eq!(Module::injective(&algebra, 1).dim_vector(), [1, 1, 0]);

        let vertex_a = pair_of(&algebra, &[&p0, &s0, &p2], &[]);
        let vertex_b = pair_of(&algebra, &[&p0, &p1, &p2], &[]);
        let vertex_h = pair_of(&algebra, &[&s0, &p2], &[1]);
        let vertex_k = pair_of(&algebra, &[&p2], &[0, 1]);
        let vertex_m = pair_of(&algebra, &[&s0], &[1, 2]);

        let b_at_p2 = left(&vertex_b, &[0, 0, 1]);
        assert_target(&b_at_p2, &[&[1, 1, 1], &[0, 1, 1], &[0, 1, 0]], &[]);
        assert_eq!(
            *b_at_p2.shape(),
            ExchangeShape::ReplacedByModule { multiplicity: 1 }
        );

        let b_at_p1 = left(&vertex_b, &[0, 1, 1]);
        assert_target(&b_at_p1, &[&[1, 1, 1], &[0, 0, 1], &[1, 0, 0]], &[]);

        let b_at_p0 = left(&vertex_b, &[1, 1, 1]);
        assert_target(&b_at_p0, &[&[0, 1, 1], &[0, 0, 1]], &[0]);
        assert_eq!(
            *b_at_p0.shape(),
            ExchangeShape::MovesToProjective { vertex: 0 }
        );

        let a_at_p2 = left(&vertex_a, &[0, 0, 1]);
        assert_target(&a_at_p2, &[&[1, 1, 1], &[1, 0, 0], &[1, 1, 0]], &[]);

        let fac = no_left(&vertex_a, &[1, 0, 0]);
        assert_eq!(fac.image_dims(), [1, 0, 0]);

        let a_at_p0 = left(&vertex_a, &[1, 1, 1]);
        assert_target(&a_at_p0, &[&[1, 0, 0], &[0, 0, 1]], &[1]);
        assert_eq!(
            *a_at_p0.shape(),
            ExchangeShape::MovesToProjective { vertex: 1 }
        );

        let h_at_p2 = left(&vertex_h, &[0, 0, 1]);
        assert_target(&h_at_p2, &[&[1, 0, 0]], &[1, 2]);

        let h_at_s0 = left(&vertex_h, &[1, 0, 0]);
        assert_target(&h_at_s0, &[&[0, 0, 1]], &[0, 1]);

        let k_at_p2 = left(&vertex_k, &[0, 0, 1]);
        assert_target(&k_at_p2, &[], &[0, 1, 2]);

        let m_at_s0 = left(&vertex_m, &[1, 0, 0]);
        assert_target(&m_at_s0, &[], &[0, 1, 2]);
    }
}

// `(A, 0)` is the maximum of the order, so no slot of it can be a right
// mutation. Concretely: dropping P_j leaves U = sum of the other
// projectives, every quotient of a sum of copies of U has top a sum of the
// simples S_v with v not j, and top P_j = S_j, so P_j is outside Fac U.
// The argument uses no property of the algebra, so it holds on both
// fixtures.
#[test]
fn every_slot_of_the_regular_pair_mutates() {
    for field in fields() {
        for algebra in [linear_an(3, field), d4(field)] {
            let pair = regular_pair(&algebra);
            assert_eq!(pair.module().len(), pair.summand_count());
            for slot in 0..pair.module().len() {
                let outcome = mutate_at(&pair, slot).expect("the regular pair mutates");
                let mutation = match outcome {
                    SlotOutcome::LeftMutation(mutation) => *mutation,
                    SlotOutcome::NoLeftMutation(_) => {
                        panic!("slot {slot} of the regular pair has a left mutation")
                    }
                };
                assert!(mutation.witness().verify());
                assert!(mutation.target().verify());
            }
        }
    }
}

// k[x]/(x^3) has one vertex and two pairs, `(A, 0)` and `(0, A)`. The one
// slot drops the only summand, leaving U = 0 with empty support, so vertex
// 0 moves to the projective part.
#[test]
fn truncated_poly_3_has_one_slot_to_the_zero_pair() {
    for field in fields() {
        let algebra = truncated_poly(3, field).expect("x^3 is admissible");
        let pair = regular_pair(&algebra);
        assert_eq!(pair.module().len(), 1);
        let mutation = left(&pair, &[3]);
        assert_target(&mutation, &[], &[0]);
        assert_eq!(
            *mutation.shape(),
            ExchangeShape::MovesToProjective { vertex: 0 }
        );
        assert!(mutation.target().module().is_empty());
    }
}

// One cache across several mutations answers repeated translates from the
// store. The hit count rising is what shows the cache is shared rather
// than rebuilt per call.
#[test]
fn one_cache_serves_several_mutations() {
    let algebra = linear_an(3, f5());
    let pair = regular_pair(&algebra);
    let indices: Vec<usize> = (0..pair.module().len()).collect();
    let mut cache = TauCache::new();
    let mut hits = Vec::new();
    for slot in 0..pair.module().len() {
        let outcome = mutate_at_with_cache(
            &pair,
            slot,
            &indices,
            indices.len() + slot,
            Some(&mut cache),
        )
        .expect("the regular pair mutates");
        assert!(outcome.is_left_mutation());
        hits.push(cache.hits());
    }
    assert!(hits[0] > 0, "the first call already reuses a translate");
    assert!(
        hits[2] > hits[0],
        "later calls keep hitting the shared store, got {hits:?}"
    );
    assert!(cache.misses() > 0);
}
