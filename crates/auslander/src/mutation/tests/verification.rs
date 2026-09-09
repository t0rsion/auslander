use super::fixtures::{f2, f5, left, no_left, pair_of};
use crate::algebra::linear_an;
use crate::context::VerificationContext;
use crate::module::Module;

#[test]
fn mutation_witness_reuses_context_for_nested_approximation() {
    let algebra = linear_an(2, f5());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let pair = pair_of(&algebra, &[&p0, &p1], &[]);
    let mutation = left(&pair, &[1, 1]);
    let context = VerificationContext::new();

    assert!(mutation.witness().verify_with_context(&context));
    let first_memo = context.memo_stats();
    assert!(first_memo.1 > 0, "the first verification has memo misses");

    assert!(mutation.witness().verify_with_context(&context));
    let second_memo = context.memo_stats();
    assert_eq!(second_memo.1, first_memo.1);
    assert!(
        second_memo.0 > first_memo.0,
        "the second verification has memo hits"
    );
}

// A witness whose target is another slot's target, which is a valid pair
// in its own right. The stored almost complete pair no longer sits inside
// it, so the extension check fails.
#[test]
fn a_swapped_target_fails_verification() {
    let algebra = linear_an(2, f2());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let pair = pair_of(&algebra, &[&p0, &p1], &[]);

    let at_p0 = left(&pair, &[1, 1]);
    let at_p1 = left(&pair, &[0, 1]);
    let mut tampered = at_p0.witness;
    tampered.target_module = at_p1.witness.target_module.clone();
    tampered.target_projective = at_p1.witness.target_projective.clone();
    assert!(!tampered.verify());
}

// An approximation borrowed from the other slot of the same pair. It
// starts at the wrong summand, which the witness catches before it
// recomputes the exchange sequence.
#[test]
fn a_borrowed_approximation_fails_verification() {
    let algebra = linear_an(2, f2());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let pair = pair_of(&algebra, &[&p0, &p1], &[]);

    let at_p0 = left(&pair, &[1, 1]);
    let at_p1 = left(&pair, &[0, 1]);
    let mut tampered = at_p1.witness;
    tampered.approximation = at_p0.witness.approximation;
    assert!(!tampered.verify());
}

// A witness whose target is the source pair, with the matching extension
// witness moved over so that the add-closure checks pass. What is left is
// the check that the two completions differ, and it fails: AIR Theorem
// 2.18 gives two completions, not one taken twice.
#[test]
fn a_target_equal_to_the_source_fails_verification() {
    let algebra = linear_an(2, f2());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let pair = pair_of(&algebra, &[&p0, &p1], &[]);

    let mut tampered = left(&pair, &[0, 1]).witness;
    tampered.target_module = tampered.source_module.clone();
    tampered.target_projective = tampered.source_projective.clone();
    tampered.target_extension = tampered.source_extension.clone();
    assert!(!tampered.verify());
}

// A Fac witness that lost a map. The remaining images no longer cover
// X_j, which is the rank equality the witness exists to prove.
#[test]
fn a_truncated_fac_witness_fails_verification() {
    let algebra = linear_an(2, f2());
    let p0 = Module::projective(&algebra, 0);
    let s0 = Module::simple(&algebra, 0);
    let pair = pair_of(&algebra, &[&p0, &s0], &[]);

    let mut witness = no_left(&pair, &[1, 0]);
    assert!(witness.verify());
    witness.maps.pop();
    assert!(!witness.verify());
}

// A Fac witness whose summand list is not a decomposition of its stored
// U. The rank equality is proved over U, so a caller reading the summand
// list has to know it belongs to that U, and only the direct-sum check
// says so.
#[test]
fn a_fac_witness_whose_summands_miss_u_fails_verification() {
    // Vertex A of the linear_an(3) table above. S_0 is the top of P_0, so
    // it lies in Fac(P_0 + P_2) and slot S_0 has no left mutation.
    let algebra = linear_an(3, f2());
    let p0 = Module::projective(&algebra, 0);
    let p2 = Module::projective(&algebra, 2);
    let s0 = Module::simple(&algebra, 0);
    let pair = pair_of(&algebra, &[&p0, &s0, &p2], &[]);

    let mut witness = no_left(&pair, &[1, 0, 0]);
    assert_eq!(witness.summands().len(), 2);
    witness.summands.pop();
    assert!(!witness.verify());
}

// A mutation carrying another slot's target pair. Both halves still pass
// on their own, so only the binding between them catches the swap.
#[test]
fn a_mutation_with_another_slot_target_fails_verification() {
    let algebra = linear_an(2, f2());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let pair = pair_of(&algebra, &[&p0, &p1], &[]);

    let mut at_p0 = left(&pair, &[1, 1]);
    let at_p1 = left(&pair, &[0, 1]);
    at_p0.target = at_p1.target;
    assert!(at_p0.witness.verify());
    assert!(at_p0.target.verify());
    assert!(!at_p0.verify());
}

// A witness proves a statement about one slot, so relabelling the
// mutation must not survive verification. Both halves still pass alone.
#[test]
fn a_mutation_relabelled_to_another_slot_fails_verification() {
    let algebra = linear_an(2, f2());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let pair = pair_of(&algebra, &[&p0, &p1], &[]);

    let mut at_p0 = left(&pair, &[1, 1]);
    let other = left(&pair, &[0, 1]);
    assert_ne!(at_p0.slot, other.slot, "the two slots must differ");
    at_p0.slot = other.slot;
    assert!(at_p0.witness.verify());
    assert!(at_p0.target.verify());
    assert!(!at_p0.verify());
}

// Every mutation of the A_2 pentagon leaves the source pair usable, since
// mutate_at takes it by reference and builds fresh modules for the target.
#[test]
fn the_source_pair_survives_a_mutation() {
    let algebra = linear_an(2, f5());
    let p0 = Module::projective(&algebra, 0);
    let p1 = Module::projective(&algebra, 1);
    let pair = pair_of(&algebra, &[&p0, &p1], &[]);
    let _ = left(&pair, &[1, 1]);
    assert!(pair.verify());
}
