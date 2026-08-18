//! The sealed order, checked from outside the crate.
//!
//! `order.rs` carries the one order every certificate rests on: completion
//! reduces in it, the certificate names it by [`ORDER_ID`], and the verifier
//! rechecks each reduction descends in it. The module documentation claims the
//! order is admissible, and this file checks the three parts of that claim
//! that are computable, over every word of a small quiver.
//!
//! The quiver is one vertex with three loops. Every arrow sequence over its
//! three arrows is a path of the quiver, and every concatenation of two paths
//! is defined, so "all short words of a small quiver" and "all short arrow
//! sequences" are the same set here and the two-sided compatibility law has no
//! undefined products to skip.
//!
//! Well-foundedness is not checked here. It is a statement about infinite
//! descending chains, and the argument is the one in the module
//! documentation: a longer word is always larger, and there are finitely many
//! words of each length.

use std::cmp::Ordering;

use auslander::order::{ORDER_ID, word_cmp};
use auslander::quiver::{ArrowId, Quiver};

/// Words of length at most 3 over the arrows of the quiver, including the
/// empty word: 1 + 3 + 9 + 27 = 40 of them.
const MAX_LEN: usize = 3;

/// One vertex, three loops. Every word over the three arrows is a path.
fn loop_quiver() -> Quiver {
    Quiver::new(1, &[(0, 0), (0, 0), (0, 0)]).expect("both endpoints are vertex 0")
}

/// Every word of length at most `max_len` over the arrows of `quiver`, in no
/// particular order.
fn words(quiver: &Quiver, max_len: usize) -> Vec<Vec<ArrowId>> {
    let alphabet: Vec<ArrowId> = (0..quiver.num_arrows())
        .map(|i| ArrowId(i as u32))
        .collect();
    let mut all = vec![Vec::new()];
    let mut level = vec![Vec::new()];
    for _ in 0..max_len {
        let mut next = Vec::new();
        for word in &level {
            for &id in &alphabet {
                let mut extended = word.clone();
                extended.push(id);
                next.push(extended);
            }
        }
        all.extend(next.iter().cloned());
        level = next;
    }
    all
}

/// The certificate format names the order by this string, so a change to the
/// comparison without a change to the identifier would let an old certificate
/// verify against a new order.
#[test]
fn the_order_identifier_is_the_sealed_one() {
    assert_eq!(ORDER_ID, "deglex-arrowid-v1");
}

/// The three loops are arrows of one quiver, so the words below are paths and
/// every concatenation of two of them is defined.
#[test]
fn every_word_of_the_loop_quiver_is_a_path() {
    let quiver = loop_quiver();
    assert_eq!(quiver.num_vertices(), 1);
    assert_eq!(quiver.num_arrows(), 3);
    for i in 0..quiver.num_arrows() {
        let a = ArrowId(i as u32);
        assert_eq!(quiver.source(a), quiver.target(a));
    }
    assert_eq!(words(&quiver, MAX_LEN).len(), 40);
}

/// Antisymmetry: reversing the arguments reverses the answer, on all 1600
/// ordered pairs. Equality is included, since `Ordering::Equal` reverses to
/// itself.
#[test]
fn the_order_is_antisymmetric_on_every_short_word() {
    let all = words(&loop_quiver(), MAX_LEN);
    for a in &all {
        for b in &all {
            assert_eq!(
                word_cmp(a, b),
                word_cmp(b, a).reverse(),
                "{a:?} against {b:?}"
            );
        }
        assert_eq!(word_cmp(a, a), Ordering::Equal);
    }
}

/// Transitivity, on all 64000 ordered triples. Checked for `Less` and for
/// `Equal`: equal words are identical here, but the assertion states the law
/// rather than the representation.
#[test]
fn the_order_is_transitive_on_every_short_word() {
    let all = words(&loop_quiver(), MAX_LEN);
    for a in &all {
        for b in &all {
            let ab = word_cmp(a, b);
            for c in &all {
                let bc = word_cmp(b, c);
                if ab == Ordering::Less && bc == Ordering::Less {
                    assert_eq!(word_cmp(a, c), Ordering::Less, "{a:?} {b:?} {c:?}");
                }
                if ab == Ordering::Equal && bc == Ordering::Equal {
                    assert_eq!(word_cmp(a, c), Ordering::Equal, "{a:?} {b:?} {c:?}");
                }
            }
        }
    }
}

/// Totality on the words between two fixed vertices. The loop quiver has one
/// vertex, so every pair of distinct words is a pair of parallel paths and
/// none of them may compare `Equal`.
#[test]
fn the_order_is_total_on_the_parallel_paths() {
    let all = words(&loop_quiver(), MAX_LEN);
    for (i, a) in all.iter().enumerate() {
        for (j, b) in all.iter().enumerate() {
            if i == j {
                continue;
            }
            assert_ne!(word_cmp(a, b), Ordering::Equal, "{a:?} ties with {b:?}");
        }
    }
}

/// Compatibility with concatenation on both sides: `a < b` implies
/// `w.a < w.b` and `a.w < b.w`, over every ordered pair of words of length at
/// most 3 and every context of length at most 2.
///
/// This is the property the certificate format depends on. A reduction
/// rewrites a subword in place, and the certificate claims the whole word
/// descends; that claim is exactly two-sided compatibility applied to the
/// prefix and the suffix around the rewritten part.
#[test]
fn the_order_is_compatible_with_two_sided_concatenation() {
    let quiver = loop_quiver();
    let all = words(&quiver, MAX_LEN);
    let contexts = words(&quiver, 2);
    for a in &all {
        for b in &all {
            if word_cmp(a, b) != Ordering::Less {
                continue;
            }
            for left in &contexts {
                for right in &contexts {
                    let wa: Vec<ArrowId> = left.iter().chain(a).chain(right).copied().collect();
                    let wb: Vec<ArrowId> = left.iter().chain(b).chain(right).copied().collect();
                    assert_eq!(
                        word_cmp(&wa, &wb),
                        Ordering::Less,
                        "{left:?} . {a:?} . {right:?} against {left:?} . {b:?} . {right:?}"
                    );
                }
            }
        }
    }
}

/// The two clauses of the comparison, stated on the shortest witnesses.
///
/// Length first: `[1, 1]` has length 2 and `[0, 0, 0]` length 3, so the
/// shorter word is smaller even though its arrow ids are larger. On equal
/// length, the arrow sequence decides: `[0, 1]` is below `[1, 0]`. The empty
/// word is the minimum, since every other word is longer.
#[test]
fn the_order_compares_length_first_then_arrow_ids() {
    let ids = |raw: &[u32]| -> Vec<ArrowId> { raw.iter().copied().map(ArrowId).collect() };
    assert_eq!(word_cmp(&ids(&[1, 1]), &ids(&[0, 0, 0])), Ordering::Less);
    assert_eq!(word_cmp(&ids(&[0, 1]), &ids(&[1, 0])), Ordering::Less);
    assert_eq!(word_cmp(&ids(&[0, 2]), &ids(&[1, 0])), Ordering::Less);
    let all = words(&loop_quiver(), MAX_LEN);
    for word in &all {
        if word.is_empty() {
            continue;
        }
        assert_eq!(
            word_cmp(&[], word),
            Ordering::Less,
            "empty against {word:?}"
        );
    }
}
