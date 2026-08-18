//! The sealed admissible order on path words.
//!
//! The crate has exactly one order, identified by [`ORDER_ID`]. Completion,
//! certificates, and verification all use it. No user-supplied comparators
//! exist.
//!
//! The order is admissible:
//!
//! - Well-founded: a quiver has finitely many arrows, so only finitely many
//!   words are smaller than any given word. Every strictly decreasing chain
//!   is finite.
//! - Total on the paths between any two fixed vertices, because it is total
//!   on all arrow sequences.
//! - Compatible with concatenation on both sides where products are defined:
//!   `a < b` implies `w·a < w·b` and `a·w < b·w`. Lengths grow by the same
//!   amount, and on equal length the shared factor `w` never decides the
//!   lexicographic comparison.

use std::cmp::Ordering;

use crate::quiver::ArrowId;

/// Identifies the sealed order in certificates.
pub const ORDER_ID: &str = "deglex-arrowid-v1";

/// Degree-lexicographic comparison of arrow words.
///
/// Compares length first: the longer word is the larger word. On equal
/// length, compares the arrow sequences lexicographically by [`ArrowId`]
/// numeric order: the larger sequence is the larger word.
pub fn word_cmp(a: &[ArrowId], b: &[ArrowId]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| a.cmp(b))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn w(ids: &[u32]) -> Vec<ArrowId> {
        ids.iter().copied().map(ArrowId).collect()
    }

    /// All words over arrows `0` and `1` with length at most `max_len`.
    fn words_up_to(max_len: usize) -> Vec<Vec<ArrowId>> {
        let mut all = vec![Vec::new()];
        let mut level = vec![Vec::new()];
        for _ in 0..max_len {
            let mut next = Vec::new();
            for word in &level {
                for id in [ArrowId(0), ArrowId(1)] {
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

    #[test]
    fn longer_word_is_larger() {
        assert_eq!(word_cmp(&w(&[1, 1]), &w(&[0, 0, 0])), Ordering::Less);
        assert_eq!(word_cmp(&w(&[0, 0, 0]), &w(&[1, 1])), Ordering::Greater);
        assert_eq!(word_cmp(&w(&[]), &w(&[0])), Ordering::Less);
    }

    #[test]
    fn equal_length_compares_lexicographically_by_arrow_id() {
        assert_eq!(word_cmp(&w(&[0, 1]), &w(&[1, 0])), Ordering::Less);
        assert_eq!(word_cmp(&w(&[1, 0]), &w(&[0, 1])), Ordering::Greater);
        assert_eq!(word_cmp(&w(&[0, 2, 5]), &w(&[0, 3, 0])), Ordering::Less);
    }

    #[test]
    fn equal_words_compare_equal() {
        for word in words_up_to(3) {
            assert_eq!(word_cmp(&word, &word), Ordering::Equal);
        }
    }

    #[test]
    fn antisymmetric_on_all_short_words() {
        let all = words_up_to(3);
        for a in &all {
            for b in &all {
                assert_eq!(word_cmp(a, b), word_cmp(b, a).reverse(), "{a:?} {b:?}");
            }
        }
    }

    #[test]
    fn transitive_on_all_short_words() {
        let all = words_up_to(3);
        for a in &all {
            for b in &all {
                for c in &all {
                    if word_cmp(a, b) == Ordering::Less && word_cmp(b, c) == Ordering::Less {
                        assert_eq!(word_cmp(a, c), Ordering::Less, "{a:?} {b:?} {c:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn compatible_with_concatenation_on_both_sides() {
        let all = words_up_to(3);
        let contexts = words_up_to(2);
        for a in &all {
            for b in &all {
                if word_cmp(a, b) != Ordering::Less {
                    continue;
                }
                for ctx in &contexts {
                    let left_a: Vec<ArrowId> = ctx.iter().chain(a).copied().collect();
                    let left_b: Vec<ArrowId> = ctx.iter().chain(b).copied().collect();
                    assert_eq!(word_cmp(&left_a, &left_b), Ordering::Less);
                    let right_a: Vec<ArrowId> = a.iter().chain(ctx).copied().collect();
                    let right_b: Vec<ArrowId> = b.iter().chain(ctx).copied().collect();
                    assert_eq!(word_cmp(&right_a, &right_b), Ordering::Less);
                }
            }
        }
    }
}
