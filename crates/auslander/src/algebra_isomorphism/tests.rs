use std::sync::Arc;

use super::*;
use crate::algebra::{commutative_square, linear_an, monomial_algebra};
use crate::monomial::MonomialIdeal;
use crate::quiver::Quiver;

fn field(p: u64) -> PrimeField {
    PrimeField::new(p).unwrap()
}

/// The monomial algebra with quadratic zero relations `(first, second)`.
fn bound(p: u64, vertices: u32, arrows: &[(u32, u32)], relations: &[(u32, u32)]) -> Arc<Algebra> {
    let quiver = Quiver::new(vertices, arrows).unwrap();
    let words = relations
        .iter()
        .map(|&(first, second)| vec![ArrowId(first), ArrowId(second)])
        .collect();
    monomial_algebra(&MonomialIdeal::new(quiver, words).unwrap(), field(p)).unwrap()
}

/// `A_3/(ab)` twice: arrows `0 → 1 → 2`, and the reversed numbering with
/// arrows listed in the other order.
fn relabeled_pair() -> (Arc<Algebra>, Arc<Algebra>) {
    (
        bound(5, 3, &[(0, 1), (1, 2)], &[(0, 1)]),
        bound(5, 3, &[(1, 0), (2, 1)], &[(1, 0)]),
    )
}

#[test]
fn gentle_relabeling_verifies() {
    let (source, target) = relabeled_pair();
    let isomorphism = AlgebraIsomorphism::from_gentle(&source, &target).unwrap();
    assert_eq!(isomorphism.vertex_map(), [2, 1, 0]);
    assert!(isomorphism.verify());
    let reverse = AlgebraIsomorphism::from_gentle(&target, &source).unwrap();
    assert!(reverse.verify());
}

#[test]
fn from_gentle_types_every_mismatch() {
    let (source, _) = relabeled_pair();
    let a3 = linear_an(3, field(5));
    assert_eq!(
        AlgebraIsomorphism::from_gentle(&source, &a3).unwrap_err(),
        GentleMatchError::DifferentKeys
    );
    assert!(matches!(
        AlgebraIsomorphism::from_gentle(&commutative_square(field(5)), &a3),
        Err(GentleMatchError::SourceNotGentle(
            GentleError::NonMonomial { .. }
        ))
    ));
    assert!(matches!(
        AlgebraIsomorphism::from_gentle(&a3, &commutative_square(field(5))),
        Err(GentleMatchError::TargetNotGentle(_))
    ));
    assert_eq!(
        AlgebraIsomorphism::from_gentle(&a3, &linear_an(3, field(2))).unwrap_err(),
        GentleMatchError::FieldMismatch {
            source: 5,
            target: 2
        }
    );
}

#[test]
fn tampered_isomorphisms_fail() {
    let (source, target) = relabeled_pair();
    let valid = AlgebraIsomorphism::from_gentle(&source, &target).unwrap();
    let f5 = field(5);
    let mut cases = Vec::new();
    let mut tampered = valid.clone();
    tampered.vertex_map = vec![2, 2, 0];
    cases.push(("vertex map not injective", tampered));
    let mut tampered = valid.clone();
    tampered.vertex_map.pop();
    cases.push(("vertex map too short", tampered));
    let mut tampered = valid.clone();
    tampered.arrow_images.swap(0, 1);
    cases.push(("images in the wrong corners", tampered));
    let mut tampered = valid.clone();
    tampered.arrow_images[0] = vec![f5.zero(); target.dim()];
    cases.push(("images do not span", tampered));
    let mut tampered = valid.clone();
    let vertex = tampered.vertex_map[0] as usize;
    tampered.arrow_images[0][vertex] = f5.one();
    cases.push(("image outside the radical", tampered));
    let mut tampered = valid.clone();
    tampered.arrow_images[1].push(f5.zero());
    cases.push(("image of the wrong length", tampered));
    let mut tampered = valid.clone();
    tampered.target = linear_an(3, f5);
    cases.push(("dimensions differ", tampered));
    for (name, tampered) in cases {
        assert!(!tampered.verify(), "{name}");
    }
}

/// The 2-cycle `a: 0 → 1`, `b: 1 → 0` with `a·b = 0` has basis
/// `e_0, e_1, a, b, b·a`. The version with `b·a = 0` has the same dimension
/// and arrow space. The identity on arrows passes every check except the
/// relation: `a·b` maps to the nonzero word `a·b`.
#[test]
fn a_relation_that_survives_fails() {
    let source = bound(5, 2, &[(0, 1), (1, 0)], &[(0, 1)]);
    let target = bound(5, 2, &[(0, 1), (1, 0)], &[(1, 0)]);
    let identity = AlgebraIsomorphism::between_equal(&source, &target);
    assert!(identity.vertices_biject() && identity.spans_arrow_space());
    assert!(!identity.verify());
    let swapped = AlgebraIsomorphism::from_gentle(&source, &target).unwrap();
    assert_eq!(swapped.vertex_map(), [1, 0]);
    assert!(swapped.verify());
}

/// The basis index of the path `arrows` in `algebra`.
fn word_index(algebra: &Algebra, arrows: &[u32]) -> usize {
    let ids: Vec<_> = arrows.iter().map(|&a| ArrowId(a)).collect();
    let word = PathWord::from_arrows(algebra.quiver(), &ids).unwrap();
    algebra.path_index(&word).unwrap().unwrap()
}

/// Two parallel arrows `a, b: 0 → 1` and `c: 1 → 2` with `a·c = 0`, and the
/// same bound quiver with its arrows listed as `c, b, a`. Only the relation
/// tells `a` from `b`, so swapping their images fails the relation check.
#[test]
fn parallel_arrows_are_matched_by_their_relations() {
    let source = bound(5, 3, &[(0, 1), (0, 1), (1, 2)], &[(0, 2)]);
    let target = bound(5, 3, &[(1, 2), (0, 1), (0, 1)], &[(2, 0)]);
    let isomorphism = AlgebraIsomorphism::from_gentle(&source, &target).unwrap();
    assert_eq!(isomorphism.vertex_map(), [0, 1, 2]);
    let images: Vec<usize> = isomorphism
        .arrow_images()
        .iter()
        .map(|image| image.iter().position(|v| !v.is_zero()).unwrap())
        .collect();
    let expected: Vec<usize> = [2, 1, 0]
        .iter()
        .map(|&a| word_index(&target, &[a]))
        .collect();
    assert_eq!(images, expected);
    assert!(isomorphism.verify());
    let mut swapped = isomorphism.clone();
    swapped.arrow_images.swap(0, 1);
    assert!(swapped.vertices_biject() && swapped.spans_arrow_space());
    assert!(!swapped.verify());
}

/// A loop `x` at vertex 0 with `x·x = 0` and an arrow `a: 0 → 1`, and its
/// copy with the vertices swapped. The map `x ↦ 2x'`, `a ↦ a' + x'·a'` is
/// not a relabeling, but it is an isomorphism, and the verifier accepts it.
#[test]
fn a_loop_with_a_non_monomial_image_verifies() {
    let source = bound(5, 2, &[(0, 0), (0, 1)], &[(0, 0)]);
    let target = bound(5, 2, &[(1, 0), (1, 1)], &[(1, 1)]);
    let relabeling = AlgebraIsomorphism::from_gentle(&source, &target).unwrap();
    assert_eq!(relabeling.vertex_map(), [1, 0]);
    assert!(relabeling.verify());
    let f5 = field(5);
    let mut images = vec![vec![f5.zero(); target.dim()]; 2];
    images[0][word_index(&target, &[1])] = f5.elem(2);
    images[1][word_index(&target, &[0])] = f5.one();
    images[1][word_index(&target, &[1, 0])] = f5.one();
    let twisted = AlgebraIsomorphism {
        arrow_images: images,
        ..relabeling.clone()
    };
    assert!(twisted.verify());
    // `a ↦ x'·a'` lies in the right corner but in `J²`, so it spans nothing.
    let mut degenerate = twisted.clone();
    degenerate.arrow_images[1][word_index(&target, &[0])] = f5.zero();
    assert!(degenerate.image_in_corner(1) && !degenerate.verify());
}

#[test]
fn family_index_matches_and_reports_duplicates() {
    let (source, target) = relabeled_pair();
    let square = commutative_square(field(5));
    let family = vec![
        linear_an(3, field(5)),
        target.clone(),
        square.clone(),
        commutative_square(field(5)),
        source.clone(),
    ];
    let index = FamilyIndex::new(&family).unwrap();
    let duplicates: Vec<_> = (0..family.len()).map(|m| index.duplicate_of(m)).collect();
    assert_eq!(duplicates, [None, None, None, Some(2), Some(1)]);
    let (member, isomorphism) = index.match_member(&source).unwrap();
    assert_eq!(member, 1);
    assert!(isomorphism.verify());
    let (member, isomorphism) = index.match_member(&square).unwrap();
    assert_eq!(member, 2);
    assert!(isomorphism.verify());
    assert!(index.duplicate_isomorphism(3, 2).verify());
    assert!(index.duplicate_isomorphism(4, 1).verify());
    assert!(index.match_member(&linear_an(4, field(5))).is_none());
    assert!(index.match_member(&linear_an(3, field(2))).is_none());
}

#[test]
fn family_index_rejects_mixed_fields() {
    let family = vec![linear_an(2, field(5)), linear_an(2, field(3))];
    assert_eq!(
        FamilyIndex::new(&family).unwrap_err(),
        FamilyFieldError {
            member: 1,
            expected: 5,
            found: 3
        }
    );
    assert_eq!(FamilyIndex::new(&[]).unwrap().field(), None);
}
