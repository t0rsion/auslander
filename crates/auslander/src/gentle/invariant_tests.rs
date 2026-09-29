use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::classes_tests::relabel;
use super::presentation_tests::bound;
use super::*;
use crate::algebra::Algebra;
use crate::field::PrimeField;

fn f2() -> PrimeField {
    PrimeField::new(2).unwrap()
}

fn invariant(algebra: &Arc<Algebra>) -> GentleDerivedInvariant {
    GentlePresentation::new(algebra)
        .unwrap()
        .complete_invariant()
}

/// Amiot, Plamondon, and Schroll, section 7, first pair: `Λ_1` is `1 ⇉ 2 ⇉ 3`
/// with two relations.
pub(super) fn aps_first() -> Arc<Algebra> {
    bound(3, &[(0, 1), (0, 1), (1, 2), (1, 2)], &[(0, 2), (1, 3)])
}

/// `Λ_2` of the same pair: `1 → 2 → 3` and two arrows `3 → 1`.
pub(super) fn aps_second() -> Arc<Algebra> {
    bound(
        3,
        &[(0, 1), (1, 2), (2, 0), (2, 0)],
        &[(2, 0), (0, 1), (1, 3)],
    )
}

#[test]
fn the_first_aps_pair_is_separated_by_the_gcd() {
    // APS compute gcd 0 for Λ_1 and gcd 2 for Λ_2, with one boundary
    // component of winding number -2.
    let first = invariant(&aps_first());
    let second = invariant(&aps_second());
    assert_eq!(first.aag_function(), second.aag_function());
    assert_eq!(first.aag_function().pairs(), [(2, 4)]);
    assert_eq!(first.winding_class(), WindingClass::Gcd(0));
    assert_eq!(second.winding_class(), WindingClass::Gcd(2));
    assert_eq!(first.to_string(), "[(2, 4)], genus 1, gcd 0");
    assert_eq!(second.to_string(), "[(2, 4)], genus 1, gcd 2");
}

#[test]
fn the_second_aps_pair_shares_the_invariant() {
    // Section 7 of APS: a torus with two boundary components and a puncture,
    // boundary winding numbers -3, 0, -3, and gcd 1 for both algebras.
    let first = bound(
        6,
        &[
            (4, 0),
            (1, 4),
            (5, 1),
            (5, 3),
            (3, 2),
            (4, 3),
            (2, 4),
            (1, 0),
            (0, 1),
        ],
        &[(6, 5), (4, 6), (5, 4), (1, 0), (0, 8), (8, 7), (2, 1)],
    );
    let second = bound(
        6,
        &[
            (0, 5),
            (1, 0),
            (4, 1),
            (4, 3),
            (1, 2),
            (3, 5),
            (2, 3),
            (5, 2),
            (0, 4),
        ],
        &[(5, 7), (7, 6), (3, 5), (8, 2), (1, 8), (2, 1)],
    );
    let value = invariant(&first);
    assert_eq!(value, invariant(&second));
    assert_eq!(value.genus(), 1);
    assert_eq!(value.winding_class(), WindingClass::Gcd(1));
    let windings: BTreeSet<i64> = value
        .aag_function()
        .pairs()
        .iter()
        .map(|&(n, m)| n as i64 - m as i64)
        .collect();
    assert_eq!(windings, BTreeSet::from([-3, 0]));
}

#[test]
fn the_lekili_polishchuk_koszul_dual_has_gcd_zero() {
    // Example 3.3.3 of Lekili and Polishchuk with every arrow in degree 1:
    // w(α) = w(β) = 0 and both boundary winding numbers are -2.
    let dual = bound(
        6,
        &[
            (0, 1),
            (1, 2),
            (0, 4),
            (4, 2),
            (3, 4),
            (4, 5),
            (3, 1),
            (1, 5),
        ],
        &[(0, 1), (2, 3), (4, 5), (6, 7)],
    );
    let value = invariant(&dual);
    assert_eq!(value.aag_function().pairs(), [(2, 4), (2, 4)]);
    assert_eq!(value.winding_class(), WindingClass::Gcd(0));
}

#[test]
fn genus_zero_reduces_to_the_aag_function() {
    for vertices in 1..=4 {
        for key in connected_gentle_keys(vertices) {
            let presentation = GentlePresentation::new(&key.algebra(f2()).unwrap()).unwrap();
            let value = presentation.complete_invariant();
            assert_eq!(&presentation.aag_function(), value.aag_function());
            assert_eq!(value.genus(), presentation.genus());
            let planar = value.winding_class() == WindingClass::Planar;
            assert_eq!(planar, value.genus() == 0, "{value}");
        }
    }
}

#[test]
fn relabeling_keeps_the_invariant() {
    let mut state = 0x2545_f491_4f6c_dd1du64;
    for key in connected_gentle_keys(4) {
        let value = invariant(&key.algebra(f2()).unwrap());
        if value.genus() == 0 {
            continue;
        }
        for _ in 0..2 {
            assert_eq!(invariant(&relabel(&key, &mut state)), value, "{key:?}");
        }
    }
}

#[test]
fn the_invariant_splits_seven_aag_groups_at_four_vertices() {
    let mut groups: BTreeMap<AagFunction, BTreeSet<GentleDerivedInvariant>> = BTreeMap::new();
    let mut classes: BTreeMap<String, usize> = BTreeMap::new();
    let keys = connected_gentle_keys(4);
    for key in &keys {
        let value = invariant(&key.algebra(f2()).unwrap());
        let name = value.winding_class().to_string();
        let kind = name.split(' ').next().unwrap().to_string();
        *classes.entry(kind).or_default() += 1;
        let group = groups.entry(value.aag_function().clone()).or_default();
        group.insert(value);
    }
    let split: Vec<usize> = groups
        .values()
        .map(BTreeSet::len)
        .filter(|&len| len > 1)
        .collect();
    let total: usize = groups.values().map(BTreeSet::len).sum();
    assert_eq!(keys.len(), 894);
    assert_eq!(groups.len(), 91);
    assert_eq!(split, [3, 2, 2, 2, 2, 3, 4]);
    assert_eq!(total, 102);
    let expected = [("gcd", 385), ("odd", 21), ("planar", 488)];
    let expected: BTreeMap<String, usize> = expected
        .iter()
        .map(|&(kind, count)| (kind.to_string(), count))
        .collect();
    assert_eq!(classes, expected);
}

/// The majority value of `q` over all of `H_1(Σ; F_2)`, computed without
/// symplectic reduction.
fn majority_arf(presentation: &GentlePresentation) -> u8 {
    let graph = presentation.ribbon_graph();
    let cycles = graph.fundamental_cycles();
    let values: Vec<bool> = cycles
        .iter()
        .map(|cycle| (graph.winding(cycle) / 2 + 1) % 2 != 0)
        .collect();
    let pairing = graph.pairing(&cycles);
    let size = cycles.len();
    let mut ones = 0usize;
    for mask in 0u64..1 << size {
        let bit = |i: usize| mask >> i & 1 == 1;
        let mut value = false;
        for i in (0..size).filter(|&i| bit(i)) {
            value ^= values[i];
            for j in (i + 1..size).filter(|&j| bit(j)) {
                value ^= pairing[i][j] % 2 != 0;
            }
        }
        ones += usize::from(value);
    }
    u8::from(2 * ones > 1 << size)
}

#[test]
fn the_arf_invariant_is_the_majority_value_at_five_vertices() {
    // Genus 2 first allows even winding numbers at five vertices. The Arf
    // invariant then splits the AAG group [(2, 8)].
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    for key in connected_gentle_keys(5) {
        let presentation = GentlePresentation::new(&key.algebra(f2()).unwrap()).unwrap();
        let value = presentation.complete_invariant();
        if value.genus() < 2 {
            continue;
        }
        if let WindingClass::Arf(arf) = value.winding_class() {
            assert_eq!(arf, majority_arf(&presentation), "{key:?}");
            assert_eq!(value.aag_function().pairs(), [(2, 8)]);
        }
        *seen.entry(value.winding_class().to_string()).or_default() += 1;
    }
    let expected = [("arf 0", 14), ("arf 1", 9), ("odd", 1213)];
    let expected: BTreeMap<String, usize> = expected
        .iter()
        .map(|&(class, count)| (class.to_string(), count))
        .collect();
    assert_eq!(seen, expected);
}

#[test]
fn winding_classes_print_their_value() {
    let printed: Vec<String> = [
        WindingClass::Planar,
        WindingClass::Gcd(3),
        WindingClass::Odd,
        WindingClass::Even,
        WindingClass::Arf(1),
    ]
    .iter()
    .map(ToString::to_string)
    .collect();
    assert_eq!(printed, ["planar", "gcd 3", "odd", "even", "arf 1"]);
}
