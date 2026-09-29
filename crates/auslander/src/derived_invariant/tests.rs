use std::sync::Arc;

use super::integer::{self, Overflow};
use super::*;
use crate::algebra::{
    Algebra, an_with_relations, commutative_square, dual_numbers, kronecker, linear_an,
};
use crate::completion::CompletionLimits;
use crate::field::PrimeField;
use crate::quiver::{ArrowId, Quiver};
use crate::relation::{Presentation, Relation};

#[path = "tests/discovery.rs"]
mod discovery;

fn field(p: u64) -> PrimeField {
    PrimeField::new(p).unwrap()
}

fn limits(hochschild_degree: usize) -> InvariantLimits {
    InvariantLimits {
        hochschild_degree,
        bar: BarLimits {
            max_tensor_tuples: 10_000,
            max_cochain_dim: 100_000,
            max_matrix_entries: 10_000_000,
            max_work_units: 1_000_000_000,
        },
    }
}

fn invariants(algebra: &Arc<Algebra>, degree: usize) -> DerivedInvariants {
    DerivedInvariants::compute(algebra, limits(degree), &ComputationControl::new()).unwrap()
}

/// The expected finished readings of every kind, in table order.
struct Expected {
    vertices: usize,
    determinant: i128,
    factors: [&'static [i128]; 3],
    pencil: &'static [i128],
    /// The AAG pairs, or `None` when the presentation is not gentle.
    aag: Option<&'static [(usize, usize)]>,
    hochschild: &'static [usize],
}

fn assert_expected(algebra: &Arc<Algebra>, expected: &Expected) {
    use InvariantValue as Value;
    let computed = invariants(algebra, expected.hochschild.len() - 1);
    let values = [
        Value::Count(expected.vertices),
        Value::Integer(expected.determinant),
        Value::Factors(expected.factors[0].to_vec()),
        Value::Factors(expected.factors[1].to_vec()),
        Value::Factors(expected.factors[2].to_vec()),
        Value::Polynomial(expected.pencil.to_vec()),
        Value::Dimensions(expected.hochschild.to_vec()),
        Value::Count(expected.hochschild[0]),
    ];
    let gentle = [
        DerivedInvariantKind::AagFunction,
        DerivedInvariantKind::WindingClass,
    ];
    let kinds = DerivedInvariantKind::ALL
        .into_iter()
        .filter(|kind| !gentle.contains(kind));
    for (kind, value) in kinds.zip(values) {
        assert_eq!(
            computed.reading(kind),
            &InvariantReading::Finished(value),
            "{kind:?}"
        );
    }
    let aag = computed.reading(DerivedInvariantKind::AagFunction);
    match (expected.aag, aag) {
        (Some(pairs), InvariantReading::Finished(Value::AagFunction(function))) => {
            assert_eq!(function.pairs(), pairs);
        }
        (None, InvariantReading::NotApplicable(_)) => {}
        (expected, reading) => panic!("AAG: expected {expected:?}, read {reading:?}"),
    }
    // Every gentle fixture here has genus 0.
    let winding = computed.reading(DerivedInvariantKind::WindingClass);
    match (expected.aag, winding) {
        (Some(_), InvariantReading::Finished(Value::WindingClass(WindingClass::Planar))) => {}
        (None, InvariantReading::NotApplicable(_)) => {}
        (expected, reading) => panic!("winding: expected {expected:?}, read {reading:?}"),
    }
    assert_eq!(computed.hochschild().end(), &HochschildEnd::Complete);
}

#[test]
fn kind_order_matches_the_contract_table() {
    for (index, kind) in DerivedInvariantKind::ALL.into_iter().enumerate() {
        assert_eq!(kind as usize, index);
    }
    assert!(DerivedInvariantKind::ALL.is_sorted());
}

/// `A_1`: `C = [1]`, `C + C^T = [2]`, `C - C^T = [0]`, pencil `x + 1`. The
/// algebra is `k`, so `HH^0 = k` and `HH^i = 0` for `i >= 1`.
#[test]
fn a1_values() {
    let expected = Expected {
        vertices: 1,
        determinant: 1,
        factors: [&[1], &[2], &[0]],
        pencil: &[1, 1],
        aag: Some(&[(2, 0)]),
        hochschild: &[1, 0, 0],
    };
    assert_expected(&linear_an(1, field(5)), &expected);
}

/// `A_2`, arrow `0 → 1`: `C = [[1, 1], [0, 1]]` is unitriangular, so the
/// factors are `[1, 1]`. `C + C^T = [[2, 1], [1, 2]]` has entry gcd `1` and
/// determinant `3`. `C - C^T = [[0, 1], [-1, 0]]` has determinant `1`. The
/// pencil is `(x + 1)^2 - x = x^2 + x + 1`. A path algebra of a tree has
/// `HH^0 = k`, `HH^1 = 0`, and `HH^i = 0` for `i >= 2` (hereditary).
#[test]
fn a2_values() {
    let expected = Expected {
        vertices: 2,
        determinant: 1,
        factors: [&[1, 1], &[1, 3], &[1, 1]],
        pencil: &[1, 1, 1],
        aag: Some(&[(3, 1)]),
        hochschild: &[1, 0, 0],
    };
    assert_expected(&linear_an(2, field(5)), &expected);
}

/// `A_3`, arrows `0 → 1 → 2`: `C` is the upper unitriangular all-ones
/// matrix. `C + C^T = [[2, 1, 1], [1, 2, 1], [1, 1, 2]]` has determinant `4`
/// and a `2 x 2` minor `[[1, 1], [2, 1]] = -1`, so its factors are
/// `[1, 1, 4]`. `C - C^T` is skew of odd size, so singular, and has the
/// minor `[[0, 1], [-1, 0]] = 1`: factors `[1, 1, 0]`. The pencil of `A_n` is
/// `1 + x + ... + x^n`. Hochschild cohomology as for `A_2`.
#[test]
fn a3_values() {
    let expected = Expected {
        vertices: 3,
        determinant: 1,
        factors: [&[1, 1, 1], &[1, 1, 4], &[1, 1, 0]],
        pencil: &[1, 1, 1, 1],
        aag: Some(&[(4, 2)]),
        hochschild: &[1, 0, 0, 0],
    };
    assert_expected(&linear_an(3, field(2)), &expected);
    assert_expected(&linear_an(3, field(5)), &expected);
}

/// `kA_3/(ab)`: `C = [[1, 1, 0], [0, 1, 1], [0, 0, 1]]`. `C + C^T` is the
/// `A_3` Dynkin Cartan matrix, determinant `4`, minor `[[1, 0], [2, 1]] = 1`.
/// `C - C^T` is odd skew with minor `1`. The pencil expands to
/// `(x + 1)((x + 1)^2 - x) - x(x + 1) = (x + 1)(x^2 + 1)`. Every value equals
/// the `A_3` value: the algebra is tilted of type `A_3`.
#[test]
fn a3_with_relation_values() {
    let expected = Expected {
        vertices: 3,
        determinant: 1,
        factors: [&[1, 1, 1], &[1, 1, 4], &[1, 1, 0]],
        pencil: &[1, 1, 1, 1],
        aag: Some(&[(4, 2)]),
        hochschild: &[1, 0, 0, 0],
    };
    let algebra = an_with_relations(3, &[(0, 2)], field(5)).unwrap();
    assert_expected(&algebra, &expected);
    assert_eq!(
        first_difference(
            &invariants(&algebra, 3),
            &invariants(&linear_an(3, field(5)), 3)
        ),
        None
    );
}

/// Kronecker, two arrows `0 → 1`: `C = [[1, 2], [0, 1]]`, factors `[1, 1]`.
/// `C + C^T = [[2, 2], [2, 2]]` has gcd `2` and determinant `0`: `[2, 0]`.
/// `C - C^T = [[0, 2], [-2, 0]]` has gcd `2` and determinant `4`: `[2, 2]`.
/// The pencil is `(x + 1)^2 - 4x = x^2 - 2x + 1`. Happel's formula for a
/// hereditary algebra gives `dim HH^0 - dim HH^1 = n - Σ_α dim e_s(α) A e_t(α)
/// = 2 - 4`, so `HH^1` has dimension `3`.
#[test]
fn kronecker_values() {
    let expected = Expected {
        vertices: 2,
        determinant: 1,
        factors: [&[1, 1], &[2, 0], &[2, 2]],
        pencil: &[1, -2, 1],
        aag: Some(&[(1, 1), (1, 1)]),
        hochschild: &[1, 3, 0],
    };
    assert_expected(&kronecker(2, field(2)), &expected);
    assert_expected(&kronecker(2, field(5)), &expected);
}

/// `k[x]/(x^2)`: `C = [2]`, `C + C^T = [4]`, `C - C^T = [0]`, pencil
/// `2x + 2`. The periodic bimodule resolution has maps `x ⊗ 1 - 1 ⊗ x` and
/// `x ⊗ 1 + 1 ⊗ x`. The Hom complex is `A --0--> A --2x--> A --0--> ...`.
/// Over `F_5`, `HH^0 = A` and `HH^i` has dimension `1` for `i >= 1`. Over
/// `F_2`, `2x = 0` and every `HH^i` has dimension `2`.
#[test]
fn dual_numbers_values() {
    let mut expected = Expected {
        vertices: 1,
        determinant: 2,
        factors: [&[2], &[4], &[0]],
        pencil: &[2, 2],
        aag: Some(&[(0, 1), (1, 0)]),
        hochschild: &[2, 1, 1, 1],
    };
    assert_expected(&dual_numbers(field(5)), &expected);
    expected.hochschild = &[2, 2, 2, 2];
    assert_expected(&dual_numbers(field(2)), &expected);
}

/// The commutative square: `C` is upper unitriangular with rows
/// `[1, 1, 1, 1], [0, 1, 0, 1], [0, 0, 1, 1], [0, 0, 0, 1]`. The pencil `p`
/// is palindromic, `p(0) = det C^T = 1`, `p(1) = det(C + C^T) = 4`, and
/// `p(-1) = det(C^T - C) = 0` because rows `1` and `2` of `C - C^T` agree.
/// Hence `p = 1 + x + x^3 + x^4`, the Coxeter polynomial of `D_4`. The `3 x 3`
/// minors of `C + C^T` are even (for example `4, 2, -2`), so its factors are
/// `[1, 1, 2, 2]`. The algebra is derived equivalent to `D_4`, so
/// `HH^0 = k` and the higher groups vanish.
#[test]
fn commutative_square_values() {
    let expected = Expected {
        vertices: 4,
        determinant: 1,
        factors: [&[1, 1, 1, 1], &[1, 1, 2, 2], &[1, 1, 0, 0]],
        pencil: &[1, 1, 0, 1, 1],
        aag: None,
        hochschild: &[1, 0, 0],
    };
    assert_expected(&commutative_square(field(5)), &expected);
}

/// Builds `quiver` with every vertex `v` renamed `permutation[v]` and the
/// same arrow order, with relation terms given as arrow-id words.
fn relabeled(
    vertices: u32,
    arrows: &[(u32, u32)],
    permutation: &[u32],
    relations: &[&[(i64, &[u32])]],
) -> Arc<Algebra> {
    let field = field(5);
    let renamed: Vec<_> = arrows
        .iter()
        .map(|&(source, target)| (permutation[source as usize], permutation[target as usize]))
        .collect();
    let quiver = Quiver::new(vertices, &renamed).unwrap();
    let relations = relations
        .iter()
        .map(|terms| {
            let terms = terms
                .iter()
                .map(|(coefficient, word)| {
                    (
                        field.elem(*coefficient),
                        word.iter().map(|&a| ArrowId(a)).collect(),
                    )
                })
                .collect();
            Relation::new(&quiver, field, terms).unwrap()
        })
        .collect();
    let presentation = Presentation::new(quiver, field, relations).unwrap();
    Algebra::new(presentation, &CompletionLimits::default()).unwrap()
}

#[test]
fn vertex_relabeling_keeps_every_reading() {
    let square_arrows = [(0, 1), (1, 3), (0, 2), (2, 3)];
    let square_relation: &[(i64, &[u32])] = &[(1, &[0, 1]), (-1, &[2, 3])];
    let path_arrows = [(0, 1), (1, 2)];
    let path_relation: &[(i64, &[u32])] = &[(1, &[0, 1])];
    let cases = [
        (4, &square_arrows[..], &[3, 1, 0, 2][..], square_relation),
        (3, &path_arrows[..], &[2, 0, 1][..], path_relation),
    ];
    for (vertices, arrows, permutation, relation) in cases {
        let identity: Vec<u32> = (0..vertices).collect();
        let original = relabeled(vertices, arrows, &identity, &[relation]);
        let renamed = relabeled(vertices, arrows, permutation, &[relation]);
        assert_ne!(original.cartan_matrix(), renamed.cartan_matrix());
        let (left, right) = (invariants(&original, 2), invariants(&renamed, 2));
        for kind in DerivedInvariantKind::ALL {
            assert_eq!(left.reading(kind), right.reading(kind), "{kind:?}");
        }
    }
}

#[test]
fn integer_helpers_return_typed_overflow() {
    let big = i128::MAX / 2 + 1;
    let square = vec![vec![big, 1], vec![1, big]];
    assert_eq!(integer::determinant(&square), Err(Overflow));
    assert_eq!(integer::pencil(&square), Err(Overflow));
    let skew_overflow = vec![vec![0, i128::MAX], vec![i128::MIN, 0]];
    assert_eq!(integer::invariant_factors(&skew_overflow), Err(Overflow));
    // lcm(2^100, 3^50) exceeds `i128`, though each entry fits.
    let coprime = vec![vec![1 << 100, 0], vec![0, 3i128.pow(50)]];
    assert_eq!(integer::invariant_factors(&coprime), Err(Overflow));
    assert_eq!(integer::determinant(&[vec![i128::MAX]]), Ok(i128::MAX));
}

#[test]
fn integer_helpers_agree_on_small_matrices() {
    let matrix = vec![vec![2, 4, 4], vec![-6, 6, 12], vec![10, -4, -16]];
    // The classical example has Smith form diag(2, 6, 12) and determinant -144.
    assert_eq!(integer::invariant_factors(&matrix), Ok(vec![2, 6, 12]));
    assert_eq!(integer::determinant(&matrix), Ok(-144));
    let pencil = integer::pencil(&matrix).unwrap();
    for point in -3i128..=3 {
        let at: i128 = pencil.iter().rev().fold(0, |sum, &c| sum * point + c);
        let shifted: Vec<Vec<i128>> = (0..3)
            .map(|row| {
                (0..3)
                    .map(|col| point * matrix[row][col] + matrix[col][row])
                    .collect()
            })
            .collect();
        assert_eq!(Ok(at), integer::determinant(&shifted), "x = {point}");
    }
    assert_eq!(
        integer::invariant_factors(&[vec![0, 0], vec![0, 0]]),
        Ok(vec![0, 0])
    );
    assert_eq!(integer::pencil(&[vec![0, 0], vec![0, 0]]), Ok(vec![]));
}

fn stopped_record(kind: DerivedInvariantKind) -> DerivedInvariants {
    let mut record = invariants(&linear_an(2, field(5)), 1);
    record.readings[kind as usize] = InvariantReading::Stopped(InvariantStop::Overflow);
    record
}

#[test]
fn a_stopped_reading_never_separates() {
    let left = stopped_record(DerivedInvariantKind::SymmetricFactors);
    let right = invariants(&kronecker(2, field(5)), 1);
    assert_eq!(
        first_difference(&left, &right),
        Some(DerivedInvariantKind::SkewFactors)
    );
    assert_eq!(
        DerivedInequivalenceWitness::new(&left, &right, DerivedInvariantKind::SymmetricFactors)
            .unwrap_err(),
        WitnessError::NoDifference(DerivedInvariantKind::SymmetricFactors)
    );
}

/// Work budgets measured on `k[x]/(x^2)` over `F_5`: 300 units finish
/// `HH^0` and `HH^1` and cut in `HH^2`, and 0 units finish nothing.
#[test]
fn a_bar_cut_keeps_the_finished_prefix() {
    let algebra = dual_numbers(field(5));
    let full = invariants(&algebra, 3);
    let with_work = |max_work_units| {
        let mut limits = limits(3);
        limits.bar.max_work_units = max_work_units;
        DerivedInvariants::compute(&algebra, limits, &ComputationControl::new()).unwrap()
    };
    let cut = with_work(300);
    assert_eq!(cut.hochschild().dimensions(), &[2, 1]);
    assert!(matches!(
        cut.hochschild().end(),
        HochschildEnd::Stopped(InvariantStop::BarCut(_))
    ));
    assert_eq!(
        cut.reading(DerivedInvariantKind::CenterDimension),
        &InvariantReading::Finished(InvariantValue::Count(2))
    );
    assert_eq!(first_difference(&cut, &full), None);

    let empty = with_work(0);
    for kind in [
        DerivedInvariantKind::HochschildDimensions,
        DerivedInvariantKind::CenterDimension,
    ] {
        assert!(matches!(
            empty.reading(kind),
            InvariantReading::Stopped(InvariantStop::BarCut(_))
        ));
    }
    let control = ComputationControl::new();
    control.cancel();
    let cancelled = DerivedInvariants::compute(&algebra, limits(3), &control).unwrap();
    assert_eq!(
        cancelled.reading(DerivedInvariantKind::CenterDimension),
        &InvariantReading::Stopped(InvariantStop::Cancelled)
    );
    assert_eq!(first_difference(&cancelled, &full), None);
    assert_eq!(
        first_difference(&empty, &invariants(&dual_numbers(field(5)), 1)),
        None
    );
}

#[test]
fn witness_recomputes_and_rejects_tampering() {
    let kronecker = invariants(&kronecker(2, field(5)), 2);
    let a2 = invariants(&linear_an(2, field(5)), 2);
    let kind = first_difference(&kronecker, &a2).unwrap();
    assert_eq!(kind, DerivedInvariantKind::SymmetricFactors);
    let witness = DerivedInequivalenceWitness::new(&kronecker, &a2, kind).unwrap();
    assert!(witness.verify());

    let mut tampered = witness.clone();
    tampered.left_value = InvariantValue::Factors(vec![2, 1]);
    assert!(!tampered.verify());
    let mut tampered = witness.clone();
    tampered.right_value = tampered.left_value.clone();
    assert!(!tampered.verify());
    let mut tampered = witness.clone();
    tampered.kind = DerivedInvariantKind::CartanDeterminant;
    assert!(!tampered.verify());
    let mut tampered = witness.clone();
    tampered.right = kronecker.algebra().clone();
    assert!(!tampered.verify());

    let hochschild = DerivedInequivalenceWitness::new(
        &kronecker,
        &a2,
        DerivedInvariantKind::HochschildDimensions,
    )
    .unwrap();
    assert!(hochschild.verify());
    let mut tampered = hochschild.clone();
    tampered.left_value = InvariantValue::Dimensions(vec![1, 4, 0]);
    assert!(!tampered.verify());
}

#[test]
fn witness_rejects_mixed_fields_and_limits() {
    let over_2 = invariants(&dual_numbers(field(2)), 2);
    let over_5 = invariants(&dual_numbers(field(5)), 2);
    assert_eq!(
        first_difference(&over_2, &over_5),
        Some(DerivedInvariantKind::HochschildDimensions)
    );
    assert_eq!(
        DerivedInequivalenceWitness::new(
            &over_2,
            &over_5,
            DerivedInvariantKind::HochschildDimensions
        )
        .unwrap_err(),
        WitnessError::FieldMismatch { left: 2, right: 5 }
    );
    let a2 = invariants(&linear_an(2, field(5)), 1);
    assert_eq!(
        DerivedInequivalenceWitness::new(&over_5, &a2, DerivedInvariantKind::VertexCount)
            .unwrap_err(),
        WitnessError::LimitsMismatch
    );
    let mut tampered = DerivedInequivalenceWitness::new(
        &over_5,
        &invariants(&linear_an(2, field(5)), 2),
        DerivedInvariantKind::VertexCount,
    )
    .unwrap();
    assert!(tampered.verify());
    tampered.left = dual_numbers(field(2));
    assert!(!tampered.verify());
}

/// `A_3` and the 3-cycle `a: 0 → 1`, `b: 1 → 2`, `c: 2 → 0` with `a·b = 0`
/// agree on every Cartan kind, the kinds before the AAG function.
/// Their AAG functions differ: `A_3` has `[(4, 2)]`, and the cycle has two
/// boundary pairs.
#[test]
fn aag_witness_separates_equal_cartan_data() {
    let cycle = relabeled(3, &[(0, 1), (1, 2), (2, 0)], &[0, 1, 2], &[&[(1, &[0, 1])]]);
    let (a3, cycle) = (
        invariants(&linear_an(3, field(5)), 2),
        invariants(&cycle, 2),
    );
    let kind = DerivedInvariantKind::AagFunction;
    assert_eq!(first_difference(&a3, &cycle), Some(kind));
    let aag = |record: &DerivedInvariants| match record.reading(kind) {
        InvariantReading::Finished(InvariantValue::AagFunction(function)) => function.to_string(),
        reading => panic!("{reading:?}"),
    };
    assert_eq!(
        (aag(&a3), aag(&cycle)),
        ("[(4, 2)]".into(), "[(1, 0), (2, 3)]".into())
    );
    let witness = DerivedInequivalenceWitness::new(&a3, &cycle, kind).unwrap();
    assert!(witness.verify());

    let mut tampered = witness.clone();
    tampered.right_value = tampered.left_value.clone();
    assert!(!tampered.verify());
    let mut tampered = witness.clone();
    tampered.right = commutative_square(field(5));
    assert!(!tampered.verify());
    let mut tampered = witness.clone();
    tampered.kind = DerivedInvariantKind::HochschildDimensions;
    assert!(!tampered.verify());
}

/// A reading that is not applicable never separates, even from a finished
/// value, and gives no witness.
#[test]
fn not_applicable_never_separates() {
    let square = invariants(&commutative_square(field(5)), 2);
    let a4 = invariants(&linear_an(4, field(5)), 2);
    let kind = DerivedInvariantKind::AagFunction;
    assert!(matches!(
        square.reading(kind),
        InvariantReading::NotApplicable(crate::gentle::GentleError::NonMonomial { .. })
    ));
    assert!(!square.reading(kind).separates(a4.reading(kind)));
    assert_eq!(
        DerivedInequivalenceWitness::new(&square, &a4, kind).unwrap_err(),
        WitnessError::NoDifference(kind)
    );
}

/// One kind computed alone equals its reading in the full record. Under
/// cancellation, the kinds before the bar computation still finish and the
/// two Hochschild kinds stop.
#[test]
fn a_single_kind_reads_like_the_full_record() {
    let algebra = kronecker(2, field(3));
    let full = invariants(&algebra, 2);
    let cancelled = ComputationControl::new();
    cancelled.cancel();
    for kind in DerivedInvariantKind::ALL {
        let alone = derived_invariant(&algebra, kind, limits(2), &ComputationControl::new());
        assert_eq!(&alone.unwrap(), full.reading(kind), "{kind:?}");
        let stopped = derived_invariant(&algebra, kind, limits(2), &cancelled).unwrap();
        if kind < DerivedInvariantKind::HochschildDimensions {
            assert_eq!(&stopped, full.reading(kind), "{kind:?}");
        } else {
            assert_eq!(stopped, InvariantReading::Stopped(InvariantStop::Cancelled));
        }
    }
}
