use std::env;
use std::process::Command;
use std::sync::Arc;

use super::bar::{Ledger, Stop, input_rank};
use super::cochain::{as_usize, checked_add, checked_product, next_usize};
use super::verification::{same_complete, same_cut};
use super::*;
use crate::algebra::{
    Algebra, commutative_square, dual_numbers, linear_an, path_algebra, truncated_poly,
};
use crate::field::PrimeField;
use crate::linalg::DenseMat;
use crate::quiver::Quiver;

#[path = "tests/full_bar.rs"]
mod full_bar;

use full_bar::{
    center_dimension, full_bar_dimensions, inhomogeneous_dual_numbers, outer_derivation_dimension,
};

fn field(p: u64) -> PrimeField {
    PrimeField::new(p).unwrap()
}

fn generous() -> BarLimits {
    BarLimits {
        max_tensor_tuples: 10_000,
        max_cochain_dim: 100_000,
        max_matrix_entries: 10_000_000,
        max_work_units: 1_000_000_000,
    }
}

fn complete(outcome: HochschildOutcome) -> HochschildCohomology {
    match outcome {
        HochschildOutcome::Complete(value) => value,
        HochschildOutcome::Cut(cut) => panic!("unexpected cut: {:?}", cut.diagnostics()),
    }
}

fn bar_record() -> String {
    let exact = complete(bar_hochschild(&commutative_square(field(5)), 2, generous()).unwrap());
    let degrees: Vec<_> = exact
        .degrees()
        .iter()
        .map(|degree| {
            (
                degree.dim(),
                degree.cochain_basis(),
                degree.differential().entries_u64(),
                degree.cocycle_basis().entries_u64(),
                degree.coboundary_basis().entries_u64(),
                degree.complement_basis().entries_u64(),
            )
        })
        .collect();
    let limits = BarLimits {
        max_work_units: 0,
        ..generous()
    };
    let HochschildOutcome::Cut(cut) = bar_hochschild(&dual_numbers(field(5)), 0, limits).unwrap()
    else {
        panic!("zero work must cut")
    };
    format!("{degrees:?}|{:?}", cut.diagnostics())
}

#[test]
fn semisimple_algebra_has_only_degree_zero_cohomology() {
    let quiver = Quiver::new(2, &[]).unwrap();
    let algebra = path_algebra(quiver, field(5)).unwrap();
    let result = complete(bar_hochschild(&algebra, 2, generous()).unwrap());
    assert_eq!(
        result
            .degrees()
            .iter()
            .map(HochschildDegree::dim)
            .collect::<Vec<_>>(),
        [2, 0, 0]
    );
    assert!(result.verify());
}

#[test]
fn dual_numbers_pin_the_characteristic_two_sign() {
    let f5 = complete(bar_hochschild(&dual_numbers(field(5)), 3, generous()).unwrap());
    let f2 = complete(bar_hochschild(&dual_numbers(field(2)), 3, generous()).unwrap());
    assert_eq!(
        f5.degrees()
            .iter()
            .map(HochschildDegree::dim)
            .collect::<Vec<_>>(),
        [2, 1, 1, 1]
    );
    assert_eq!(
        f2.degrees()
            .iter()
            .map(HochschildDegree::dim)
            .collect::<Vec<_>>(),
        [2, 2, 2, 2]
    );
}

#[test]
fn a_work_cut_keeps_an_exact_prefix() {
    let algebra = dual_numbers(field(5));
    let degree_zero = complete(bar_hochschild(&algebra, 0, generous()).unwrap());
    let mut limits = generous();
    limits.max_work_units = degree_zero.diagnostics().work_units;
    let HochschildOutcome::Cut(cut) = bar_hochschild(&algebra, 1, limits).unwrap() else {
        panic!("degree one must exceed the degree-zero work ceiling")
    };
    assert_eq!(cut.completed_degrees().len(), 1);
    assert_eq!(cut.diagnostics().stage, BarStage::DegreeRecord);
    assert_eq!(
        cut.completed_degrees()[0].dim(),
        degree_zero.degrees()[0].dim()
    );
    assert!(cut.verify());
}

#[test]
fn classes_evaluate_on_vertex_and_tuple_inputs() {
    let algebra = dual_numbers(field(5));
    let result = complete(bar_hochschild(&algebra, 1, generous()).unwrap());
    let one = algebra.field().one();
    let h0 = result
        .degree(0)
        .unwrap()
        .class_from_coordinates(vec![one, algebra.field().zero()])
        .unwrap();
    assert_eq!(h0.evaluate(&BarInput::Vertex(0)).unwrap().len(), 1);
    let h1 = result
        .degree(1)
        .unwrap()
        .class_from_coordinates(vec![one])
        .unwrap();
    assert_eq!(h1.evaluate(&BarInput::Tuple(vec![1])).unwrap().len(), 1);
    assert!(matches!(
        h1.evaluate(&BarInput::Tuple(vec![0])),
        Err(HochschildError::TrivialInput { .. })
    ));
    assert!(matches!(
        h1.evaluate(&BarInput::Tuple(vec![1, 1])),
        Err(HochschildError::WrongInputDegree { .. })
    ));
    assert!(matches!(
        h1.evaluate(&BarInput::Tuple(vec![2])),
        Err(HochschildError::BasisOutOfRange { .. })
    ));
    assert!(matches!(
        h0.evaluate(&BarInput::Vertex(1)),
        Err(HochschildError::VertexOutOfRange { .. })
    ));
    let a2 = complete(bar_hochschild(&linear_an(2, field(5)), 2, generous()).unwrap());
    assert!(matches!(
        a2.degree(2)
            .unwrap()
            .zero_class()
            .evaluate(&BarInput::Tuple(vec![2, 2])),
        Err(HochschildError::NonComposableInput { .. })
    ));
}

#[test]
fn nonmonomial_differentials_square_to_zero() {
    let result = complete(bar_hochschild(&commutative_square(field(5)), 2, generous()).unwrap());
    assert!(result.verify());
}

#[test]
fn normalized_bar_agrees_with_full_bar_and_low_degree_checks() {
    let fixtures: Vec<(&str, Arc<Algebra>, usize)> = vec![
        (
            "F5 squared",
            path_algebra(Quiver::new(2, &[]).unwrap(), field(5)).unwrap(),
            2,
        ),
        ("A2", linear_an(2, field(5)), 2),
        ("dual numbers", dual_numbers(field(5)), 3),
        ("x cubed", truncated_poly(3, field(5)).unwrap(), 2),
        ("commutative square", commutative_square(field(5)), 1),
        ("inhomogeneous", inhomogeneous_dual_numbers(field(5)), 2),
    ];
    for (name, algebra, max_degree) in fixtures {
        let normalized = complete(bar_hochschild(&algebra, max_degree, generous()).unwrap());
        let dimensions: Vec<_> = normalized
            .degrees()
            .iter()
            .map(HochschildDegree::dim)
            .collect();
        assert_eq!(
            dimensions,
            full_bar_dimensions(&algebra, max_degree),
            "{name}"
        );
        assert_eq!(dimensions[0], center_dimension(&algebra), "{name}: center");
        if max_degree > 0 {
            assert_eq!(
                dimensions[1],
                outer_derivation_dimension(&algebra),
                "{name}: derivations"
            );
        }
    }
}

#[test]
fn hand_derived_fixtures_pin_dimensions() {
    for vertices in [1, 2, 3] {
        let algebra = path_algebra(Quiver::new(vertices, &[]).unwrap(), field(5)).unwrap();
        let result = complete(bar_hochschild(&algebra, 2, generous()).unwrap());
        assert_eq!(
            result
                .degrees()
                .iter()
                .map(HochschildDegree::dim)
                .collect::<Vec<_>>(),
            [vertices as usize, 0, 0]
        );
    }
    for vertices in [1, 2, 3] {
        let result =
            complete(bar_hochschild(&linear_an(vertices, field(5)), 2, generous()).unwrap());
        assert_eq!(
            result
                .degrees()
                .iter()
                .map(HochschildDegree::dim)
                .collect::<Vec<_>>(),
            [1, 0, 0]
        );
    }
    let x_cubed =
        complete(bar_hochschild(&truncated_poly(3, field(5)).unwrap(), 2, generous()).unwrap());
    assert_eq!(
        x_cubed
            .degrees()
            .iter()
            .map(HochschildDegree::dim)
            .collect::<Vec<_>>(),
        [3, 2, 2]
    );
}

#[test]
fn every_limit_cuts_before_its_first_unaffordable_operation() {
    let algebra = dual_numbers(field(5));
    let tensor = BarLimits {
        max_tensor_tuples: 0,
        ..generous()
    };
    let cochains = BarLimits {
        max_cochain_dim: 0,
        ..generous()
    };
    let matrix = BarLimits {
        max_matrix_entries: 0,
        ..generous()
    };
    let work = BarLimits {
        max_work_units: 0,
        ..generous()
    };
    for (limits, limit, stage) in [
        (tensor, BarLimit::TensorTuples, BarStage::Shape),
        (cochains, BarLimit::CochainDimension, BarStage::Shape),
        (matrix, BarLimit::MatrixEntries, BarStage::Differential),
        (work, BarLimit::WorkUnits, BarStage::DegreeRecord),
    ] {
        let HochschildOutcome::Cut(cut) = bar_hochschild(&algebra, 0, limits).unwrap() else {
            panic!("a zero ceiling must cut")
        };
        let diagnostics = cut.diagnostics();
        assert_eq!(diagnostics.reason, BarCutReason::Limit(limit));
        assert_eq!(diagnostics.stage, stage);
        assert_eq!(diagnostics.completed_degree_count, 0);
        assert_eq!(diagnostics.first_uncomputed_differential, 0);
        assert_eq!(diagnostics.ceiling, Some(0));
        assert!(diagnostics.proposed > diagnostics.used);
        assert!(cut.verify());
    }
}

#[test]
fn matrix_limit_counts_left_kernel_scratch_for_zero_columns() {
    let algebra = path_algebra(Quiver::new(2, &[]).unwrap(), field(5)).unwrap();
    let limits = BarLimits {
        max_matrix_entries: 3,
        ..generous()
    };
    let HochschildOutcome::Cut(cut) = bar_hochschild(&algebra, 0, limits).unwrap() else {
        panic!("the kernel scratch must exceed the ceiling")
    };
    assert_eq!(
        cut.diagnostics().reason,
        BarCutReason::Limit(BarLimit::MatrixEntries)
    );
    assert_eq!(cut.diagnostics().stage, BarStage::Cocycles);
    assert_eq!(cut.diagnostics().used, 0);
    assert_eq!(cut.diagnostics().proposed, 4);
    assert!(cut.verify());
}

#[test]
fn checked_size_arithmetic_cuts_without_wrapping() {
    let ledger = Ledger {
        limits: generous(),
        requested_degree: 0,
        completed_degree_count: 0,
        work_units: 0,
        matrix_entries: 0,
        degrees: Vec::new(),
    };
    for Stop(diagnostics) in [
        checked_product(&ledger, 0, BarStage::Shape, &[u128::MAX, 2])
            .expect_err("product overflow must cut"),
        checked_add(&ledger, 0, BarStage::Shape, u128::MAX, 1).expect_err("sum overflow must cut"),
        as_usize(&ledger, 0, BarStage::Shape, u128::MAX).expect_err("usize overflow must cut"),
        next_usize(&ledger, 0, BarStage::Shape, usize::MAX)
            .expect_err("increment overflow must cut"),
    ] {
        assert_eq!(diagnostics.reason, BarCutReason::SizeOverflow);
        assert_eq!(diagnostics.stage, BarStage::Shape);
        assert!(diagnostics.ceiling.is_none());
    }
}

#[test]
fn fresh_equal_algebras_compare_structurally() {
    let left = dual_numbers(field(5));
    let right = dual_numbers(field(5));
    assert!(!Arc::ptr_eq(&left, &right));
    let left = complete(bar_hochschild(&left, 2, generous()).unwrap());
    let right = complete(bar_hochschild(&right, 2, generous()).unwrap());
    assert!(same_complete(&left, &right));
    assert!(left.verify());
    assert!(right.verify());

    let limits = BarLimits {
        max_work_units: 0,
        ..generous()
    };
    let HochschildOutcome::Cut(left) = bar_hochschild(&dual_numbers(field(5)), 0, limits).unwrap()
    else {
        panic!("zero work must cut")
    };
    let HochschildOutcome::Cut(right) = bar_hochschild(&dual_numbers(field(5)), 0, limits).unwrap()
    else {
        panic!("zero work must cut")
    };
    assert!(same_cut(&left, &right));
}

#[test]
fn verification_rejects_mutated_bar_records() {
    let algebra = dual_numbers(field(5));
    let result = complete(bar_hochschild(&algebra, 1, generous()).unwrap());

    let mut differential = result.clone();
    let inner = Arc::make_mut(&mut differential.degrees[0].0);
    inner.differential.set(0, 0, algebra.field().one());
    assert!(!differential.verify());

    let mut basis = result.clone();
    Arc::make_mut(&mut basis.degrees[0].0).layout.coordinates[0].output = 1;
    assert!(!basis.verify());

    let mut tuple_rank = result.clone();
    Arc::make_mut(&mut tuple_rank.degrees[1].0)
        .layout
        .coordinates[0]
        .tuple_rank = 1;
    assert!(!tuple_rank.verify());

    let mut offsets = result.clone();
    Arc::make_mut(&mut offsets.degrees[1].0).layout.offsets[1] -= 1;
    assert!(!offsets.verify());

    let mut cocycles = result.clone();
    Arc::make_mut(&mut cocycles.degrees[0].0)
        .cocycles
        .set(0, 0, algebra.field().zero());
    assert!(!cocycles.verify());

    let mut dimension = result.clone();
    let inner = Arc::make_mut(&mut dimension.degrees[0].0);
    inner.complement = DenseMat::zero(inner.complement.rows() - 1, inner.complement.cols());
    assert!(!dimension.verify());

    let mut requested_degree = result.clone();
    requested_degree.requested_degree += 1;
    assert!(!requested_degree.verify());

    let mut limits = result.clone();
    limits.limits.max_tensor_tuples += 1;
    assert!(!limits.verify());

    let mut degree_index = result.clone();
    Arc::make_mut(&mut degree_index.degrees[0].0).degree += 1;
    assert!(!degree_index.verify());

    let mut diagnostics = result;
    diagnostics.diagnostics.work_units += 1;
    assert!(!diagnostics.verify());

    let algebra = linear_an(2, field(5));
    let result = complete(bar_hochschild(&algebra, 1, generous()).unwrap());

    let mut coboundaries = result.clone();
    let coboundary = &mut Arc::make_mut(&mut coboundaries.degrees[1].0).coboundaries;
    let (row, column) = (0..coboundary.rows())
        .flat_map(|row| (0..coboundary.cols()).map(move |column| (row, column)))
        .find(|&(row, column)| !coboundary.get(row, column).is_zero())
        .expect("A2 has a nonzero degree-one coboundary");
    coboundary.set(row, column, algebra.field().zero());
    assert!(!coboundaries.verify());

    let mut sign = result.clone();
    let differential = &mut Arc::make_mut(&mut sign.degrees[0].0).differential;
    let (row, column) = (0..differential.rows())
        .flat_map(|row| (0..differential.cols()).map(move |column| (row, column)))
        .find(|&(row, column)| !differential.get(row, column).is_zero())
        .expect("A2 has a nonzero degree-zero differential");
    let value = differential.get(row, column);
    differential.set(row, column, algebra.field().neg(value));
    assert!(!sign.verify());

    let algebra = truncated_poly(3, field(5)).unwrap();
    let result = complete(bar_hochschild(&algebra, 1, generous()).unwrap());
    let product_entry = result.degree(1).unwrap().differential().get(5, 2);
    assert_eq!(product_entry, algebra.field().neg(algebra.field().one()));
    let mut product = result;
    Arc::make_mut(&mut product.degrees[1].0)
        .differential
        .set(5, 2, algebra.field().zero());
    assert!(!product.verify());
}

#[test]
fn tuple_ranks_follow_normal_basis_lexicographic_order() {
    let algebra = truncated_poly(3, field(5)).unwrap();
    assert_eq!(input_rank(&algebra, 2, &BarInput::Tuple(vec![1, 1])), Ok(0));
    assert_eq!(input_rank(&algebra, 2, &BarInput::Tuple(vec![1, 2])), Ok(1));
    assert_eq!(input_rank(&algebra, 2, &BarInput::Tuple(vec![2, 1])), Ok(2));
    assert_eq!(input_rank(&algebra, 2, &BarInput::Tuple(vec![2, 2])), Ok(3));
    let result = complete(bar_hochschild(&algebra, 2, generous()).unwrap());
    let degree = result.degree(2).unwrap();
    assert_eq!(degree.algebra().basis(), algebra.basis());
    assert_eq!(degree.input_for_rank(0), Some(BarInput::Tuple(vec![1, 1])));
    assert_eq!(degree.input_for_rank(1), Some(BarInput::Tuple(vec![1, 2])));
    assert_eq!(degree.input_for_rank(2), Some(BarInput::Tuple(vec![2, 1])));
    assert_eq!(degree.input_for_rank(3), Some(BarInput::Tuple(vec![2, 2])));
    assert_eq!(degree.input_for_rank(4), None);
    assert_eq!(degree.input_for_rank(usize::MAX), None);

    let algebra = linear_an(3, field(5));
    let result = complete(bar_hochschild(&algebra, 2, generous()).unwrap());
    let degree = result.degree(2).unwrap();
    assert_eq!(degree.input_for_rank(0), Some(BarInput::Tuple(vec![3, 4])));
    assert_eq!(degree.input_for_rank(1), None);
}

const BAR_CHILD_ENV: &str = "AUSLANDER_HOCHSCHILD_CHILD";
const BAR_MARKER: &str = "hochschild-record:";

#[test]
fn fresh_process_child_prints_bar_record() {
    if env::var(BAR_CHILD_ENV).is_ok() {
        println!("{BAR_MARKER}{}", bar_record());
    }
}

fn fresh_bar_record() -> String {
    let output = Command::new(env::current_exe().expect("path of this test binary"))
        .args([
            "--exact",
            "hochschild::tests::fresh_process_child_prints_bar_record",
            "--nocapture",
        ])
        .env(BAR_CHILD_ENV, "1")
        .output()
        .expect("spawn a fresh test process");
    assert!(output.status.success(), "fresh test process failed");
    String::from_utf8(output.stdout)
        .expect("test output is UTF-8")
        .lines()
        .find_map(|line| line.find(BAR_MARKER).map(|index| line[index..].to_owned()))
        .expect("fresh test process printed the bar record")
}

#[test]
fn fresh_processes_reproduce_bar_bases_and_cut_diagnostics() {
    let first = fresh_bar_record();
    let second = fresh_bar_record();
    assert_eq!(first, second);
    assert_eq!(first, format!("{BAR_MARKER}{}", bar_record()));
}

#[test]
fn verification_rejects_a_mutated_cut_record() {
    let limits = BarLimits {
        max_work_units: 0,
        ..generous()
    };
    let HochschildOutcome::Cut(mut cut) =
        bar_hochschild(&dual_numbers(field(5)), 0, limits).unwrap()
    else {
        panic!("zero work must cut")
    };
    assert!(cut.verify());
    cut.diagnostics.proposed += 1;
    assert!(!cut.verify());
}
