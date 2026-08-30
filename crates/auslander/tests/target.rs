//! Public acceptance and determinism gates for split tilting targets.

use std::env;
use std::sync::Arc;
use std::time::Duration;

use auslander::algebra::{Algebra, an_with_relations, dual_numbers, linear_an};
use auslander::field::PrimeField;
use auslander::module::{Module, direct_sum};
use auslander::target::{
    TargetBudgetCut, TargetCutReason, TargetCutStage, TargetLimits, TargetWork,
    VerifiedTargetPresentation, present_target,
};
use auslander::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};

mod common;

use common::{f2, f5};

const CHILD_ENV: &str = "AUSLANDER_TARGET_DETERMINISM_CHILD";
const MARKER: &str = "target-fingerprint:";
const CHILD_TIMEOUT: Duration = Duration::from_secs(60);

fn fields() -> [PrimeField; 2] {
    [f2(), f5()]
}

fn regular(algebra: &Arc<Algebra>) -> Module {
    let summands: Vec<Module> = (0..algebra.quiver().num_vertices())
        .map(|vertex| Module::projective(algebra, vertex))
        .collect();
    match summands.as_slice() {
        [only] => only.clone(),
        _ => direct_sum(&summands.iter().collect::<Vec<_>>()).0,
    }
}

fn classify(module: &Module) -> ClassicalTiltingModule {
    let limits = TiltingLimits {
        max_projective_dimension: 4,
        max_generation_steps: 8,
    };
    let ClassicalTiltingResult::Tilting(tilting) =
        ClassicalTiltingModule::classify(module, limits).unwrap()
    else {
        panic!("the acceptance fixture is classical tilting")
    };
    assert!(tilting.verify());
    tilting
}

fn presented(module: &Module) -> VerifiedTargetPresentation {
    let tilting = classify(module);
    let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
    assert!(outcome.verify());
    outcome
        .presented()
        .expect("the acceptance fixture has a split target")
        .clone()
}

fn pd2_dual(field: PrimeField) -> Module {
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let injectives: Vec<Module> = (0..3)
        .map(|vertex| Module::injective(&algebra, vertex))
        .collect();
    direct_sum(&injectives.iter().collect::<Vec<_>>()).0
}

fn pd1_tilting(field: PrimeField) -> Module {
    let algebra = linear_an(2, field);
    direct_sum(&[
        &Module::projective(&algebra, 0),
        &Module::simple(&algebra, 0),
    ])
    .0
}

#[test]
fn projective_generators_recover_verified_opposite_targets_over_f2_and_f5() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let target = presented(&regular(&algebra));
        assert_eq!(target.target().dim(), algebra.dim());
        assert_eq!(target.target().quiver().arrows(), &[(1, 0), (2, 1)]);
        assert_eq!(target.work().endo_dimension, algebra.dim());

        let coordinates: Vec<_> = (0..target.target().dim())
            .map(|index| field.elem(index as i64))
            .collect();
        let image = target.map_coordinates(&coordinates);
        assert_eq!(target.preimage_coordinates(&image), coordinates);
    }
}

#[test]
fn projective_dimension_one_targets_use_the_opposite_orientation_over_both_fields() {
    for field in fields() {
        let module = pd1_tilting(field);
        let tilting = classify(&module);
        assert_eq!(tilting.projective_dimension(), 1);
        let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
        let target = outcome.presented().expect("the pd1 target is split");
        assert_eq!(target.target().quiver().arrows(), &[(1, 0)]);
        assert!(outcome.verify());
    }
}

#[test]
fn projective_dimension_two_targets_verify_over_f2_and_f5() {
    for field in fields() {
        let module = pd2_dual(field);
        let tilting = classify(&module);
        assert_eq!(tilting.projective_dimension(), 2);
        let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
        assert!(outcome.presented().is_some());
        assert!(outcome.verify());
    }
}

#[test]
fn relation_bearing_targets_keep_the_quadratic_loop_over_both_fields() {
    for field in fields() {
        let algebra = dual_numbers(field);
        let target = presented(&regular(&algebra));
        assert_eq!(target.target().quiver().arrows(), &[(0, 0)]);
        assert!(
            target
                .completion_certificate()
                .input_relations
                .iter()
                .any(|relation| relation.iter().any(|(_, word)| word.len() == 2))
        );
        assert_eq!(target.work().paths, 1);
        assert_eq!(target.work().relation_terms, 1);
    }
}

#[test]
fn recorded_target_work_counts_do_not_grow() {
    // These ceilings are copied from the target benchmark record. They count
    // deterministic work, so machine speed cannot change them.
    for field in fields() {
        let generator = linear_an(3, field);
        assert_eq!(
            presented(&regular(&generator)).work(),
            TargetWork {
                endo_dimension: 6,
                radical_products: 84,
                paths: 1,
                relation_terms: 0,
            }
        );

        let dual = dual_numbers(field);
        assert_eq!(
            presented(&regular(&dual)).work(),
            TargetWork {
                endo_dimension: 2,
                radical_products: 3,
                paths: 1,
                relation_terms: 1,
            }
        );

        assert_eq!(
            presented(&pd2_dual(field)).work(),
            TargetWork {
                endo_dimension: 5,
                radical_products: 40,
                paths: 1,
                relation_terms: 1,
            }
        );
    }
}

fn assert_budget_cut(
    tilting: &ClassicalTiltingModule,
    limits: &TargetLimits,
    stage: impl FnOnce(TargetCutStage) -> bool,
) {
    let outcome = present_target(tilting, limits).unwrap();
    let cut = outcome.cut().expect("the target budget must stop recovery");
    let TargetCutReason::Budget(TargetBudgetCut { stage: actual, .. }) = cut.reason() else {
        panic!("the target must stop at a local budget")
    };
    assert!(stage(*actual));
    assert_eq!(cut.limits(), limits);
    assert!(outcome.verify());
}

#[test]
fn every_target_cut_replays_over_f2_and_f5() {
    for field in fields() {
        let algebra = dual_numbers(field);
        let tilting = classify(&regular(&algebra));

        assert_budget_cut(
            &tilting,
            &TargetLimits {
                max_endo_dimension: 1,
                ..TargetLimits::default()
            },
            |stage| stage == TargetCutStage::EndoDimension,
        );
        assert_budget_cut(
            &tilting,
            &TargetLimits {
                max_radical_products: 0,
                ..TargetLimits::default()
            },
            |stage| matches!(stage, TargetCutStage::RadicalPower { .. }),
        );
        assert_budget_cut(
            &tilting,
            &TargetLimits {
                max_paths: 0,
                ..TargetLimits::default()
            },
            |stage| matches!(stage, TargetCutStage::Paths { length: 2 }),
        );
        assert_budget_cut(
            &tilting,
            &TargetLimits {
                max_relation_terms: 0,
                ..TargetLimits::default()
            },
            |stage| matches!(stage, TargetCutStage::Relations { .. }),
        );

        let mut limits = TargetLimits::default();
        limits.completion.max_steps = 0;
        let outcome = present_target(&tilting, &limits).unwrap();
        assert!(matches!(
            outcome.cut().expect("completion must stop").reason(),
            TargetCutReason::Completion(_)
        ));
        assert!(outcome.verify());
    }
}

fn render_presented(name: &str, value: &VerifiedTargetPresentation, out: &mut String) {
    out.push_str(name);
    out.push('\n');
    out.push_str(&format!("quiver={:?}\n", value.target().quiver().arrows()));
    out.push_str("certificate=");
    out.push_str(&value.completion_certificate().to_canonical_json());
    out.push('\n');
    out.push_str(&format!(
        "idempotents={:?}\narrows={:?}\nnormal={:?}\ninverse={:?}\nwork={:?}\n",
        value.idempotent_images().entries_u64(),
        value.arrow_images().entries_u64(),
        value.normal_word_images().entries_u64(),
        value.normal_word_preimages().entries_u64(),
        value.work(),
    ));
}

fn determinism_payload() -> String {
    let mut out = String::new();
    for field in fields() {
        let modulus = field.modulus();
        let generator = linear_an(3, field);
        render_presented(
            &format!("generator-f{modulus}"),
            &presented(&regular(&generator)),
            &mut out,
        );
        render_presented(
            &format!("pd1-f{modulus}"),
            &presented(&pd1_tilting(field)),
            &mut out,
        );
        render_presented(
            &format!("pd2-f{modulus}"),
            &presented(&pd2_dual(field)),
            &mut out,
        );
        let dual = dual_numbers(field);
        render_presented(
            &format!("relation-f{modulus}"),
            &presented(&regular(&dual)),
            &mut out,
        );

        let tilting = classify(&regular(&dual));
        for (name, limits) in [
            (
                "endo",
                TargetLimits {
                    max_endo_dimension: 1,
                    ..TargetLimits::default()
                },
            ),
            (
                "radical",
                TargetLimits {
                    max_radical_products: 0,
                    ..TargetLimits::default()
                },
            ),
            (
                "paths",
                TargetLimits {
                    max_paths: 0,
                    ..TargetLimits::default()
                },
            ),
            (
                "relations",
                TargetLimits {
                    max_relation_terms: 0,
                    ..TargetLimits::default()
                },
            ),
        ] {
            let outcome = present_target(&tilting, &limits).unwrap();
            out.push_str(&format!(
                "cut-{name}-f{modulus}={:?}\n",
                outcome.cut().expect("the local limit must cut").reason()
            ));
        }
        let mut limits = TargetLimits::default();
        limits.completion.max_steps = 0;
        let outcome = present_target(&tilting, &limits).unwrap();
        out.push_str(&format!(
            "cut-completion-f{modulus}={:?}\n",
            outcome.cut().expect("completion must cut").reason()
        ));
    }
    out
}

#[test]
fn target_data_is_deterministic_in_one_process() {
    assert_eq!(determinism_payload(), determinism_payload());
}

#[test]
fn target_determinism_child_prints_fingerprint() {
    if env::var(CHILD_ENV).is_err() {
        return;
    }
    println!("{}", common::fingerprint(MARKER, &determinism_payload()));
}

fn child_fingerprint() -> String {
    let stdout = common::child_test_stdout(
        "target_determinism_child_prints_fingerprint",
        CHILD_ENV,
        CHILD_TIMEOUT,
    );
    common::marked_line(&stdout, MARKER)
}

#[test]
fn target_data_is_deterministic_across_fresh_processes() {
    let first = child_fingerprint();
    let second = child_fingerprint();
    assert_eq!(first, second, "fresh processes disagree on target data");
    assert_eq!(
        first,
        common::fingerprint(MARKER, &determinism_payload()),
        "child processes disagree with this process"
    );
}
