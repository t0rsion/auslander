use super::*;

#[test]
fn each_local_target_budget_has_a_typed_cut() {
    let algebra = dual_numbers(f5());
    let tilting = tilting(&regular(&algebra));

    let limits = TargetLimits {
        max_endo_dimension: 1,
        ..TargetLimits::default()
    };
    let outcome = present_target(&tilting, &limits).unwrap();
    let cut = outcome
        .cut()
        .expect("the endomorphism dimension exceeds one");
    assert!(matches!(
        cut.reason(),
        TargetCutReason::Budget(TargetBudgetCut {
            stage: TargetCutStage::EndoDimension,
            requested: 2,
            ..
        })
    ));
    assert!(cut.source().ptr_eq(tilting.module()));
    assert_eq!(cut.tilting_limits(), tilting.limits());
    assert_eq!(cut.limits(), &limits);
    assert!(outcome.verify());

    let limits = TargetLimits {
        max_radical_products: 0,
        ..TargetLimits::default()
    };
    let outcome = present_target(&tilting, &limits).unwrap();
    assert!(matches!(
        outcome.cut().expect("the radical budget is zero").reason(),
        TargetCutReason::Budget(TargetBudgetCut {
            stage: TargetCutStage::RadicalPower { .. },
            ..
        })
    ));
    assert!(outcome.verify());

    let limits = TargetLimits {
        max_paths: 0,
        ..TargetLimits::default()
    };
    let outcome = present_target(&tilting, &limits).unwrap();
    assert!(matches!(
        outcome.cut().expect("the path budget is zero").reason(),
        TargetCutReason::Budget(TargetBudgetCut {
            stage: TargetCutStage::Paths { length: 2 },
            ..
        })
    ));
    assert!(outcome.verify());

    let limits = TargetLimits {
        max_relation_terms: 0,
        ..TargetLimits::default()
    };
    let outcome = present_target(&tilting, &limits).unwrap();
    assert!(matches!(
        outcome.cut().expect("the relation budget is zero").reason(),
        TargetCutReason::Budget(TargetBudgetCut {
            stage: TargetCutStage::Relations { .. },
            ..
        })
    ));
    assert!(outcome.verify());
}

#[test]
fn completion_exhaustion_keeps_its_diagnostics() {
    let algebra = dual_numbers(f5());
    let tilting = tilting(&regular(&algebra));
    let mut limits = TargetLimits::default();
    limits.completion.max_steps = 0;
    let outcome = present_target(&tilting, &limits).unwrap();
    assert!(matches!(
        outcome.cut().expect("completion must stop").reason(),
        TargetCutReason::Completion(_)
    ));
    assert!(outcome.verify());
}
