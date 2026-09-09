use std::hint::black_box;

use auslander::algebra::{an_with_relations, dual_numbers, linear_an};
use auslander::module::{Module, direct_sum};
use auslander::target::{TargetLimits, present_target};
use auslander::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};

use super::perf_support::{Runner, f2, f5, regular};

pub(crate) fn target_tilting(module: &Module) -> ClassicalTiltingModule {
    let limits = TiltingLimits {
        max_projective_dimension: 4,
        max_generation_steps: 8,
    };
    let ClassicalTiltingResult::Tilting(tilting) =
        ClassicalTiltingModule::classify(module, limits).expect("the fixture classifies")
    else {
        panic!("the target benchmark fixture is classical tilting")
    };
    tilting
}

fn target_case(r: &mut Runner, name: &str, module: &Module) {
    let tilting = target_tilting(module);
    let limits = TargetLimits::default();
    let preview = present_target(&tilting, &limits)
        .expect("target recovery succeeds")
        .presented()
        .expect("the target is split")
        .clone();
    let work = preview.work();
    let label = format!(
        "present_target {name} endo={} radical={} paths={} terms={}",
        work.endo_dimension, work.radical_products, work.paths, work.relation_terms
    );
    r.case("target", &label, 1, || {
        black_box(present_target(&tilting, &limits).expect("target recovery succeeds"));
    });
    r.case("target", &format!("verify {name}"), 1, || {
        assert!(black_box(preview.verify()), "target verification failed");
    });
}

pub(crate) fn target_layer(r: &mut Runner) {
    for (field_name, field) in [("f2", f2()), ("f5", f5())] {
        let generator_algebra = linear_an(3, field);
        target_case(
            r,
            &format!("generator-a3-{field_name}"),
            &regular(&generator_algebra),
        );

        let relation_algebra = dual_numbers(field);
        target_case(
            r,
            &format!("dual-numbers-{field_name}"),
            &regular(&relation_algebra),
        );

        let pd2_algebra =
            an_with_relations(3, &[(0, 2)], field).expect("the zero path is admissible");
        let injectives: Vec<Module> = (0..3)
            .map(|vertex| Module::injective(&pd2_algebra, vertex))
            .collect();
        let pd2 = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
        target_case(r, &format!("pd2-dual-{field_name}"), &pd2);
    }
}
