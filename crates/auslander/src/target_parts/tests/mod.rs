use std::sync::Arc;

use crate::algebra::{Algebra, an_with_relations, dual_numbers, linear_an};
use crate::field::PrimeField;
use crate::module::{Module, direct_sum};
use crate::target::{
    TargetBudgetCut, TargetCutReason, TargetCutStage, TargetLimits, TargetWork, present_target,
};
use crate::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};

mod budgets;
mod presentation;

fn f5() -> PrimeField {
    PrimeField::new(5).unwrap()
}

fn tilting(module: &Module) -> ClassicalTiltingModule {
    let limits = TiltingLimits {
        max_projective_dimension: 4,
        max_generation_steps: 8,
    };
    let ClassicalTiltingResult::Tilting(value) =
        ClassicalTiltingModule::classify(module, limits).unwrap()
    else {
        panic!("the fixture is classical tilting")
    };
    value
}

fn regular(algebra: &Arc<Algebra>) -> Module {
    let parts: Vec<Module> = (0..algebra.quiver().num_vertices())
        .map(|vertex| Module::projective(algebra, vertex))
        .collect();
    match parts.as_slice() {
        [only] => only.clone(),
        _ => direct_sum(&parts.iter().collect::<Vec<_>>()).0,
    }
}
