use super::*;
use crate::algebra::{an_with_relations, dual_numbers, kronecker, linear_an};
use crate::field::PrimeField;
use crate::linalg::DenseMat;
use crate::module::direct_sum;

fn fields() -> [PrimeField; 2] {
    [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
}

fn generous() -> TiltingLimits {
    TiltingLimits {
        max_projective_dimension: 4,
        max_generation_steps: 5,
    }
}

fn sum(parts: &[Module]) -> Module {
    direct_sum(&parts.iter().collect::<Vec<_>>()).0
}

#[test]
fn regular_module_is_zero_tilting_over_f2_and_f5() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let regular = regular_module(&algebra);
        let ClassicalTiltingResult::Tilting(tilting) = classify(&regular, generous()).unwrap()
        else {
            panic!("the regular module is tilting")
        };
        assert_eq!(tilting.projective_dimension(), 0);
        assert!(tilting.ext_spaces().is_empty());
        assert_eq!(tilting.generation_complex().complex().len(), 2);
        assert!(
            tilting.generation_complex().complex().terms()[1].dim_vector() == regular.dim_vector()
        );
        assert!(tilting.verify());
    }
}

#[test]
fn dual_numbers_simple_keeps_an_honest_projective_cut() {
    for field in fields() {
        let algebra = dual_numbers(field);
        let simple = Module::simple(&algebra, 0);
        let limits = TiltingLimits {
            max_projective_dimension: 2,
            max_generation_steps: 3,
        };
        let ClassicalTiltingResult::Undetermined(TiltingBlocker::ProjectiveDimension(blocker)) =
            classify(&simple, limits).unwrap()
        else {
            panic!("the periodic resolution must cut")
        };
        assert_eq!(blocker.lower_bound(), 3);
        assert!(blocker.verify());
    }
}

#[test]
fn self_extension_is_the_only_negative_outcome() {
    for field in fields() {
        let algebra = kronecker(2, field);
        let mut first = DenseMat::zero(1, 1);
        first.set(0, 0, field.one());
        let module = Module::new(algebra, vec![1, 1], vec![first, DenseMat::zero(1, 1)]).unwrap();
        let ClassicalTiltingResult::NotTilting(witness) = classify(&module, generous()).unwrap()
        else {
            panic!("the Kronecker module has a self-extension")
        };
        assert_eq!(witness.degree(), 1);
        assert_eq!(witness.dimension(), 1);
        assert!(witness.verify());
    }
}

#[test]
fn generation_has_separate_step_and_non_monic_blockers() {
    for field in fields() {
        let algebra = linear_an(3, field);
        let regular = regular_module(&algebra);
        let limits = TiltingLimits {
            max_projective_dimension: 0,
            max_generation_steps: 0,
        };
        let ClassicalTiltingResult::Undetermined(TiltingBlocker::Generation(
            step @ GenerationBlocker::StepLimit { .. },
        )) = classify(&regular, limits).unwrap()
        else {
            panic!("zero generation steps must cut")
        };
        assert_eq!(step.stage(), 0);
        assert!(step.verify());

        let simple = Module::simple(&algebra, 0);
        let ClassicalTiltingResult::Undetermined(TiltingBlocker::Generation(
            non_monic @ GenerationBlocker::NonMonic { .. },
        )) = classify(&simple, generous()).unwrap()
        else {
            panic!("the approximation of A by add(S_0) is not monic")
        };
        assert_eq!(non_monic.stage(), 0);
        assert!(non_monic.verify());
    }
}

#[test]
fn dual_module_over_a3_mod_ab_is_pd2_tilting() {
    for field in fields() {
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let injectives: Vec<Module> = (0..3)
            .map(|vertex| Module::injective(&algebra, vertex))
            .collect();
        let dual = sum(&injectives);
        assert_eq!(dual.dim_vector(), [2, 2, 1]);
        let ClassicalTiltingResult::Tilting(tilting) = classify(&dual, generous()).unwrap() else {
            panic!("D(A) is the named projective-dimension-two tilting fixture")
        };
        assert_eq!(tilting.projective_dimension(), 2);
        let dimensions: Vec<&[usize]> = tilting
            .generation_complex()
            .complex()
            .terms()
            .iter()
            .map(Module::dim_vector)
            .collect();
        assert_eq!(
            dimensions,
            vec![&[1, 2, 2][..], &[1, 3, 2], &[1, 1, 0], &[1, 0, 0]]
        );
        assert!(tilting.verify());
    }
}

#[test]
fn repeated_summand_is_a_basic_error() {
    let algebra = linear_an(2, PrimeField::new(5).unwrap());
    let projective = Module::projective(&algebra, 0);
    let doubled = sum(&[projective.clone(), projective]);
    assert_eq!(
        classify(&doubled, generous()).unwrap_err(),
        TiltingError::Basic(BasicError::NotBasic {
            first: 0,
            second: 1,
        })
    );
}

#[test]
fn pd2_generation_step_bound_keeps_the_partial_complex() {
    let field = PrimeField::new(5).unwrap();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let dual = sum(&(0..3)
        .map(|vertex| Module::injective(&algebra, vertex))
        .collect::<Vec<_>>());
    let limits = TiltingLimits {
        max_projective_dimension: 2,
        max_generation_steps: 2,
    };
    let ClassicalTiltingResult::Undetermined(TiltingBlocker::Generation(
        blocker @ GenerationBlocker::StepLimit { .. },
    )) = classify(&dual, limits).unwrap()
    else {
        panic!("two maps do not finish the three-map generation complex")
    };
    assert_eq!(blocker.stage(), 2);
    assert_eq!(blocker.partial_complex().len(), 3);
    assert!(blocker.verify());
}
