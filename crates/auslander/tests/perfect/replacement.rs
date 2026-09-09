use auslander::algebra::{an_with_relations, dual_numbers};
use auslander::control::{ComputationControl, ProgressStage};
use auslander::hom::zero_morphism;
use auslander::homotopy::BoundedComplex;
use auslander::module::Module;
use auslander::perfect::{
    ReplacementCompletedStage, ReplacementLimits, ReplacementOutcome, ReplacementResource,
    replace_perfect,
};

#[test]
fn a_pd2_module_gets_its_complete_minimal_replacement() {
    for field in [super::common::f2(), super::f5()] {
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let simple = Module::simple(&algebra, 0);
        let input = BoundedComplex::new(0, vec![simple], vec![]).unwrap();
        let control = ComputationControl::new();
        let ReplacementOutcome::Replaced(replacement) =
            replace_perfect(&input, ReplacementLimits::default(), Some(&control)).unwrap()
        else {
            panic!("the fixed pd2 module has a finite replacement")
        };
        assert!(replacement.verify());
        assert_eq!(replacement.projective().complex().range().lower(), 0);
        assert_eq!(replacement.projective().complex().range().upper(), 2);
        let dimensions: Vec<Vec<usize>> = replacement
            .projective()
            .complex()
            .terms()
            .iter()
            .map(|term| term.dim_vector().to_vec())
            .collect();
        assert_eq!(
            dimensions,
            vec![vec![1, 1, 0], vec![0, 1, 1], vec![0, 0, 1]]
        );
        assert_eq!(control.progress().completed_work(), 28);
        assert_eq!(control.progress().reserved_work(), 28);
    }
}

#[test]
fn an_infinite_resolution_returns_a_checked_cut() {
    let algebra = dual_numbers(super::f5());
    let simple = Module::simple(&algebra, 0);
    let input = BoundedComplex::new(0, vec![simple], vec![]).unwrap();
    let limits = ReplacementLimits {
        max_resolution_steps: 2,
        ..ReplacementLimits::default()
    };
    let ReplacementOutcome::Cut(cut) = replace_perfect(&input, limits, None).unwrap() else {
        panic!("the periodic simple reaches the fixed resolution limit")
    };
    assert!(cut.verify());
    assert_eq!(cut.prefix().len(), 3);
    assert!(cut.next_kernel().is_some_and(|kernel| !kernel.is_zero()));
    assert_eq!(
        cut.rejected().resource(),
        ReplacementResource::ResolutionSteps
    );
    assert_eq!(cut.rejected().requested(), 3);
    assert_eq!(cut.rejected().limit(), 2);
}

#[test]
fn cancellation_keeps_the_last_complete_prefix() {
    let algebra = dual_numbers(super::f5());
    let simple = Module::simple(&algebra, 0);
    let input = BoundedComplex::new(0, vec![simple], vec![]).unwrap();
    let control = ComputationControl::new();
    control.cancel();
    let ReplacementOutcome::Cancelled(cancelled) =
        replace_perfect(&input, ReplacementLimits::default(), Some(&control)).unwrap()
    else {
        panic!("a clear pre-loop cancellation is typed")
    };
    assert!(cancelled.verify());
    assert!(cancelled.prefix().is_empty());
    assert_eq!(cancelled.last_completed(), ReplacementCompletedStage::Input);
    assert_eq!(control.progress().stage(), ProgressStage::Idle);
}

#[test]
fn a_two_term_complex_totalizes_to_a_projective_model() {
    let algebra = an_with_relations(3, &[(0, 2)], super::f5()).unwrap();
    let s0 = Module::simple(&algebra, 0);
    let s1 = Module::simple(&algebra, 1);
    let differential = zero_morphism(&s1, &s0).unwrap();
    let input = BoundedComplex::new(-1, vec![s0, s1], vec![differential]).unwrap();
    let control = ComputationControl::new();
    let ReplacementOutcome::Replaced(replacement) =
        replace_perfect(&input, ReplacementLimits::default(), Some(&control)).unwrap()
    else {
        panic!("the bounded Dynkin complex has a finite replacement")
    };
    assert!(replacement.verify());
    assert_eq!(control.progress().stage(), ProgressStage::Complete);
    assert_eq!(replacement.projective().complex().lower(), -1);
    assert!(replacement.projective().complex().upper() >= 1);
}
