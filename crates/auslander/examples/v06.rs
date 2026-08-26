use auslander::algebra::{an_with_relations, truncated_poly};
use auslander::field::PrimeField;
use auslander::hochschild::{BarLimits, HochschildDegree, HochschildOutcome, bar_hochschild};
use auslander::module::{Module, direct_sum};
use auslander::resolution::resolve;
use auslander::tilting::{ClassicalTiltingResult, TiltingLimits, classify};

fn bar_limits() -> BarLimits {
    BarLimits {
        max_tensor_tuples: 10_000,
        max_cochain_dim: 100_000,
        max_matrix_entries: 10_000_000,
        max_work_units: 1_000_000_000,
    }
}

fn main() {
    for prime in [2, 5] {
        let field = PrimeField::new(prime).unwrap();
        let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
        let injectives: Vec<Module> = (0..3)
            .map(|vertex| Module::injective(&algebra, vertex))
            .collect();
        let dual = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
        let result = classify(
            &dual,
            TiltingLimits {
                max_projective_dimension: 4,
                max_generation_steps: 5,
            },
        )
        .unwrap();
        let ClassicalTiltingResult::Tilting(tilting) = result else {
            panic!("D(A) must be the designated tilting module")
        };
        assert_eq!(dual.dim_vector(), [2, 2, 1]);
        assert_eq!(tilting.projective_dimension(), 2);
        assert_eq!(
            tilting
                .generation_complex()
                .complex()
                .terms()
                .iter()
                .map(|term| term.dim_vector().to_vec())
                .collect::<Vec<_>>(),
            [[1, 2, 2], [1, 3, 2], [1, 1, 0], [1, 0, 0]]
        );
        assert!(tilting.generation_complex().verify());
        assert!(tilting.verify());
    }

    let field = PrimeField::new(5).unwrap();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let exact = resolve(&Module::simple(&algebra, 0), 2)
        .checked_complex()
        .unwrap();
    assert!(exact.verify());

    let x_cubed = truncated_poly(3, field).unwrap();
    let HochschildOutcome::Complete(cohomology) =
        bar_hochschild(&x_cubed, 2, bar_limits()).unwrap()
    else {
        panic!("the explicit limits must admit degrees zero through two")
    };
    assert_eq!(
        cohomology
            .degrees()
            .iter()
            .map(HochschildDegree::dim)
            .collect::<Vec<_>>(),
        [3, 2, 2]
    );
    assert!(cohomology.verify());

    let mut cut_limits = bar_limits();
    cut_limits.max_work_units = 0;
    let HochschildOutcome::Cut(cut) = bar_hochschild(&x_cubed, 2, cut_limits).unwrap() else {
        panic!("zero work must produce a typed cut")
    };
    assert!(cut.completed_degrees().is_empty());
    assert!(cut.verify());
}
