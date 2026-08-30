use auslander::algebra::an_with_relations;
use auslander::basic::{AddClosureWitness, BasicDecomposition};
use auslander::derived::{AddTComplex, DerivedEquivalenceCertificate};
use auslander::endo::EndoAlgebra;
use auslander::field::PrimeField;
use auslander::hom::identity;
use auslander::homotopy::{BoundedComplex, HomotopyHom};
use auslander::module::{Module, direct_sum};
use auslander::target::{TargetLimits, TargetPresentationOutcome, present_target};
use auslander::tilting::{ClassicalTiltingResult, TiltingLimits, classify};

fn main() {
    let field = PrimeField::new(5).unwrap();
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let injectives: Vec<Module> = (0..3)
        .map(|vertex| Module::injective(&algebra, vertex))
        .collect();
    let tilting_module = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
    let ClassicalTiltingResult::Tilting(tilting) = classify(
        &tilting_module,
        TiltingLimits {
            max_projective_dimension: 4,
            max_generation_steps: 8,
        },
    )
    .unwrap() else {
        panic!("the dual A3/(ab) fixture is classical tilting")
    };
    let TargetPresentationOutcome::Presented(target) =
        present_target(&tilting, &TargetLimits::default()).unwrap()
    else {
        panic!("the tilting target is split")
    };
    let certificate = DerivedEquivalenceCertificate::new(tilting, target).unwrap();
    assert!(certificate.verify());

    let endomorphisms = EndoAlgebra::new(&tilting_module);
    let differential = endomorphisms
        .basis()
        .iter()
        .find(|map| !map.is_zero() && **map != identity(&tilting_module))
        .unwrap()
        .clone();
    let complex = BoundedComplex::new(
        0,
        vec![tilting_module.clone(), tilting_module.clone()],
        vec![differential],
    )
    .unwrap();
    let basic = BasicDecomposition::new(&tilting_module).unwrap();
    let witness = AddClosureWitness::from_module(&tilting_module, &basic)
        .unwrap()
        .expect("T belongs to add(T)");
    let source = AddTComplex::new(complex, vec![witness.clone(), witness]).unwrap();
    let transported = certificate.transport().forward(&source).unwrap();
    let recovered = certificate.transport().reverse(&transported).unwrap();
    assert!(recovered.verify());
    assert!(
        certificate
            .transport()
            .source_round_trip(&source)
            .unwrap()
            .verify()
    );
    assert!(
        certificate
            .transport()
            .target_round_trip(&transported)
            .unwrap()
            .verify()
    );

    let graded_dimensions: Vec<(i32, usize)> = (-2..=2)
        .map(|degree| {
            let source_hom = HomotopyHom::new(source.complex(), source.complex(), degree)
                .unwrap()
                .quotient()
                .unwrap();
            let target_hom = HomotopyHom::new(transported.complex(), transported.complex(), degree)
                .unwrap()
                .quotient()
                .unwrap();
            assert_eq!(source_hom.dim(), target_hom.dim());
            (degree, source_hom.dim())
        })
        .collect();

    println!(
        "target dimension: {}; resolution width: {}; graded Hom dimensions: {:?}",
        certificate.target().target().dim(),
        certificate.tilting().projective_dimension(),
        graded_dimensions
    );
}
