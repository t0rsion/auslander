use auslander::algebra::an_with_relations;
use auslander::basic::{AddClosureWitness, BasicDecomposition};
use auslander::derived::{AddTComplex, DerivedEquivalenceCertificate};
use auslander::endo::EndoAlgebra;
use auslander::field::PrimeField;
use auslander::hom::Morphism;
use auslander::homotopy::{BoundedComplex, ChainMap};
use auslander::module::{Module, direct_sum};
use auslander::target::{TargetLimits, TargetPresentationOutcome, present_target};
use auslander::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};

pub(super) fn pd2_tilting(field: PrimeField) -> ClassicalTiltingModule {
    let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
    let injectives: Vec<Module> = (0..3)
        .map(|vertex| Module::injective(&algebra, vertex))
        .collect();
    let module = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
    let limits = TiltingLimits {
        max_projective_dimension: 4,
        max_generation_steps: 8,
    };
    let ClassicalTiltingResult::Tilting(tilting) =
        ClassicalTiltingModule::classify(&module, limits).unwrap()
    else {
        panic!("the dual A3/(ab) fixture is classical tilting")
    };
    assert_eq!(tilting.projective_dimension(), 2);
    tilting
}

pub(super) fn certificate(field: PrimeField) -> DerivedEquivalenceCertificate {
    let tilting = pd2_tilting(field);
    let TargetPresentationOutcome::Presented(target) =
        present_target(&tilting, &TargetLimits::default()).unwrap()
    else {
        panic!("the dual A3/(ab) target is split")
    };
    DerivedEquivalenceCertificate::new(tilting, target).unwrap()
}

pub(super) fn one_term_source(certificate: &DerivedEquivalenceCertificate) -> AddTComplex {
    let module = certificate.tilting().module();
    let basic = BasicDecomposition::new(module).unwrap();
    let witness = AddClosureWitness::from_module(module, &basic)
        .unwrap()
        .expect("T belongs to add(T)");
    AddTComplex::new(
        BoundedComplex::new(0, vec![module.clone()], Vec::new()).unwrap(),
        vec![witness],
    )
    .unwrap()
}

pub(super) fn two_term_source(certificate: &DerivedEquivalenceCertificate) -> AddTComplex {
    let module = certificate.tilting().module();
    let endo = EndoAlgebra::new(module);
    let differential = endo
        .basis()
        .iter()
        .find(|map| {
            !map.is_zero()
                && !map.is_isomorphism()
                && map.then(map).is_ok_and(|square| square.is_zero())
        })
        .expect("the pd2 fixture has a nonzero square-zero radical endomorphism")
        .clone();
    let complex = BoundedComplex::new(0, vec![module.clone(), module.clone()], vec![differential])
        .expect("the selected radical endomorphism forms a two-term complex");
    let basic = BasicDecomposition::new(module).expect("the tilting module is basic");
    let witness = AddClosureWitness::from_module(module, &basic)
        .expect("membership decomposes")
        .expect("T belongs to add(T)");
    AddTComplex::new(complex, vec![witness.clone(), witness])
        .expect("the two-term complex has add(T) witnesses")
}

pub(super) fn shifted_source(source: &AddTComplex, degree: i32) -> AddTComplex {
    AddTComplex::new(
        source
            .complex()
            .shift(degree)
            .expect("the fixture shift fits in homological degrees"),
        source.witnesses().to_vec(),
    )
    .expect("shifting preserves add(T) witnesses")
}

pub(super) fn zero_chain_map(map: &ChainMap) -> bool {
    map.components().iter().all(Morphism::is_zero)
}

pub(super) fn witnessed_source(complex: BoundedComplex, target: &Module) -> AddTComplex {
    let basic = BasicDecomposition::new(target).expect("the source witness target is basic");
    let witnesses = complex
        .terms()
        .iter()
        .map(|term| {
            AddClosureWitness::from_module(term, &basic)
                .expect("the padded term decomposes")
                .expect("every padded term lies in add(T)")
        })
        .collect();
    AddTComplex::new(complex, witnesses).expect("padded source witnesses match terms")
}
