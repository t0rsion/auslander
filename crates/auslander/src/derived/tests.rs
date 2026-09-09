use super::*;
use crate::algebra::{Algebra, an_with_relations, linear_an};
use crate::basic::{AddClosureWitness, BasicDecomposition};
use crate::endo::EndoAlgebra;
use crate::field::PrimeField;
use crate::hom::{identity, zero_morphism};
use crate::homotopy::{BoundedComplex, ChainHomotopy, ChainMap};
use crate::module::{Module, direct_sum};
use crate::resolution::{ResolutionEnd, resolve};
use crate::target::{
    TargetLimits, TargetPresentationOutcome, VerifiedTargetPresentation, present_target,
};
use crate::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};
use std::sync::Arc;

fn f5() -> PrimeField {
    PrimeField::new(5).expect("5 is prime")
}

fn f2() -> PrimeField {
    PrimeField::new(2).expect("2 is prime")
}

fn regular(algebra: &Arc<Algebra>) -> Module {
    let projectives: Vec<Module> = (0..algebra.quiver().num_vertices())
        .map(|vertex| Module::projective(algebra, vertex))
        .collect();
    direct_sum(&projectives.iter().collect::<Vec<_>>()).0
}

fn strict_regular_transport() -> (StrictTransport, Module) {
    let algebra = linear_an(2, f5());
    let module = regular(&algebra);
    let limits = TiltingLimits {
        max_projective_dimension: 4,
        max_generation_steps: 8,
    };
    let ClassicalTiltingResult::Tilting(tilting) =
        ClassicalTiltingModule::classify(&module, limits).expect("fixture classifies")
    else {
        panic!("the regular module is classical tilting")
    };
    let TargetPresentationOutcome::Presented(target) =
        present_target(&tilting, &TargetLimits::default()).expect("target completes")
    else {
        panic!("the regular target is split")
    };
    (
        StrictTransport::new(target).expect("strict transport builds"),
        module,
    )
}

fn regular_certificate_inputs() -> (ClassicalTiltingModule, VerifiedTargetPresentation) {
    let algebra = linear_an(2, f5());
    let module = regular(&algebra);
    let limits = TiltingLimits {
        max_projective_dimension: 4,
        max_generation_steps: 8,
    };
    let ClassicalTiltingResult::Tilting(tilting) =
        ClassicalTiltingModule::classify(&module, limits).expect("fixture classifies")
    else {
        panic!("the regular module is classical tilting")
    };
    let TargetPresentationOutcome::Presented(target) =
        present_target(&tilting, &TargetLimits::default()).expect("target completes")
    else {
        panic!("the regular target is split")
    };
    (tilting, target)
}

#[test]
fn regular_generator_transports_one_term_in_both_directions() {
    let (transport, module) = strict_regular_transport();
    let basic = BasicDecomposition::new(&module).expect("regular module is basic");
    let witness = AddClosureWitness::from_module(&module, &basic)
        .expect("membership decomposes")
        .expect("T lies in add(T)");
    let source = AddTComplex::new(
        BoundedComplex::new(0, vec![module], Vec::new()).expect("one term is a complex"),
        vec![witness],
    )
    .expect("witnessed source builds");
    let target = transport
        .forward(&source)
        .expect("forward transport builds");
    assert!(target.verify());
    let back = transport
        .reverse(&target)
        .expect("reverse transport builds");
    assert!(back.verify());
    assert!(transport.source_round_trip(&source).is_ok());
    assert!(transport.target_round_trip(&target).is_ok());
}

#[test]
fn regular_generator_transports_a_chain_map_and_round_trip() {
    let (transport, module) = strict_regular_transport();
    let basic = BasicDecomposition::new(&module).expect("regular module is basic");
    let witness = AddClosureWitness::from_module(&module, &basic)
        .expect("membership decomposes")
        .expect("T lies in add(T)");
    let complex = BoundedComplex::new(
        0,
        vec![module.clone(), module.clone()],
        vec![identity(&module)],
    )
    .expect("identity is a one-step complex");
    let source = AddTComplex::new(complex.clone(), vec![witness.clone(), witness])
        .expect("witnessed source builds");
    let map = ChainMap::identity(&complex);
    assert!(transport.forward_chain_map(&source, &source, &map).is_ok());
    let target = transport
        .forward(&source)
        .expect("forward transport builds");
    assert!(
        transport
            .reverse_chain_map(&target, &target, &ChainMap::identity(target.complex()))
            .is_ok()
    );
    assert!(transport.source_round_trip(&source).is_ok());
}

#[test]
fn transport_normalizes_unequal_chain_supports_before_mapping() {
    let (transport, module) = strict_regular_transport();
    let basic = BasicDecomposition::new(&module).expect("regular module is basic");
    let witness = AddClosureWitness::from_module(&module, &basic)
        .expect("membership decomposes")
        .expect("T lies in add(T)");
    let low = AddTComplex::new(
        BoundedComplex::new(0, vec![module.clone()], Vec::new()).expect("one term is a complex"),
        vec![witness.clone()],
    )
    .expect("lower source builds");
    let high = AddTComplex::new(
        BoundedComplex::new(1, vec![module.clone()], Vec::new()).expect("one term is a complex"),
        vec![witness],
    )
    .expect("upper source builds");
    let map =
        ChainMap::zero(low.complex(), high.complex()).expect("the offset zero map is a chain map");
    assert_eq!((map.range().lower(), map.range().upper()), (0, 1));
    let target_map = transport
        .forward_chain_map(&low, &high, &map)
        .expect("forward map accepts padded support");
    assert!(target_map.verify());
    let low_target = transport.forward(&low).expect("lower target builds");
    let high_target = transport.forward(&high).expect("upper target builds");
    let reverse_map = transport
        .reverse_chain_map(&low_target, &high_target, &target_map)
        .expect("reverse map accepts padded support");
    assert!(reverse_map.verify());

    let homotopy = ChainHomotopy::new(low.complex(), high.complex(), vec![identity(&module)])
        .expect("the offset identity is a homotopy component");
    let target_homotopy = transport
        .forward_homotopy(&low, &high, &homotopy)
        .expect("forward homotopy accepts padded support");
    assert!(target_homotopy.verify());
    let reverse_homotopy = transport
        .reverse_homotopy(&low_target, &high_target, &target_homotopy)
        .expect("reverse homotopy accepts padded support");
    assert!(reverse_homotopy.verify());

    assert!(transport.forward_cone(&low, &high, &map).is_ok());
    assert!(
        transport
            .reverse_cone(&low_target, &high_target, &target_map)
            .is_ok()
    );
}

#[test]
fn regular_generator_has_a_verified_derived_certificate() {
    let (tilting, target) = regular_certificate_inputs();
    let certificate = DerivedEquivalenceCertificate::new(tilting, target)
        .expect("regular generator has a certificate");
    assert!(certificate.verify());
    assert_eq!(certificate.graded_homotopy().len(), 1);
    assert_eq!(
        certificate.degree_zero_identification().quotient().dim(),
        certificate.target().endo().dim()
    );
}

#[test]
fn projective_dimension_one_tilting_module_has_a_certificate() {
    let algebra = linear_an(2, f5());
    let p0 = Module::projective(&algebra, 0);
    let s0 = Module::simple(&algebra, 0);
    let module = direct_sum(&[&p0, &s0]).0;
    let limits = TiltingLimits {
        max_projective_dimension: 4,
        max_generation_steps: 8,
    };
    let ClassicalTiltingResult::Tilting(tilting) =
        ClassicalTiltingModule::classify(&module, limits).expect("fixture classifies")
    else {
        panic!("the fixture is classical tilting")
    };
    let TargetPresentationOutcome::Presented(target) =
        present_target(&tilting, &TargetLimits::default()).expect("target completes")
    else {
        panic!("the tilting target is split")
    };
    let certificate = DerivedEquivalenceCertificate::new(tilting, target)
        .expect("projective-dimension-one fixture has a certificate");
    assert!(certificate.verify());
    assert_eq!(certificate.graded_homotopy().len(), 3);
}

#[test]
fn projective_dimension_two_fixture_has_a_certificate_over_f2_and_f5() {
    for field in [f2(), f5()] {
        let algebra = an_with_relations(3, &[(0, 2)], field).expect("ab is a valid relation");
        let injectives: Vec<Module> = (0..3)
            .map(|vertex| Module::injective(&algebra, vertex))
            .collect();
        let module = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
        let limits = TiltingLimits {
            max_projective_dimension: 4,
            max_generation_steps: 8,
        };
        let ClassicalTiltingResult::Tilting(tilting) =
            ClassicalTiltingModule::classify(&module, limits).expect("fixture classifies")
        else {
            panic!("the dual fixture is classical tilting")
        };
        assert_eq!(
            tilting.projective_dimension(),
            2,
            "over F_{}",
            field.modulus()
        );
        let TargetPresentationOutcome::Presented(target) =
            present_target(&tilting, &TargetLimits::default()).expect("target completes")
        else {
            panic!("the dual target is split")
        };
        let certificate = DerivedEquivalenceCertificate::new(tilting, target)
            .expect("pd2 fixture has a certificate");
        assert!(certificate.verify(), "over F_{}", field.modulus());
        assert_eq!(certificate.graded_homotopy().len(), 5);
        assert!(
            certificate
                .graded_homotopy()
                .iter()
                .filter(|space| space.degree() != 0)
                .all(|space| space.quotient().dim() == 0)
        );
    }
}

#[test]
fn nonidentity_two_term_complex_and_chain_map_round_trip() {
    let (transport, module) = strict_regular_transport();
    let endo = EndoAlgebra::new(&module);
    let differential = endo
        .basis()
        .iter()
        .find(|map| !map.is_zero() && **map != identity(&module))
        .expect("A_2 has a nonidentity endomorphism")
        .clone();
    let complex = BoundedComplex::new(
        0,
        vec![module.clone(), module.clone()],
        vec![differential.clone()],
    )
    .expect("one differential forms a complex");
    let map = ChainMap::new(&complex, &complex, vec![differential.clone(), differential])
        .expect("the same endomorphism in both degrees is a chain map");
    let basic = BasicDecomposition::new(&module).expect("regular module is basic");
    let witness = AddClosureWitness::from_module(&module, &basic)
        .expect("membership decomposes")
        .expect("T lies in add(T)");
    let source =
        AddTComplex::new(complex, vec![witness.clone(), witness]).expect("witnessed source builds");
    let target_map = transport
        .forward_chain_map(&source, &source, &map)
        .expect("forward map transport builds");
    assert!(target_map.verify());
    let target = transport.forward(&source).expect("forward complex builds");
    let target_map_again = transport
        .forward_chain_map(&source, &source, &map)
        .expect("independent forward map transport builds");
    let source_product = map.then(&map).expect("source maps compose");
    let target_product = transport
        .forward_chain_map(&source, &source, &source_product)
        .expect("forward product transport builds");
    assert!(
        target_product.agrees_with(
            &target_map
                .then(&target_map_again)
                .expect("independent forward images compose")
        )
    );
    let reverse_map = transport
        .reverse_chain_map(&target, &target, &target_map)
        .expect("reverse map transport builds");
    assert!(reverse_map.verify());
    let reverse_map_again = transport
        .reverse_chain_map(&target, &target, &target_map_again)
        .expect("independent reverse map transport builds");
    let reverse_product = transport
        .reverse_chain_map(&target, &target, &target_product)
        .expect("reverse product transport builds");
    assert!(
        reverse_product.agrees_with(
            &reverse_map
                .then(&reverse_map_again)
                .expect("independent reverse images compose")
        )
    );
    let homotopy = ChainHomotopy::new(
        source.complex(),
        source.complex(),
        vec![zero_morphism(&module, &module).expect("zero map exists")],
    )
    .expect("zero component is a homotopy");
    let target_homotopy = transport
        .forward_homotopy(&source, &source, &homotopy)
        .expect("forward homotopy transport builds");
    assert!(target_homotopy.verify());
    let reverse_homotopy = transport
        .reverse_homotopy(&target, &target, &target_homotopy)
        .expect("reverse homotopy transport builds");
    assert!(reverse_homotopy.verify());
    assert!(transport.forward_cone(&source, &source, &map).is_ok());
    assert!(
        transport
            .reverse_cone(&target, &target, &target_map)
            .is_ok()
    );
    assert!(transport.forward_shift(&source, 2).is_ok());
    assert!(transport.reverse_shift(&target, -2).is_ok());
    assert!(transport.forward_direct_sum(&[&source, &source]).is_ok());
    assert!(transport.reverse_direct_sum(&[&target, &target]).is_ok());
    assert!(transport.source_round_trip(&source).is_ok());
    assert!(transport.target_round_trip(&target).is_ok());
}

#[test]
fn strict_domains_reject_the_first_bad_source_and_target_terms() {
    let (transport, module) = strict_regular_transport();
    let algebra = module.algebra().clone();
    let p0 = Module::projective(&algebra, 0);
    let p0_basic = BasicDecomposition::new(&p0).expect("P_0 is basic");
    let wrong_witness = AddClosureWitness::from_module(&p0, &p0_basic)
        .expect("membership decomposes")
        .expect("P_0 lies in add(P_0)");
    let wrong_source = AddTComplex::new(
        BoundedComplex::new(0, vec![p0], Vec::new()).expect("one term is a complex"),
        vec![wrong_witness],
    )
    .expect("the unrelated witness is internally valid");
    assert!(matches!(
        transport.forward(&wrong_source),
        Err(TransportError::SourceWitnessTarget { term: 0 })
    ));

    let target_algebra = transport.target().target();
    let nonprojective = (0..target_algebra.quiver().num_vertices())
        .map(|vertex| Module::simple(target_algebra, vertex))
        .find(|simple| matches!(resolve(simple, 0).end, ResolutionEnd::Cut { .. }))
        .expect("a nonsemisimple target has a nonprojective simple");
    assert!(matches!(
        transport.target_complex(
            BoundedComplex::new(0, vec![nonprojective], Vec::new()).expect("one term is a complex")
        ),
        Err(TransportError::TargetTermNotProjective { term: 0 })
    ));
}

#[test]
fn derived_certificate_and_transport_mutations_fail_verification() {
    let (tilting, target) = regular_certificate_inputs();
    let certificate = DerivedEquivalenceCertificate::new(tilting, target)
        .expect("regular generator has a certificate");
    assert!(certificate.verify());

    let mut changed = certificate;
    changed.graded_homotopy[0].degree = 1;
    assert!(!changed.verify());

    let (tilting, target) = regular_certificate_inputs();
    let mut changed = DerivedEquivalenceCertificate::new(tilting, target)
        .expect("regular generator has a certificate");
    let entry = changed.degree_zero.coordinates.get(0, 0);
    let field = changed.target.endo().field();
    changed
        .degree_zero
        .coordinates
        .set(0, 0, field.add(entry, field.one()));
    assert!(!changed.verify());

    let (transport, module) = strict_regular_transport();
    assert!(transport.verify());
    let basic = BasicDecomposition::new(&module).expect("regular module is basic");
    let witness = AddClosureWitness::from_module(&module, &basic)
        .expect("membership decomposes")
        .expect("T lies in add(T)");
    let source = AddTComplex::new(
        BoundedComplex::new(0, vec![module], Vec::new()).expect("one term is a complex"),
        vec![witness],
    )
    .expect("witnessed source builds");
    let mut target_complex = transport
        .forward(&source)
        .expect("forward transport builds");
    target_complex.terms[0].indices[0] = 1 - target_complex.terms[0].indices[0];
    assert!(!target_complex.verify());

    let mut changed = transport;
    changed.canonical_projectives[0] = Module::zero(changed.target.target());
    assert!(!changed.verify());
}
