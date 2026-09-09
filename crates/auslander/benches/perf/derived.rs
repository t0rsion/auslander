use std::hint::black_box;

use auslander::algebra::{an_with_relations, linear_an};
use auslander::basic::{AddClosureWitness, BasicDecomposition};
use auslander::complex_target::{ComplexTargetOutcome, present_complex_target};
use auslander::control::ComputationControl;
use auslander::derived::{AddTComplex, DerivedEquivalenceCertificate};
use auslander::derived_artifact::{ArtifactVerifyLimits, DerivedArtifact, verify_derived_artifact};
use auslander::derived_hom::{DerivedHomLimits, derived_hom};
use auslander::equivalence_discovery::{DiscoveryLimits, discover_equivalences};
use auslander::equivalence_edge::{DerivedEquivalenceEdge, DerivedEquivalenceEdgeOutcome};
use auslander::homotopy::BoundedComplex;
use auslander::module::{Module, direct_sum};
use auslander::perfect::{ReplacementLimits, replace_perfect};
use auslander::target::{TargetLimits, present_target};
use auslander::tilting_complex::{
    TiltingComplexLimits, TiltingComplexResult, TiltingMutationOutcome, left_tilting_mutation,
    regular_tilting_complex,
};

use super::perf_support::{Runner, f2, f5};
use super::perf_target::target_tilting;

pub(crate) fn derived_case(r: &mut Runner, name: &str, module: &Module) {
    r.case(
        "derived",
        &format!("end-to-end certificate {name}"),
        1,
        || {
            let tilting = target_tilting(module);
            let target = present_target(&tilting, &TargetLimits::default())
                .expect("target recovery succeeds")
                .presented()
                .expect("the target is split")
                .clone();
            black_box(
                DerivedEquivalenceCertificate::new(tilting, target)
                    .expect("the tilting certificate completes"),
            );
        },
    );

    let tilting = target_tilting(module);
    let target = present_target(&tilting, &TargetLimits::default())
        .expect("target recovery succeeds")
        .presented()
        .expect("the target is split")
        .clone();
    let certificate = DerivedEquivalenceCertificate::new(tilting, target)
        .expect("the tilting certificate completes");
    r.case("derived", &format!("verify certificate {name}"), 1, || {
        assert!(
            black_box(certificate.verify()),
            "derived certificate verification failed"
        );
    });

    let basic = BasicDecomposition::new(module).expect("the tilting module is basic");
    let witness = AddClosureWitness::from_module(module, &basic)
        .expect("membership decomposes")
        .expect("T belongs to add(T)");
    let source = AddTComplex::new(
        BoundedComplex::new(0, vec![module.clone()], Vec::new()).expect("one term is a complex"),
        vec![witness],
    )
    .expect("the source term has an add(T) witness");
    let transported = certificate
        .transport()
        .forward(&source)
        .expect("forward transport succeeds");
    r.case("derived", &format!("forward one-term {name}"), 1, || {
        black_box(
            certificate
                .transport()
                .forward(&source)
                .expect("forward transport succeeds"),
        );
    });
    r.case("derived", &format!("reverse one-term {name}"), 1, || {
        black_box(
            certificate
                .transport()
                .reverse(&transported)
                .expect("reverse transport succeeds"),
        );
    });
}

pub(crate) fn derived_layer(r: &mut Runner) {
    for (field_name, field) in [("f2", f2()), ("f5", f5())] {
        let algebra = an_with_relations(3, &[(0, 2)], field).expect("the zero path is admissible");
        let injectives: Vec<Module> = (0..3)
            .map(|vertex| Module::injective(&algebra, vertex))
            .collect();
        let module = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
        derived_case(r, &format!("pd2-dual-{field_name}"), &module);
    }
}

pub(crate) fn derived_workbench(r: &mut Runner) {
    let algebra = an_with_relations(3, &[(0, 2)], f5()).expect("the zero path is admissible");
    let source = BoundedComplex::new(0, vec![Module::simple(&algebra, 0)], Vec::new())
        .expect("one term is a complex");
    let target = BoundedComplex::new(0, vec![Module::simple(&algebra, 2)], Vec::new())
        .expect("one term is a complex");
    r.case("workbench", "replace_perfect pd2-simple-f5", 1, || {
        black_box(
            replace_perfect(&source, ReplacementLimits::default(), None)
                .expect("replacement succeeds"),
        );
    });
    r.case("workbench", "derived_hom pd2-simple-f5", 1, || {
        black_box(
            derived_hom(&source, &target, DerivedHomLimits::default(), None)
                .expect("derived Hom succeeds"),
        );
    });

    let mutation_algebra = linear_an(2, f5());
    let limits = DiscoveryLimits {
        max_vertices: 3,
        ..DiscoveryLimits::default()
    };
    r.case("workbench", "discover_equivalences a2-f5", 1, || {
        black_box(
            discover_equivalences(&mutation_algebra, limits, &ComputationControl::new())
                .expect("discovery succeeds"),
        );
    });
    let TiltingComplexResult::Tilting(regular) =
        regular_tilting_complex(&mutation_algebra, TiltingComplexLimits::default())
            .expect("regular classification succeeds")
    else {
        panic!("the regular generator certifies")
    };
    let mutation = (0..regular.candidate().len())
        .find_map(|summand| {
            match left_tilting_mutation(&regular, summand, TiltingComplexLimits::default())
                .expect("left mutation succeeds")
            {
                TiltingMutationOutcome::Tilting(value)
                    if value
                        .candidate()
                        .summands()
                        .iter()
                        .any(|part| part.complex().len() > 1) =>
                {
                    Some(*value)
                }
                _ => None,
            }
        })
        .expect("A2 has a multi-degree mutation");
    r.case("workbench", "present_complex_target a2-f5", 1, || {
        assert!(matches!(
            black_box(present_complex_target(&mutation, &TargetLimits::default())),
            Ok(ComplexTargetOutcome::Presented(_))
        ));
    });
    let edge = match DerivedEquivalenceEdge::recover(mutation, &TargetLimits::default())
        .expect("target recovery succeeds")
    {
        DerivedEquivalenceEdgeOutcome::Certified(value) => value,
        DerivedEquivalenceEdgeOutcome::Cut(_) => panic!("the A2 target completes"),
    };
    let artifact = DerivedArtifact::from_edge(&edge)
        .expect("the edge exports")
        .to_canonical_json();
    r.case("workbench", "verify artifact a2-f5", 1, || {
        black_box(
            verify_derived_artifact(
                &artifact,
                ArtifactVerifyLimits::default(),
                &ComputationControl::new(),
            )
            .expect("artifact verification succeeds"),
        );
    });
}
