use super::*;
use crate::algebra::{an_with_relations, linear_an};
use crate::ext::ExtSpace;
use crate::family::{CompiledModuleFamily, FamilyFixedEntry, FamilyParameter};
use crate::field::PrimeField;
use crate::homspace::HomSpace;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::ArrowId;

fn field() -> PrimeField {
    PrimeField::new(5).unwrap()
}

#[test]
fn a3_hom_is_the_equalizer_of_its_two_edge_pieces() {
    let algebra = linear_an(3, field());
    let partition = InterfacePartition::new(&algebra, &[0], &[1], &[2]).unwrap();
    let module = Module::projective(&algebra, 0);
    let plan =
        InterfaceHomPlan::compile(&partition, module.dim_vector(), module.dim_vector()).unwrap();
    let result = plan.compute(&module, &module).unwrap();
    assert_eq!(result.dim(), 1);
    assert_eq!(result.work().interface_coordinates, 1);
    assert!(result.verify());
}

#[test]
fn an_arrow_between_the_two_interiors_rejects_the_partition() {
    let algebra = linear_an(2, field());
    assert!(matches!(
        InterfacePartition::new(&algebra, &[0], &[], &[1]),
        Err(InterfaceHomError::CrossingArrow { arrow: ArrowId(0) })
    ));
}

#[test]
fn a_relation_through_both_interiors_rejects_the_partition() {
    let algebra = an_with_relations(3, &[(0, 2)], field()).unwrap();
    assert!(matches!(
        InterfacePartition::new(&algebra, &[0], &[1], &[2]),
        Err(InterfaceHomError::CrossingRelation { .. })
    ));
}

#[test]
fn the_plan_rejects_changed_dimensions_and_algebra_identity() {
    let algebra = linear_an(3, field());
    let partition = InterfacePartition::new(&algebra, &[0], &[1], &[2]).unwrap();
    let plan = InterfaceHomPlan::compile(&partition, &[1, 1, 1], &[1, 1, 1]).unwrap();
    let changed = Module::simple(&algebra, 0);
    assert!(matches!(
        plan.compute(&changed, &changed),
        Err(InterfaceHomError::DimensionVectorMismatch { .. })
    ));

    let other = linear_an(3, field());
    let module = Module::projective(&other, 0);
    assert!(matches!(
        plan.compute(&module, &module),
        Err(InterfaceHomError::DifferentAlgebra { .. })
    ));
}

#[test]
fn every_vertex_must_occur_once() {
    let algebra = linear_an(3, field());
    assert!(matches!(
        InterfacePartition::new(&algebra, &[0], &[1], &[]),
        Err(InterfaceHomError::MissingVertex { vertex: 2 })
    ));
    assert!(matches!(
        InterfacePartition::new(&algebra, &[0, 1], &[1], &[2]),
        Err(InterfaceHomError::DuplicateVertex { vertex: 1, .. })
    ));
}

fn linear_a4_family(field: PrimeField) -> (CompiledModuleFamily, InterfacePartition) {
    let algebra = linear_an(4, field);
    let family = CompiledModuleFamily::new(
        &algebra,
        vec![1, 1, 1, 1],
        vec![
            FamilyFixedEntry::new(ArrowId(0), 0, 0, field.one()),
            FamilyFixedEntry::new(ArrowId(2), 0, 0, field.one()),
        ],
        vec![FamilyParameter::new("middle", ArrowId(1), 0, 0)],
    )
    .unwrap();
    let partition = InterfacePartition::new(&algebra, &[0], &[1, 2], &[3]).unwrap();
    (family, partition)
}

fn same_hom_basis(left: &HomSpace, right: &HomSpace) -> bool {
    left.dim() == right.dim()
        && left
            .basis_iter()
            .zip(right.basis_iter())
            .all(|(left, right)| {
                (0..left.source().algebra().quiver().num_vertices())
                    .all(|vertex| left.map_at(vertex) == right.map_at(vertex))
            })
}

#[test]
fn fixed_outer_hom_kernel_matches_generic_over_gf2_and_gf5() {
    for modulus in [2, 5] {
        let field = PrimeField::new(modulus).unwrap();
        let (family, partition) = linear_a4_family(field);
        let plan = InterfaceFamilyHomPlan::compile(&family, &partition, &[field.zero()]).unwrap();
        assert_eq!(plan.internal_arrows(), &[ArrowId(1)]);
        assert_eq!(plan.fixed_equations(), 2);
        assert_eq!(plan.fixed_rank(), 2);
        assert_eq!(plan.fixed_kernel_dimension(), 2);
        assert_eq!(plan.interface_variables(), &[1, 2]);
        assert_eq!(plan.interface_kernel_columns().cols(), 2);
        assert!(plan.verify());
        for source in 0..modulus {
            for target in 0..modulus {
                let source_value = field.elem(source as i64);
                let target_value = field.elem(target as i64);
                let specialized = plan.compute(&[source_value], &[target_value]).unwrap();
                let generic = family
                    .hom_space_generic(&[source_value], &[target_value])
                    .unwrap();
                assert!(specialized.verify());
                assert!(same_hom_basis(specialized.space(), &generic));
                assert_eq!(specialized.work().fixed_equations, 2);
                assert_eq!(specialized.work().fixed_kernel_dimension, 2);
                assert_eq!(specialized.work().interface_variables, 2);
                let active = usize::from(!source_value.is_zero() || !target_value.is_zero());
                assert_eq!(specialized.work().interface_equations, active);
                assert_eq!(specialized.work().interface_rank, active);
                assert_eq!(specialized.dim(), generic.dim());
            }
        }
    }
}

#[test]
fn hereditary_plan_reuses_the_reduced_rank_for_ext1() {
    for modulus in [2, 5] {
        let field = PrimeField::new(modulus).unwrap();
        let (family, partition) = linear_a4_family(field);
        let plan =
            InterfaceFamilyHereditaryPlan::compile(&family, &partition, &[field.zero()]).unwrap();
        assert!(plan.verify());
        assert_eq!(plan.arrow_cochains(), 3);
        for source in 0..modulus {
            for target in 0..modulus {
                let source_value = field.elem(source as i64);
                let target_value = field.elem(target as i64);
                let pair = plan.compute(&[source_value], &[target_value]).unwrap();
                let generic_source = family.specialize_generic(&[source_value]).unwrap();
                let generic_target = family.specialize_generic(&[target_value]).unwrap();
                let ext1 = ExtSpace::new(&generic_source, &generic_target, 1).unwrap();
                assert_eq!(pair.ext_dimension(0), pair.hom_dimension());
                assert_eq!(pair.ext_dimension(1), ext1.dim());
                assert_eq!(pair.ext_dimension(2), 0);
                assert_eq!(pair.work().arrow_cochains, 3);
                assert_eq!(
                    pair.work().constraint_rank,
                    pair.work().hom.fixed_rank + pair.work().hom.interface_rank
                );
                assert!(pair.verify());
            }
        }
    }
}

#[test]
fn hereditary_plan_rejects_a_nonzero_relation_ideal() {
    let field = field();
    let algebra = crate::algebra::dual_numbers(field);
    let family = CompiledModuleFamily::new(
        &algebra,
        vec![1],
        Vec::new(),
        vec![FamilyParameter::new("x", ArrowId(0), 0, 0)],
    )
    .unwrap();
    let partition = InterfacePartition::new(&algebra, &[], &[0], &[]).unwrap();
    assert!(matches!(
        InterfaceFamilyHereditaryPlan::compile(&family, &partition, &[field.zero()]),
        Err(InterfaceFamilyHereditaryError::NonzeroIdeal { .. })
    ));
}

#[test]
fn interface_family_rejects_outer_parameters_and_other_algebras() {
    let field = field();
    let algebra = linear_an(4, field);
    let outside = CompiledModuleFamily::new(
        &algebra,
        vec![1, 1, 1, 1],
        Vec::new(),
        vec![FamilyParameter::new("outer", ArrowId(0), 0, 0)],
    )
    .unwrap();
    let partition = InterfacePartition::new(&algebra, &[0], &[1, 2], &[3]).unwrap();
    assert!(matches!(
        InterfaceFamilyHomPlan::compile(&outside, &partition, &[field.zero()]),
        Err(InterfaceFamilyHomError::ParameterOutsideInterface {
            index: 0,
            arrow: ArrowId(0),
            ..
        })
    ));

    let other = linear_an(4, field);
    let other_partition = InterfacePartition::new(&other, &[0], &[1, 2], &[3]).unwrap();
    let (family, _) = linear_a4_family(field);
    assert!(matches!(
        InterfaceFamilyHomPlan::compile(&family, &other_partition, &[field.zero()]),
        Err(InterfaceFamilyHomError::DifferentAlgebra)
    ));
}

#[test]
fn interface_family_rejects_invalid_anchor_fiber_and_module_endpoints() {
    let f = field();
    let algebra = crate::algebra::dual_numbers(f);
    let family = CompiledModuleFamily::new(
        &algebra,
        vec![1],
        Vec::new(),
        vec![FamilyParameter::new("x", ArrowId(0), 0, 0)],
    )
    .unwrap();
    let partition = InterfacePartition::new(&algebra, &[], &[0], &[]).unwrap();
    assert!(matches!(
        InterfaceFamilyHomPlan::compile(&family, &partition, &[f.one()]),
        Err(InterfaceFamilyHomError::InvalidAnchor(
            crate::family::FamilyError::Module(_)
        ))
    ));
    let plan = InterfaceFamilyHomPlan::compile(&family, &partition, &[f.zero()]).unwrap();
    assert!(matches!(
        plan.compute(&[f.zero()], &[f.one()]),
        Err(InterfaceFamilyHomError::InvalidTarget(
            crate::family::FamilyError::Module(_)
        ))
    ));

    let (family, partition) = linear_a4_family(f);
    let plan = InterfaceFamilyHomPlan::compile(&family, &partition, &[f.zero()]).unwrap();
    let other = linear_an(4, f);
    let other_family = CompiledModuleFamily::new(
        &other,
        vec![1, 1, 1, 1],
        vec![
            FamilyFixedEntry::new(ArrowId(0), 0, 0, f.one()),
            FamilyFixedEntry::new(ArrowId(2), 0, 0, f.one()),
        ],
        vec![FamilyParameter::new("middle", ArrowId(1), 0, 0)],
    )
    .unwrap();
    let foreign = other_family.specialize(&[f.zero()]).unwrap();
    let local = family.specialize(&[f.zero()]).unwrap();
    assert!(matches!(
        plan.compute_modules(&foreign, &local),
        Err(InterfaceFamilyHomError::SourceAlgebraMismatch)
    ));

    let mut maps = local
        .algebra()
        .quiver()
        .arrows()
        .iter()
        .map(|&(source, target)| DenseMat::zero(local.dim_at(source), local.dim_at(target)))
        .collect::<Vec<_>>();
    maps[0].set(0, 0, f.zero());
    let changed = Module::new(local.algebra().clone(), vec![1, 1, 1, 1], maps).unwrap();
    assert!(matches!(
        plan.compute_modules(&changed, &local),
        Err(InterfaceFamilyHomError::SourceOutsideFamily {
            arrow: ArrowId(0),
            row: 0,
            column: 0,
        })
    ));
}
