use super::*;
use crate::algebra::{commutative_square, dual_numbers, linear_an};
use crate::field::PrimeField;
use crate::module::ModuleError;
use crate::quiver::ArrowId;

fn field() -> PrimeField {
    PrimeField::new(5).unwrap()
}

#[test]
fn layout_is_arrow_major_and_parameter_indices_are_stable() {
    let f = field();
    let algebra = linear_an(2, f);
    let family = CompiledModuleFamily::new(
        &algebra,
        vec![1, 1],
        Vec::new(),
        vec![FamilyParameter::new("lambda", ArrowId(0), 0, 0)],
    )
    .unwrap();
    assert_eq!(family.layout().coordinate_count(), 1);
    assert_eq!(family.parameter_index("lambda"), Some(0));
    assert_eq!(family.parameters()[0].coordinate().index(), 0);
    let module = family.specialize(&[f.elem(3)]).unwrap();
    assert_eq!(module.map(ArrowId(0)).entries_u64(), vec![vec![3]]);
    assert!(family.verify());
}

#[test]
fn fixed_and_parameter_coordinates_cannot_overlap() {
    let f = field();
    let algebra = linear_an(2, f);
    let error = CompiledModuleFamily::new(
        &algebra,
        vec![1, 1],
        vec![FamilyFixedEntry::new(ArrowId(0), 0, 0, f.one())],
        vec![FamilyParameter::new("lambda", ArrowId(0), 0, 0)],
    )
    .unwrap_err();
    assert!(matches!(error, FamilyError::FixedParameterCollision { .. }));
}

#[test]
fn relation_layout_lists_path_factors_without_evaluating_a_fiber() {
    let f = field();
    let algebra = dual_numbers(f);
    let family = CompiledModuleFamily::new(&algebra, vec![1], Vec::new(), Vec::new()).unwrap();
    let relation = &family.relation_evaluations()[0];
    assert_eq!(relation.terms().len(), 1);
    assert_eq!(relation.terms()[0].path(), &[ArrowId(0), ArrowId(0)]);
    assert_eq!(relation.terms()[0].factors().len(), 2);
    assert_eq!(relation.coordinate_support().len(), 1);
}

#[test]
fn hom_layout_has_both_commuting_square_sides() {
    let f = field();
    let algebra = linear_an(2, f);
    let family = CompiledModuleFamily::new(&algebra, vec![1, 1], Vec::new(), Vec::new()).unwrap();
    let equation = &family.hom_equations()[0];
    assert_eq!(equation.terms().len(), 2);
    assert_eq!(equation.terms()[0].side(), HomCoefficientSide::Target);
    assert_eq!(equation.terms()[0].sign(), 1);
    assert_eq!(equation.terms()[1].side(), HomCoefficientSide::Source);
    assert_eq!(equation.terms()[1].sign(), -1);
    assert_eq!(family.layout().hom_variable_count(), 2);
}

#[test]
fn specialization_rejects_a_nonzero_compiled_relation() {
    let f = field();
    let algebra = dual_numbers(f);
    let family = CompiledModuleFamily::new(
        &algebra,
        vec![1],
        Vec::new(),
        vec![FamilyParameter::new("x", ArrowId(0), 0, 0)],
    )
    .unwrap();
    assert!(family.specialize(&[f.zero()]).is_ok());
    assert!(matches!(
        family.specialize(&[f.one()]),
        Err(FamilyError::Module(ModuleError::RelationActsNonzero {
            index: 0
        }))
    ));
}

#[test]
fn compiled_and_generic_specialization_agree_on_every_scalar_fiber() {
    let f = field();
    let algebra = dual_numbers(f);
    let family = CompiledModuleFamily::new(
        &algebra,
        vec![1],
        Vec::new(),
        vec![FamilyParameter::new("x", ArrowId(0), 0, 0)],
    )
    .unwrap();
    for value in 0..f.modulus() {
        let value = f.elem(value as i64);
        let compiled = family.specialize(&[value]);
        let generic = family.specialize_generic(&[value]);
        assert_eq!(compiled.is_ok(), generic.is_ok());
        if let (Ok(compiled), Ok(generic)) = (compiled, generic) {
            assert_eq!(compiled.dim_vector(), generic.dim_vector());
            assert_eq!(compiled.map(ArrowId(0)), generic.map(ArrowId(0)));
        }
    }
}

#[test]
fn compiled_and_generic_specialization_agree_on_a_two_term_relation() {
    let f = PrimeField::new(2).unwrap();
    let algebra = commutative_square(f);
    let parameters = (0..algebra.quiver().num_arrows())
        .map(|arrow| FamilyParameter::new(format!("x{arrow}"), ArrowId(arrow as u32), 0, 0))
        .collect();
    let family =
        CompiledModuleFamily::new(&algebra, vec![1, 1, 1, 1], Vec::new(), parameters).unwrap();
    for bits in 0..16u64 {
        let values: Vec<_> = (0..4)
            .map(|shift| f.elem(((bits >> shift) & 1) as i64))
            .collect();
        let compiled = family.specialize(&values);
        let generic = family.specialize_generic(&values);
        assert_eq!(compiled.is_ok(), generic.is_ok());
        if let (Ok(compiled), Ok(generic)) = (compiled, generic) {
            assert!(crate::module::same_representation(&compiled, &generic));
        }
    }
}

fn hom_bases_agree(left: &crate::homspace::HomSpace, right: &crate::homspace::HomSpace) -> bool {
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
fn compiled_hom_basis_matches_the_generic_basis_on_every_valid_pair() {
    let f = PrimeField::new(2).unwrap();
    let algebra = commutative_square(f);
    let parameters = (0..algebra.quiver().num_arrows())
        .map(|arrow| FamilyParameter::new(format!("x{arrow}"), ArrowId(arrow as u32), 0, 0))
        .collect();
    let family =
        CompiledModuleFamily::new(&algebra, vec![1, 1, 1, 1], Vec::new(), parameters).unwrap();
    let valid: Vec<Vec<_>> = (0..16u64)
        .filter_map(|bits| {
            let values: Vec<_> = (0..4)
                .map(|shift| f.elem(((bits >> shift) & 1) as i64))
                .collect();
            family.specialize(&values).is_ok().then_some(values)
        })
        .collect();
    for source in &valid {
        for target in &valid {
            let compiled = family.hom_space(source, target).unwrap();
            let generic = family.hom_space_generic(source, target).unwrap();
            assert!(hom_bases_agree(&compiled, &generic));
        }
    }
}
