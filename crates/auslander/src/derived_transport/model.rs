use crate::approx::left_approximation;
use crate::basic::{AddClosureWitness, BasicDecomposition};
use crate::complex::{CheckedComplex, ExactnessOutcome};
use crate::derived::AddTComplex;
use crate::hom::{Morphism, cokernel, kernel, zero_morphism};
use crate::homotopy::{BoundedComplex, ChainMap, DegreeRange};
use crate::module::Module;
use crate::perfect::{ProjectiveComplex, QuasiIsomorphism};
use crate::tilting::ClassicalTiltingModule;

use super::DerivedTransportError;
use super::comparison::{
    agrees_after_padding, attachment_map, common_range, cone_chain_map, strict_comparison,
    structural_chain_isomorphism,
};

/// A projective complex and its checked model in `K^b(add(T))`.
#[derive(Clone)]
pub struct ProjectiveAddTModel {
    original: BoundedComplex,
    model: AddTComplex,
    quasi_isomorphism: QuasiIsomorphism,
}

impl ProjectiveAddTModel {
    accessor_methods! {
        /// The bounded projective input.
        pub original() -> &BoundedComplex = |this| &this.original;
        /// The checked `add(T)` model.
        pub model() -> &AddTComplex = |this| &this.model;
        /// The checked map from the projective input to its model.
        pub quasi_isomorphism() -> &QuasiIsomorphism = |this| &this.quasi_isomorphism;
    }

    /// Rechecks the model, map, and exact cone.
    pub fn verify(&self) -> bool {
        self.original.verify()
            && self.model.verify()
            && self.quasi_isomorphism.verify()
            && agrees_after_padding(self.quasi_isomorphism.map().source(), &self.original)
            && agrees_after_padding(self.quasi_isomorphism.map().target(), self.model.complex())
    }
}

fn add_t_witnesses(
    complex: &BoundedComplex,
    basic: &BasicDecomposition,
) -> Result<Vec<AddClosureWitness>, DerivedTransportError> {
    complex
        .terms()
        .iter()
        .enumerate()
        .map(|(term, module)| {
            AddClosureWitness::from_module(module, basic)
                .map_err(|error| DerivedTransportError::Coresolution {
                    reason: format!("term {term} decomposition failed: {error}"),
                })?
                .ok_or_else(|| DerivedTransportError::Coresolution {
                    reason: format!("term {term} lies outside add(T)"),
                })
        })
        .collect()
}

fn projective_step(
    current: &Module,
    summands: &[Module],
    basic: &BasicDecomposition,
    previous_projection: &mut Option<Morphism>,
    stage: usize,
) -> Result<(Module, Morphism, AddClosureWitness, Module, Morphism), DerivedTransportError> {
    let approximation = left_approximation(current, summands).map_err(|error| {
        DerivedTransportError::Coresolution {
            reason: format!("stage {stage} approximation failed: {error}"),
        }
    })?;
    if !kernel(approximation.map()).0.is_zero() {
        return Err(DerivedTransportError::Coresolution {
            reason: format!("stage {stage} approximation is not monic"),
        });
    }
    let target = approximation.map().target().clone();
    let witness = AddClosureWitness::from_module(&target, basic)
        .map_err(|error| DerivedTransportError::Coresolution {
            reason: format!("stage {stage} target decomposition failed: {error}"),
        })?
        .ok_or_else(|| DerivedTransportError::Coresolution {
            reason: format!("stage {stage} target lies outside add(T)"),
        })?;
    let displayed = match previous_projection.take() {
        Some(projection) => projection.then(approximation.map())?,
        None => approximation.map().clone(),
    };
    let (next, projection) = cokernel(approximation.map());
    Ok((target, displayed, witness, next, projection))
}

fn checked_projective_coresolution(
    display_terms: Vec<Module>,
    display_maps: Vec<Morphism>,
    stage: usize,
) -> Result<CheckedComplex, DerivedTransportError> {
    let checked = CheckedComplex::new(display_terms, display_maps).map_err(|error| {
        DerivedTransportError::Coresolution {
            reason: format!("stage {stage} exact complex failed: {error}"),
        }
    })?;
    if matches!(checked.exactness(), ExactnessOutcome::Exact(_)) {
        Ok(checked)
    } else {
        Err(DerivedTransportError::Coresolution {
            reason: format!("stage {stage} coresolution is not exact"),
        })
    }
}

fn finish_projective_module_model(
    module: &Module,
    degree: i32,
    display_terms: Vec<Module>,
    display_maps: Vec<Morphism>,
    witnesses: Vec<AddClosureWitness>,
    stage: usize,
) -> Result<ProjectiveAddTModel, DerivedTransportError> {
    let checked = checked_projective_coresolution(display_terms, display_maps, stage)?;
    let add_terms: Vec<Module> = checked.terms()[1..].iter().rev().cloned().collect();
    let add_maps: Vec<Morphism> = checked.maps()[1..].iter().rev().cloned().collect();
    let add_count =
        i32::try_from(add_terms.len()).map_err(|_| DerivedTransportError::DegreeOverflow)?;
    let base_lower = 1i32
        .checked_sub(add_count)
        .ok_or(DerivedTransportError::DegreeOverflow)?;
    let model = BoundedComplex::new(base_lower, add_terms, add_maps)?.shift(degree)?;
    let model = AddTComplex::new(model, witnesses.into_iter().rev().collect())?;
    let (original, map) = projective_model_map(module, degree, &checked, &model)?;
    let value = ProjectiveAddTModel {
        original,
        model,
        quasi_isomorphism: QuasiIsomorphism::new(map)?,
    };
    debug_assert!(value.verify());
    Ok(value)
}

fn projective_model_components(
    checked: &CheckedComplex,
    original_padded: &BoundedComplex,
    model: &BoundedComplex,
    module: &Module,
    degree: i32,
    range: DegreeRange,
) -> Result<Vec<Morphism>, DerivedTransportError> {
    (range.lower()..=range.upper())
        .map(|component_degree| {
            let index = (component_degree - range.lower()) as usize;
            if component_degree == degree {
                let first = &checked.maps()[0];
                let maps = (0..module.algebra().quiver().num_vertices())
                    .map(|vertex| first.map_at(vertex).clone())
                    .collect();
                Morphism::new(&original_padded.terms()[index], &model.terms()[index], maps)
                    .map_err(Into::into)
            } else {
                zero_morphism(&original_padded.terms()[index], &model.terms()[index])
                    .map_err(Into::into)
            }
        })
        .collect()
}

fn projective_model_map(
    module: &Module,
    degree: i32,
    checked: &CheckedComplex,
    model: &AddTComplex,
) -> Result<(BoundedComplex, ChainMap), DerivedTransportError> {
    let original = BoundedComplex::new(degree, vec![module.clone()], vec![])?;
    let range = common_range(&[&original, model.complex()])?;
    let original_padded = original.padded_to(range)?;
    let components = projective_model_components(
        checked,
        &original_padded,
        model.complex(),
        module,
        degree,
        range,
    )?;
    let map = ChainMap::new(&original_padded, model.complex(), components)?;
    Ok((original, map))
}

fn projective_module_model(
    module: &Module,
    degree: i32,
    tilting: &ClassicalTiltingModule,
    basic: &BasicDecomposition,
) -> Result<ProjectiveAddTModel, DerivedTransportError> {
    let summands: Vec<Module> = basic
        .summands()
        .iter()
        .map(|summand| summand.module().clone())
        .collect();
    let mut current = module.clone();
    let mut display_terms = vec![module.clone()];
    let mut display_maps = Vec::new();
    let mut witnesses = Vec::new();
    let mut previous_projection: Option<Morphism> = None;
    let max_steps = tilting.limits().max_generation_steps;
    for stage in 0..max_steps {
        let (target, displayed, witness, next, projection) =
            projective_step(&current, &summands, basic, &mut previous_projection, stage)?;
        display_terms.push(target);
        display_maps.push(displayed);
        witnesses.push(witness);
        if next.is_zero() {
            return finish_projective_module_model(
                module,
                degree,
                display_terms,
                display_maps,
                witnesses,
                stage,
            );
        }
        current = next;
        previous_projection = Some(projection);
    }
    Err(DerivedTransportError::Coresolution {
        reason: format!("step limit {max_steps} reached before the cokernel became zero"),
    })
}

fn extend_projective_model(
    input: &BoundedComplex,
    current: &ProjectiveAddTModel,
    degree: i32,
    tilting: &ClassicalTiltingModule,
    basic: &BasicDecomposition,
) -> Result<ProjectiveAddTModel, DerivedTransportError> {
    let source = projective_module_model(
        input.term(degree).expect("input range contains degree"),
        degree - 1,
        tilting,
        basic,
    )?;
    let original_map = attachment_map(
        source.quasi_isomorphism.map().source(),
        current.quasi_isomorphism.map().source(),
        input
            .differential(degree)
            .expect("each nonlowest term has a differential"),
        degree - 1,
    )?;
    let model_map = strict_comparison(&source, current, &original_map)?;
    let cone_map = cone_chain_map(
        &original_map,
        &model_map,
        source.quasi_isomorphism.map(),
        current.quasi_isomorphism.map(),
    )?;
    let original = original_map.mapping_cone()?;
    let model_complex = model_map.mapping_cone()?;
    let witnesses = add_t_witnesses(&model_complex, basic)?;
    let model =
        AddTComplex::new(model_complex, witnesses).map_err(DerivedTransportError::Strict)?;
    Ok(ProjectiveAddTModel {
        original,
        model,
        quasi_isomorphism: QuasiIsomorphism::new(cone_map)?,
    })
}

pub(super) fn model_projective_complex(
    projective: &ProjectiveComplex,
    tilting: &ClassicalTiltingModule,
) -> Result<ProjectiveAddTModel, DerivedTransportError> {
    let basic = BasicDecomposition::new(tilting.module()).map_err(|error| {
        DerivedTransportError::Coresolution {
            reason: format!("tilting decomposition failed: {error}"),
        }
    })?;
    let input = projective.complex();
    let mut current = projective_module_model(
        input.terms().first().expect("complex is nonempty"),
        input.lower(),
        tilting,
        &basic,
    )?;
    if input.lower() < input.upper() {
        let start = input
            .lower()
            .checked_add(1)
            .ok_or(DerivedTransportError::DegreeOverflow)?;
        for degree in start..=input.upper() {
            current = extend_projective_model(input, &current, degree, tilting, &basic)?;
        }
    }
    let comparison = structural_chain_isomorphism(input, &current.original)?;
    let final_map = comparison.then(current.quasi_isomorphism.map())?;
    let value = ProjectiveAddTModel {
        original: input.clone(),
        model: current.model,
        quasi_isomorphism: QuasiIsomorphism::new(final_map)?,
    };
    debug_assert!(value.verify());
    Ok(value)
}
