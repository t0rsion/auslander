use crate::hom::{HomError, Morphism, zero_morphism};
use crate::homotopy::{BoundedComplex, ChainMap};
use crate::homspace::scale_morphism;
use crate::module::Module;

use super::budget::ReplacementWork;
use super::cover::ComplexProjectiveCover;
use super::replacement::{PerfectReplacement, ReplacementError};
use super::work::{checked_sum, checked_sum_results, replacement_work_for};

struct TotalTerm {
    module: Module,
    parts: Vec<(usize, i32)>,
    inclusions: Vec<Morphism>,
    projections: Vec<Morphism>,
}

fn total_range(
    original: &BoundedComplex,
    cover_count: usize,
) -> Result<(i32, i32), ReplacementError> {
    let shift = cover_count
        .checked_sub(1)
        .ok_or(ReplacementError::Arithmetic)?;
    let shift = i32::try_from(shift).map_err(|_| ReplacementError::DegreeOverflow)?;
    let upper = original
        .upper()
        .checked_add(shift)
        .ok_or(ReplacementError::DegreeOverflow)?;
    Ok((original.lower(), upper))
}

fn total_parts(
    covers: &[ComplexProjectiveCover],
    degree: i32,
) -> impl Iterator<Item = (usize, i32, &Module)> + '_ {
    covers
        .iter()
        .enumerate()
        .filter_map(move |(resolution, cover)| {
            let internal = degree - resolution as i32;
            let complex = cover.projective().complex();
            complex.range().contains(internal).then(|| {
                (
                    resolution,
                    internal,
                    complex
                        .term(internal)
                        .expect("the checked range contains the degree"),
                )
            })
        })
}

fn total_degree_dimensions(
    covers: &[ComplexProjectiveCover],
    original: &BoundedComplex,
    lower: i32,
    upper: i32,
    complex_terms: usize,
) -> Result<Vec<Vec<usize>>, ReplacementError> {
    let mut degree_dims = Vec::with_capacity(complex_terms);
    for degree in lower..=upper {
        let mut dims = vec![0usize; original.terms()[0].algebra().quiver().num_vertices() as usize];
        for (_, _, term) in total_parts(covers, degree) {
            for (sum, &value) in dims.iter_mut().zip(term.dim_vector()) {
                *sum = checked_sum([*sum, value])?;
            }
        }
        degree_dims.push(dims);
    }
    Ok(degree_dims)
}

fn matrix_entry_count(left: &[usize], right: &[usize]) -> Result<usize, ReplacementError> {
    checked_sum_results(left.iter().zip(right).map(|(&source, &target)| {
        source
            .checked_mul(target)
            .ok_or(ReplacementError::Arithmetic)
    }))
}

fn differential_entry_count(degree_dims: &[Vec<usize>]) -> Result<usize, ReplacementError> {
    degree_dims.windows(2).try_fold(0usize, |total, pair| {
        let entries = matrix_entry_count(&pair[1], &pair[0])?;
        checked_sum([total, entries])
    })
}

fn augmentation_entry_count(
    degree_dims: &[Vec<usize>],
    target: &BoundedComplex,
) -> Result<usize, ReplacementError> {
    checked_sum_results(
        degree_dims
            .iter()
            .zip(target.terms())
            .map(|(source, target)| matrix_entry_count(source, target.dim_vector())),
    )
}

fn totalization_cost(
    covers: &[ComplexProjectiveCover],
    original: &BoundedComplex,
) -> Result<ReplacementWork, ReplacementError> {
    let (lower, upper) = total_range(original, covers.len())?;
    let complex_terms = (upper as i64 - lower as i64 + 1) as usize;
    let total_dimension = checked_sum(
        covers
            .iter()
            .flat_map(|cover| cover.projective().complex().terms())
            .map(Module::total_dim),
    )?;
    let matrix_entries = (|| {
        let degree_dims = total_degree_dimensions(covers, original, lower, upper, complex_terms)?;
        let differential_entries = differential_entry_count(&degree_dims)?;
        let target = padded_target(original, lower, upper)?;
        let augmentation_entries = augmentation_entry_count(&degree_dims, &target)?;
        checked_sum([differential_entries, augmentation_entries])
    })()?;
    replacement_work_for(complex_terms, total_dimension, matrix_entries)
}

fn total_terms(
    original: &BoundedComplex,
    covers: &[ComplexProjectiveCover],
    lower: i32,
    upper: i32,
) -> Vec<TotalTerm> {
    (lower..=upper)
        .map(|degree| {
            let (parts, modules): (Vec<_>, Vec<_>) = total_parts(covers, degree)
                .map(|(resolution, internal, term)| ((resolution, internal), term.clone()))
                .unzip();
            let (module, inclusions, projections) =
                crate::decompose::direct_sum_or_zero(original.terms()[0].algebra(), modules.iter());
            TotalTerm {
                module,
                parts,
                inclusions,
                projections,
            }
        })
        .collect()
}

fn vertical_piece(
    source: &TotalTerm,
    target: &TotalTerm,
    covers: &[ComplexProjectiveCover],
    source_slot: usize,
    resolution: usize,
    internal: i32,
) -> Option<Morphism> {
    covers[resolution]
        .projective()
        .complex()
        .differential(internal)
        .and_then(|map| {
            target
                .parts
                .iter()
                .position(|&part| part == (resolution, internal - 1))
                .map(|target_slot| {
                    source.projections[source_slot]
                        .then(map)
                        .and_then(|value| value.then(&target.inclusions[target_slot]))
                        .expect("total vertical blocks have matching endpoints")
                })
        })
}

fn horizontal_piece(
    source: &TotalTerm,
    target: &TotalTerm,
    horizontal: &[ChainMap],
    source_slot: usize,
    resolution: usize,
    internal: i32,
) -> Option<Morphism> {
    (resolution > 0).then(|| {
        let target_slot = target
            .parts
            .iter()
            .position(|&part| part == (resolution - 1, internal))
            .expect("a horizontal block lowers total degree by one");
        let mut map = horizontal[resolution - 1]
            .component(internal)
            .expect("horizontal maps use the fixed input range")
            .clone();
        if internal.rem_euclid(2) == 1 {
            let field = map.source().field();
            map = scale_morphism(&map, field.neg(field.one()));
        }
        source.projections[source_slot]
            .then(&map)
            .and_then(|value| value.then(&target.inclusions[target_slot]))
            .expect("total horizontal blocks have matching endpoints")
    })
}

fn sum_morphisms(
    source: &Module,
    target: &Module,
    terms: impl IntoIterator<Item = Morphism>,
) -> Result<Morphism, HomError> {
    Ok(terms
        .into_iter()
        .fold(zero_morphism(source, target)?, |sum, term| {
            crate::decompose::add_morphisms(&sum, &term)
        }))
}

fn total_differential(
    source: &TotalTerm,
    target: &TotalTerm,
    covers: &[ComplexProjectiveCover],
    horizontal: &[ChainMap],
) -> Result<Morphism, HomError> {
    let pieces =
        source
            .parts
            .iter()
            .enumerate()
            .flat_map(|(source_slot, &(resolution, internal))| {
                vertical_piece(source, target, covers, source_slot, resolution, internal)
                    .into_iter()
                    .chain(horizontal_piece(
                        source,
                        target,
                        horizontal,
                        source_slot,
                        resolution,
                        internal,
                    ))
            });
    sum_morphisms(&source.module, &target.module, pieces)
}

fn augmentation_components(
    total_terms: &[TotalTerm],
    target: &BoundedComplex,
    covers: &[ComplexProjectiveCover],
) -> Result<Vec<Morphism>, HomError> {
    total_terms
        .iter()
        .zip(target.terms())
        .map(|(source, target)| {
            let pieces = source.parts.iter().enumerate().filter_map(|(slot, part)| {
                let (resolution, internal) = *part;
                (resolution == 0).then(|| {
                    source.projections[slot]
                        .then(
                            covers[0]
                                .augmentation()
                                .component(internal)
                                .expect("the first augmentation uses the input range"),
                        )
                        .expect("the first total summand belongs to the first cover")
                })
            });
            sum_morphisms(&source.module, target, pieces)
        })
        .collect()
}

fn horizontal_maps(covers: &[ComplexProjectiveCover]) -> Result<Vec<ChainMap>, ReplacementError> {
    (1..covers.len())
        .map(|resolution| {
            covers[resolution]
                .augmentation()
                .then(covers[resolution - 1].kernel_inclusion())
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(ReplacementError::from)
}

fn padded_target(
    original: &BoundedComplex,
    lower: i32,
    upper: i32,
) -> Result<BoundedComplex, ReplacementError> {
    let range = crate::homotopy::DegreeRange::new(lower, upper)
        .map_err(|_| ReplacementError::DegreeOverflow)?;
    original.padded_to(range).map_err(ReplacementError::from)
}

pub(super) fn totalize_replacement(
    original: &BoundedComplex,
    covers: &[ComplexProjectiveCover],
) -> Result<PerfectReplacement, ReplacementError> {
    let (lower, upper, horizontal) =
        total_range(original, covers.len()).and_then(|(lower, upper)| {
            horizontal_maps(covers).map(|horizontal| (lower, upper, horizontal))
        })?;
    let terms = total_terms(original, covers, lower, upper);
    let (total, target, components) = (|| -> Result<_, ReplacementError> {
        let differentials = terms
            .windows(2)
            .map(|pair| total_differential(&pair[1], &pair[0], covers, &horizontal))
            .collect::<Result<Vec<_>, _>>()?;
        let total = BoundedComplex::new(
            lower,
            terms.iter().map(|term| term.module.clone()).collect(),
            differentials,
        )?;
        let target = padded_target(original, lower, upper)?;
        let components = augmentation_components(&terms, &target, covers)?;
        Ok((total, target, components))
    })()?;
    let quasi_isomorphism = ChainMap::new(&total, &target, components)
        .map_err(ReplacementError::from)
        .and_then(|augmentation| {
            super::quasi::QuasiIsomorphism::new(augmentation).map_err(ReplacementError::from)
        })?;
    let replacement = super::term::ProjectiveComplex::new(total)
        .map_err(ReplacementError::from)
        .and_then(|projective| {
            PerfectReplacement::new(original.clone(), projective, quasi_isomorphism)
                .map_err(ReplacementError::from)
        })?;
    debug_assert!(replacement.verify());
    Ok(replacement)
}

pub(super) fn replacement_cost(
    covers: &[ComplexProjectiveCover],
    original: &BoundedComplex,
) -> Result<ReplacementWork, ReplacementError> {
    totalization_cost(covers, original)
}
