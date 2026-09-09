use super::certify::certify;
use super::error::{ApproxDefect, ApproxError};
use super::linear::{
    compose_into, composition_rows, radical_coordinates, row_relations, unit_factorizations,
};
use super::witness::MinimalLeftApproximation;
use crate::decompose::{add_morphisms, direct_sum_or_zero};
use crate::endo::EndoAlgebra;
use crate::field::{Fp, PrimeField, unit_vector};
use crate::hom::{Morphism, hom, zero_morphism};
use crate::homspace::HomSpace;
use crate::indec::IndecomposableModule;
use crate::linalg::{DenseMat, RowReducer};
use crate::module::Module;
use crate::profile::{Site, hit};

/// The minimal left `add(N)`-approximation of `x`, with `N` given by its
/// indecomposable summands `n_summands`, one module per isomorphism class.
///
/// # Algorithm
///
/// Write `M_i` for `Hom(x, N_i)` and `R_i` for the `i`-th component of
/// `Hom(x, N) rad End(N)`, namely
/// `sum_{j != i} M_j . Hom(N_j, N_i) + M_i . rad End(N_i)`. The sum over
/// `j != i` uses all of `Hom(N_j, N_i)`, which is the categorical radical
/// exactly because `N_j` and `N_i` are non-isomorphic indecomposables; the
/// constructor rejects a repeated class for that reason.
///
/// For each `i`, start the span at `R_i` and scan the `F_p` basis of `M_i` in
/// its [`HomSpace`] order. Accept a basis map `g` as a generator when it lies
/// outside the span, then add `g . End(N_i)` to the span. Each accepted
/// generator contributes one copy of `N_i` to `B`, and `f` is the map whose
/// component into that copy is `g`.
///
/// Acceptance raises the `F_p` dimension of the span by exactly the residue
/// degree `d_i`. The span already holds `g . rad End(N_i)`, so the new part is
/// the image of `D_i = End(N_i) / rad End(N_i)`, a right `D_i`-line because
/// `g` itself is outside the span. The constructor asserts that rise and
/// reports [`ApproxDefect::GeneratorGrowth`] otherwise. The scan visits each of
/// the `dim_{F_p} M_i` basis maps once, so the loop is finite and accepts at
/// most `dim_{F_p} M_i / d_i` generators.
///
/// The accepted generators are a minimal generating set of `Hom(x, N)` as a
/// right `End(N)`-module, by Nakayama, so `Hom(B, N) -> Hom(x, N)` is a
/// projective cover and `f` is a minimal left approximation. No reduction
/// pass follows. The constructor checks both properties and reports a defect
/// rather than repairing the result.
///
/// # Errors
/// [`ApproxError::SummandNotIndecomposable`] when an add-generator fails the
/// indecomposability gate, [`ApproxError::RepeatedSummand`] when two are
/// isomorphic, [`ApproxError::Hom`] when the modules do not share one algebra,
/// and [`ApproxError::Defect`] on a failed internal cross-check.
pub fn left_approximation(
    x: &Module,
    n_summands: &[Module],
) -> Result<MinimalLeftApproximation, ApproxError> {
    hit(Site::LeftApproximation);
    let summands = certify(n_summands)?;
    let field = x.field();
    let spaces = summands
        .iter()
        .map(|summand| HomSpace::new(x, summand.module()).map_err(ApproxError::Hom))
        .collect::<Result<Vec<_>, _>>()?;
    let built = build_approximation(x, &summands, &spaces, &field)?;
    let (kernel, radical) = minimality_data(x, &built.b, &built.map, &field)?;

    Ok(MinimalLeftApproximation {
        map: built.map,
        summands,
        slots: built.slots,
        inclusions: built.inclusions,
        projections: built.projections,
        factorizations: built.factorizations,
        kernel,
        radical,
    })
}

fn radical_rows(
    space: &HomSpace,
    summand: &IndecomposableModule,
) -> Result<Vec<Vec<Fp>>, ApproxError> {
    let radical = summand.endo().radical_basis();
    let mut rows = Vec::new();
    for r in 0..radical.rows() {
        let step = summand.endo().morphism(radical.row(r));
        for g in space.basis() {
            rows.push(compose_into(space, g, &step)?);
        }
    }
    Ok(rows)
}

fn foreign_rows(
    target_space: &HomSpace,
    source_space: &HomSpace,
    source: &IndecomposableModule,
    target: &IndecomposableModule,
) -> Result<Vec<Vec<Fp>>, ApproxError> {
    let between = hom(source.module(), target.module()).map_err(ApproxError::Hom)?;
    let mut rows = Vec::new();
    for step in &between {
        for g in source_space.basis() {
            rows.push(compose_into(target_space, g, step)?);
        }
    }
    Ok(rows)
}

fn initial_rows(
    index: usize,
    summands: &[IndecomposableModule],
    spaces: &[HomSpace],
) -> Result<Vec<Vec<Fp>>, ApproxError> {
    let mut rows = Vec::new();
    for (other_index, other) in summands.iter().enumerate() {
        let part = if other_index == index {
            radical_rows(&spaces[index], &summands[index])
        } else {
            foreign_rows(
                &spaces[index],
                &spaces[other_index],
                other,
                &summands[index],
            )
        }?;
        rows.extend(part);
    }
    Ok(rows)
}

fn reduced_rows(rows: &[Vec<Fp>], width: usize, field: &PrimeField) -> RowReducer {
    let mut span = RowReducer::new(width);
    for row in rows {
        span.push(row, field);
    }
    span
}

fn accept_generator(
    span: &mut RowReducer,
    width: usize,
    summand_index: usize,
    basis_index: usize,
    summand: &IndecomposableModule,
    space: &HomSpace,
    field: &PrimeField,
) -> Result<Option<Morphism>, ApproxError> {
    if !span.push(&unit_vector(width, basis_index), field) {
        return Ok(None);
    }
    let before = span.rank() - 1;
    let generator = &space.basis()[basis_index];
    for endomorphism in summand.endo().basis() {
        span.push(&compose_into(space, generator, endomorphism)?, field);
    }
    let growth = span.rank() - before;
    if growth != summand.residue_degree() {
        return Err(ApproxError::Defect(ApproxDefect::GeneratorGrowth {
            summand: summand_index,
            growth,
            residue_degree: summand.residue_degree(),
        }));
    }
    Ok(Some(generator.clone()))
}

fn generators_for_summand(
    index: usize,
    summand: &IndecomposableModule,
    summands: &[IndecomposableModule],
    spaces: &[HomSpace],
    field: &PrimeField,
) -> Result<Vec<Morphism>, ApproxError> {
    let space = &spaces[index];
    let rows = initial_rows(index, summands, spaces)?;
    let mut span = reduced_rows(&rows, space.dim(), field);
    let mut generators = Vec::new();
    for basis_index in 0..space.dim() {
        if let Some(generator) = accept_generator(
            &mut span,
            space.dim(),
            index,
            basis_index,
            summand,
            space,
            field,
        )? {
            generators.push(generator);
        }
    }
    Ok(generators)
}

fn generator_data(
    summands: &[IndecomposableModule],
    spaces: &[HomSpace],
    field: &PrimeField,
) -> Result<(Vec<usize>, Vec<Morphism>), ApproxError> {
    let mut slots = Vec::new();
    let mut components = Vec::new();
    for (index, summand) in summands.iter().enumerate() {
        let generators = generators_for_summand(index, summand, summands, spaces, field)?;
        for generator in generators {
            slots.push(index);
            components.push(generator);
        }
    }
    Ok((slots, components))
}

fn map_images(
    map: &Morphism,
    source_space: &HomSpace,
    target_space: &HomSpace,
) -> Result<Vec<Vec<Fp>>, ApproxError> {
    let mut images = Vec::with_capacity(source_space.dim());
    for h in source_space.basis() {
        let composite = map.then(h).expect("f composes with a map out of B");
        images.push(
            target_space
                .coords(&composite)
                .map_err(ApproxError::HomSpace)?,
        );
    }
    Ok(images)
}

fn factorizations(
    b: &Module,
    map: &Morphism,
    summands: &[IndecomposableModule],
    spaces: &[HomSpace],
    field: &PrimeField,
) -> Result<Vec<Vec<Vec<Fp>>>, ApproxError> {
    let mut result = Vec::with_capacity(summands.len());
    for (index, summand) in summands.iter().enumerate() {
        let source_space = HomSpace::new(b, summand.module()).map_err(ApproxError::Hom)?;
        let target_space = &spaces[index];
        let images = map_images(map, &source_space, target_space)?;
        let system = DenseMat::from_rows_with_cols(&images, target_space.dim()).transpose();
        result.push(unit_factorizations(&system, field).map_err(|basis_index| {
            ApproxError::Defect(ApproxDefect::FactorizationMissing {
                summand: index,
                basis_index,
            })
        })?);
    }
    Ok(result)
}

fn minimality_data(
    x: &Module,
    b: &Module,
    map: &Morphism,
    field: &PrimeField,
) -> Result<(DenseMat, Vec<Vec<Fp>>), ApproxError> {
    let endo = EndoAlgebra::new(b);
    let space = HomSpace::new(x, b).map_err(ApproxError::Hom)?;
    let rows = composition_rows(map, &endo, &space)?;
    let kernel = row_relations(&rows, space.dim(), field);
    let radical = radical_coordinates(&endo, &kernel).map_err(|row| {
        ApproxError::Defect(ApproxDefect::KernelOutsideRadical {
            row,
            kernel_dim: kernel.rows(),
            radical_dim: endo.radical_dim(),
        })
    })?;
    Ok((kernel, radical))
}

struct ApproximationBuild {
    slots: Vec<usize>,
    b: Module,
    inclusions: Vec<Morphism>,
    projections: Vec<Morphism>,
    map: Morphism,
    factorizations: Vec<Vec<Vec<Fp>>>,
}

fn build_approximation(
    x: &Module,
    summands: &[IndecomposableModule],
    spaces: &[HomSpace],
    field: &PrimeField,
) -> Result<ApproximationBuild, ApproxError> {
    let (slots, components) = generator_data(summands, spaces, field)?;
    let (b, inclusions, projections) =
        direct_sum_or_zero(x.algebra(), slots.iter().map(|&i| summands[i].module()));
    let mut map = zero_morphism(x, &b).map_err(ApproxError::Hom)?;
    for (slot, component) in components.iter().enumerate() {
        let block = component
            .then(&inclusions[slot])
            .expect("a component lands in its own block");
        map = add_morphisms(&map, &block);
    }
    let factorizations = factorizations(&b, &map, summands, spaces, field)?;
    Ok(ApproximationBuild {
        slots,
        b,
        inclusions,
        projections,
        map,
        factorizations,
    })
}
