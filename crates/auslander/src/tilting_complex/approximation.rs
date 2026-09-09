use super::cache::HomotopyBlockBuilder;
use super::classification::basis_representative;
use super::*;

struct ApproximationBasis {
    indices: Vec<usize>,
    representatives: Vec<ChainMap>,
}

fn approximation_basis(
    candidate: &TiltingComplexCandidate,
    replaced: usize,
    direction: ApproximationDirection,
    blocks: &mut HomotopyBlockBuilder<'_>,
) -> Result<ApproximationBasis, TiltingComplexError> {
    let mut indices = Vec::new();
    let mut representatives = Vec::new();
    for other in 0..candidate.len() {
        if other == replaced {
            continue;
        }
        let (source, target) = direction.orient(replaced, other);
        let space = blocks.get(candidate, source, target, 0)?;
        for basis in 0..space.dim() {
            indices.push(other);
            representatives.push(basis_representative(&space, basis));
        }
    }
    Ok(ApproximationBasis {
        indices,
        representatives,
    })
}

fn zero_approximation(
    candidate: &TiltingComplexCandidate,
    replaced: usize,
    direction: ApproximationDirection,
) -> Result<ChainMap, TiltingComplexError> {
    let fixed = candidate.summands()[replaced].complex();
    let zero = BoundedComplex::new(
        fixed.lower(),
        vec![Module::zero(candidate.algebra())],
        Vec::new(),
    )?;
    let (source, target) = direction.orient(fixed, &zero);
    ChainMap::zero(source, target).map_err(Into::into)
}

fn insert_block(matrix: &mut DenseMat, block: &DenseMat, row_offset: usize, column_offset: usize) {
    (0..block.rows()).for_each(|row| {
        (0..block.cols()).for_each(|column| {
            let (target_row, target_column) = (row_offset + row, column_offset + column);
            matrix.set(target_row, target_column, block.get(row, column));
        })
    })
}

pub(super) fn approximation_matrix(
    source: &Module,
    target: &Module,
    parts: &[Module],
    representatives: &[ChainMap],
    degree: i32,
    vertex: u32,
    direction: ApproximationDirection,
) -> Result<DenseMat, TiltingComplexError> {
    let mut matrix = DenseMat::zero(source.dim_at(vertex), target.dim_at(vertex));
    let mut offset = 0;
    for (part, representative) in parts.iter().zip(representatives) {
        let ((rows, row_offset), _) =
            direction.orient((source.dim_at(vertex), 0), (part.dim_at(vertex), offset));
        let ((columns, column_offset), _) =
            direction.orient((part.dim_at(vertex), offset), (target.dim_at(vertex), 0));
        let block = if representative.range().contains(degree) {
            representative.component(degree)?.map_at(vertex).clone()
        } else {
            DenseMat::zero(rows, columns)
        };
        insert_block(&mut matrix, &block, row_offset, column_offset);
        offset += part.dim_at(vertex);
    }
    Ok(matrix)
}

fn approximation_component(
    candidate: &TiltingComplexCandidate,
    basis: &ApproximationBasis,
    source: &Module,
    target: &Module,
    degree: i32,
    direction: ApproximationDirection,
) -> Result<Morphism, TiltingComplexError> {
    let parts: Vec<Module> = basis
        .indices
        .iter()
        .map(|&index| {
            let complex = candidate.summands()[index].complex();
            if complex.range().contains(degree) {
                complex
                    .term(degree)
                    .expect("the checked range contains the degree")
                    .clone()
            } else {
                Module::zero(complex.terms()[0].algebra())
            }
        })
        .collect();
    let matrices = (0..candidate.algebra().quiver().num_vertices())
        .map(|vertex| {
            approximation_matrix(
                source,
                target,
                &parts,
                &basis.representatives,
                degree,
                vertex,
                direction,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    Morphism::new(source, target, matrices).map_err(Into::into)
}

fn approximation_components(
    candidate: &TiltingComplexCandidate,
    basis: &ApproximationBasis,
    range: DegreeRange,
    source: &BoundedComplex,
    target: &BoundedComplex,
    direction: ApproximationDirection,
) -> Result<Vec<Morphism>, TiltingComplexError> {
    (range.lower()..=range.upper())
        .map(|degree| {
            let offset = (degree - range.lower()) as usize;
            approximation_component(
                candidate,
                basis,
                &source.terms()[offset],
                &target.terms()[offset],
                degree,
                direction,
            )
        })
        .collect()
}

fn nonzero_approximation(
    candidate: &TiltingComplexCandidate,
    replaced: usize,
    basis: &ApproximationBasis,
    direction: ApproximationDirection,
) -> Result<ChainMap, TiltingComplexError> {
    let fixed = candidate.summands()[replaced].complex().clone();
    let parts: Vec<&BoundedComplex> = basis
        .indices
        .iter()
        .map(|&index| candidate.summands()[index].complex())
        .collect();
    let sum = BoundedComplex::direct_sum(&parts)?;
    let (source, target) = match direction {
        ApproximationDirection::Left => (fixed, sum),
        ApproximationDirection::Right => (sum, fixed),
    };
    let range = DegreeRange::new(
        source.lower().min(target.lower()),
        source.upper().max(target.upper()),
    )
    .map_err(|_| TiltingComplexError::DegreeOverflow)?;
    let source = source.padded_to(range)?;
    let target = target.padded_to(range)?;
    let components =
        approximation_components(candidate, basis, range, &source, &target, direction)?;
    ChainMap::new(&source, &target, components).map_err(Into::into)
}

pub(super) fn approximation_map_with_blocks(
    parent: &CertifiedTiltingComplex,
    replaced: usize,
    direction: ApproximationDirection,
    blocks: &mut HomotopyBlockBuilder<'_>,
) -> Result<(ChainMap, Vec<usize>), TiltingComplexError> {
    let candidate = parent.candidate();
    let basis = approximation_basis(candidate, replaced, direction, blocks)?;
    let map = if basis.indices.is_empty() {
        zero_approximation(candidate, replaced, direction)?
    } else {
        nonzero_approximation(candidate, replaced, &basis, direction)?
    };
    Ok((map, basis.indices))
}

pub(super) fn approximation_map(
    parent: &CertifiedTiltingComplex,
    replaced: usize,
    direction: ApproximationDirection,
) -> Result<(ChainMap, Vec<usize>), TiltingComplexError> {
    approximation_map_with_blocks(
        parent,
        replaced,
        direction,
        &mut HomotopyBlockBuilder::cold(),
    )
}
