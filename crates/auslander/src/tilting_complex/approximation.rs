use super::cache::HomotopyBlockBuilder;
use super::classification::basis_representative;
use super::*;
use crate::linalg::RowReducer;

struct ApproximationBasis {
    indices: Vec<usize>,
    representatives: Vec<ChainMap>,
}

/// Representatives of `rad(T_middle, T_other)` for a left approximation, or
/// of `rad(T_other, T_middle)` for a right one.
///
/// The certified parent has pairwise non-isomorphic summands with local
/// endomorphism rings. So the radical between distinct summands is the whole
/// Hom space, and on one summand it is the kernel of its residue map.
fn radical_maps(
    parent: &CertifiedSiltingComplex,
    middle: usize,
    other: usize,
    direction: ApproximationDirection,
    blocks: &mut HomotopyBlockBuilder<'_>,
) -> Result<Vec<ChainMap>, Interrupt> {
    if middle != other {
        let (source, target) = direction.orient(middle, other);
        let space = blocks.get(parent.candidate(), source, target, 0)?;
        return Ok((0..space.dim())
            .map(|index| basis_representative(&space, index))
            .collect());
    }
    let end = &parent.degree_zero_endomorphisms()[other];
    let residue = std::slice::from_ref(&parent.degree_zero_residues()[other]);
    let kernel = DenseMat::from_rows(residue).kernel_basis(&parent.candidate().algebra().field());
    Ok((0..kernel.rows())
        .map(|row| end.representative(kernel.row(row)))
        .collect())
}

/// Loads the maps between `T_replaced` and `T_other` that factor through a
/// radical map of `add T'`, where `T'` omits `T_replaced`.
///
/// For a left approximation these are the composites `f·r` with
/// `f: T_replaced → T_k` and `r ∈ rad(T_k, T_other)` over every `k` in `T'`,
/// including `k = other`. A right approximation uses `r·f` with
/// `r ∈ rad(T_other, T_k)` and `f: T_k → T_replaced`. Both products are
/// bilinear, so basis composites span this subspace `R_other`.
fn radical_factoring(
    parent: &CertifiedSiltingComplex,
    replaced: usize,
    other: usize,
    direction: ApproximationDirection,
    space: &HomotopyHomQuotient,
    blocks: &mut HomotopyBlockBuilder<'_>,
) -> Result<RowReducer, Interrupt> {
    let candidate = parent.candidate();
    let field = candidate.algebra().field();
    let mut reducer = RowReducer::new(space.dim());
    for middle in (0..candidate.len()).filter(|&middle| middle != replaced) {
        let (source, target) = direction.orient(replaced, middle);
        let outer = blocks.get(candidate, source, target, 0)?;
        let radical = radical_maps(parent, middle, other, direction, blocks)?;
        for index in 0..outer.dim() {
            let fixed = basis_representative(&outer, index);
            for map in &radical {
                blocks.meter.charge()?;
                let (first, second) = direction.orient(&fixed, map);
                reducer.push(&space.reduce(&first.then(second)?)?.0, &field);
            }
        }
    }
    Ok(reducer)
}

/// Selects the components of a minimal `add T'` approximation of
/// `T_replaced`.
///
/// For each `j`, a basis map of `Hom(T_replaced, T_j)` is kept when it is
/// independent of `R_j` and of the maps kept before it. The kept maps then
/// project to a basis of `Hom(T_replaced, T_j) / R_j`. When `R_j = 0`, every
/// basis map is kept. The proof is for a left approximation `f: X → Y`; the
/// right case is dual. `J = rad End(T')` is nilpotent, and
/// `Hom(X, T') = F + Hom(X, T')·J` with `F` the span of the kept maps.
/// Iterating gives `Hom(X, T') = F·End(T')`, so `f` is an approximation. If
/// `f·φ = f` for `φ` in `End(Y)`, reduce each component modulo `R_j`. The
/// entries of `φ` between distinct summands and the radical parts of its
/// diagonal entries land in `R_j`. The scalar parts `λ` then satisfy
/// `f ≡ f·λ`, and independence forces `λ = 1`. So `φ` is the identity plus a
/// radical endomorphism, hence an automorphism, and `f` is left minimal.
fn approximation_basis(
    parent: &CertifiedSiltingComplex,
    replaced: usize,
    direction: ApproximationDirection,
    blocks: &mut HomotopyBlockBuilder<'_>,
) -> Result<ApproximationBasis, Interrupt> {
    let candidate = parent.candidate();
    let field = candidate.algebra().field();
    let mut indices = Vec::new();
    let mut representatives = Vec::new();
    for other in 0..candidate.len() {
        if other == replaced {
            continue;
        }
        let (source, target) = direction.orient(replaced, other);
        let space = blocks.get(candidate, source, target, 0)?;
        let mut factoring = radical_factoring(parent, replaced, other, direction, &space, blocks)?;
        for basis in 0..space.dim() {
            let mut unit = vec![field.zero(); space.dim()];
            unit[basis] = field.one();
            if factoring.push(&unit, &field) {
                indices.push(other);
                representatives.push(basis_representative(&space, basis));
            }
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
    parent: &CertifiedSiltingComplex,
    replaced: usize,
    direction: ApproximationDirection,
    blocks: &mut HomotopyBlockBuilder<'_>,
) -> Result<(ChainMap, Vec<usize>), Interrupt> {
    let candidate = parent.candidate();
    let basis = approximation_basis(parent, replaced, direction, blocks)?;
    let map = if basis.indices.is_empty() {
        zero_approximation(candidate, replaced, direction)?
    } else {
        nonzero_approximation(candidate, replaced, &basis, direction)?
    };
    Ok((map, basis.indices))
}

pub(super) fn approximation_map(
    parent: &CertifiedSiltingComplex,
    replaced: usize,
    direction: ApproximationDirection,
) -> Result<(ChainMap, Vec<usize>), TiltingComplexError> {
    let mut meter = WorkMeter::default();
    let mut blocks = HomotopyBlockBuilder::cold(&mut meter);
    unmetered(approximation_map_with_blocks(
        parent,
        replaced,
        direction,
        &mut blocks,
    ))
}
