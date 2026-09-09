use crate::algebra::Algebra;

use super::super::cochain::next_usize;
use super::super::limits::{BarCoordinate, BarStage};
use super::tuple::walk_tuples;
use super::{Budget, BuildResult, Ledger};

#[derive(Clone, Debug)]
pub(crate) struct Layout {
    pub(crate) coordinates: Vec<BarCoordinate>,
    pub(crate) offsets: Vec<usize>,
}

#[derive(Clone, Debug)]
pub(crate) struct TupleOffsets {
    pub(crate) offsets: Vec<usize>,
    pub(crate) segments: Vec<(usize, u32, u32)>,
}

#[derive(Clone, Debug)]
pub(crate) struct Shape {
    pub(crate) tuples: usize,
    pub(crate) cochain_dim: usize,
    pub(crate) starts: Vec<usize>,
}

fn square_work(n: usize, ledger: &Ledger, degree: usize) -> BuildResult<u128> {
    let budget = ledger.budget(degree, BarStage::Shape);
    let square = budget.product([n as u128, n as u128])?;
    let cubic = budget.product([square, n as u128])?;
    budget.sum(cubic, square)
}

fn reserve_power_shape(vertices: usize, ledger: &mut Ledger, degree: usize) -> BuildResult<()> {
    ledger.work(
        degree,
        BarStage::Shape,
        square_work(vertices, ledger, degree)?,
    )?;
    let budget = ledger.budget(degree, BarStage::Shape);
    let entries = budget.product([vertices as u128, vertices as u128])?;
    budget.size(entries).map(|_| ())
}

fn power_entry(
    source: usize,
    target: usize,
    current: Option<&[Vec<usize>]>,
    algebra: &Algebra,
    budget: Budget<'_>,
) -> BuildResult<usize> {
    let mut total = 0u128;
    let vertices = algebra.quiver().num_vertices() as usize;
    for middle in 0..vertices {
        let current_count =
            current.map_or(usize::from(source == middle), |power| power[source][middle]);
        let radical_count = algebra
            .paths_between(middle as u32, target as u32)
            .len()
            .checked_sub(usize::from(middle == target))
            .expect("every vertex idempotent is a normal word");
        let product = budget.product([current_count as u128, radical_count as u128])?;
        total = budget.sum(total, product)?;
    }
    budget.size(total)
}

pub(crate) fn advance_power(
    current: Option<&[Vec<usize>]>,
    algebra: &Algebra,
    ledger: &mut Ledger,
    degree: usize,
) -> BuildResult<Vec<Vec<usize>>> {
    let vertices = algebra.quiver().num_vertices() as usize;
    reserve_power_shape(vertices, ledger, degree)?;
    let budget = ledger.budget(degree, BarStage::Shape);
    let mut next = vec![vec![0; vertices]; vertices];
    for (source, next_row) in next.iter_mut().enumerate() {
        for (target, entry) in next_row.iter_mut().enumerate() {
            *entry = power_entry(source, target, current, algebra, budget)?;
        }
    }
    Ok(next)
}

fn shape_row(
    algebra: &Algebra,
    budget: Budget<'_>,
    source: usize,
    row: &[usize],
) -> BuildResult<(u128, u128, usize)> {
    let mut tuples = 0u128;
    let mut from_source = 0u128;
    let mut cochain_dim = 0u128;
    for (target, &count) in row.iter().enumerate() {
        tuples = budget.sum(tuples, count as u128)?;
        from_source = budget.sum(from_source, count as u128)?;
        let addend = budget.product([
            count as u128,
            algebra.paths_between(source as u32, target as u32).len() as u128,
        ])?;
        cochain_dim = budget.sum(cochain_dim, addend)?;
    }
    let start = budget.size(from_source)?;
    Ok((tuples, cochain_dim, start))
}

fn shape_totals(
    algebra: &Algebra,
    radical_power: &[Vec<usize>],
    budget: Budget<'_>,
) -> BuildResult<(usize, usize, Vec<usize>)> {
    let mut tuples = 0u128;
    let mut cochain_dim = 0u128;
    let mut starts = Vec::with_capacity(radical_power.len());
    for (source, row) in radical_power.iter().enumerate() {
        let (row_tuples, row_cochain_dim, start) = shape_row(algebra, budget, source, row)?;
        tuples = budget.sum(tuples, row_tuples)?;
        cochain_dim = budget.sum(cochain_dim, row_cochain_dim)?;
        starts.push(start);
    }
    let tuples = budget.size(tuples)?;
    let cochain_dim = budget.size(cochain_dim)?;
    Ok((tuples, cochain_dim, starts))
}

pub(crate) fn measure_shape(
    algebra: &Algebra,
    radical_power: &[Vec<usize>],
    ledger: &mut Ledger,
    degree: usize,
) -> BuildResult<Shape> {
    let budget = ledger.budget(degree, BarStage::Shape);
    let (tuples, cochain_dim, starts) = shape_totals(algebra, radical_power, budget)?;
    ledger.shape(degree, tuples, cochain_dim)?;
    Ok(Shape {
        tuples,
        cochain_dim,
        starts,
    })
}

pub(crate) fn measure_identity_shape(
    algebra: &Algebra,
    ledger: &mut Ledger,
    degree: usize,
) -> BuildResult<Shape> {
    let budget = ledger.budget(degree, BarStage::Shape);
    let vertices = algebra.quiver().num_vertices() as usize;
    let mut cochain_dim = 0u128;
    for vertex in 0..vertices {
        cochain_dim = budget.sum(
            cochain_dim,
            algebra.paths_between(vertex as u32, vertex as u32).len() as u128,
        )?;
    }
    let cochain_dim = budget.size(cochain_dim)?;
    ledger.shape(degree, vertices, cochain_dim)?;
    Ok(Shape {
        tuples: vertices,
        cochain_dim,
        starts: vec![1; vertices],
    })
}

pub(crate) fn reserve_layout_work(
    current: &Shape,
    next: &Shape,
    degree: usize,
    ledger: &mut Ledger,
) -> BuildResult<()> {
    let budget = ledger.budget(degree, BarStage::Layout);
    let tuple_scan = budget.product([
        next.tuples as u128,
        next_usize(ledger, degree, BarStage::Layout, degree)? as u128,
    ])?;
    let units = budget.sum(tuple_scan, current.cochain_dim as u128)?;
    ledger.work(degree, BarStage::Layout, units)
}

pub(crate) fn build_tuple_offsets(
    algebra: &Algebra,
    degree: usize,
    shape: &Shape,
    starts: &[Vec<usize>],
    ledger: &Ledger,
) -> BuildResult<TupleOffsets> {
    let budget = ledger.budget(degree, BarStage::Layout);
    let capacity = next_usize(ledger, degree, BarStage::Layout, shape.tuples)?;
    let mut offsets = Vec::with_capacity(capacity);
    let mut segments = Vec::new();
    let mut offset = 0usize;
    walk_tuples(
        algebra,
        degree,
        shape.tuples,
        starts,
        |rank, _, source, target| {
            offsets.push(offset);
            let outputs = algebra.paths_between(source, target);
            if !outputs.is_empty() {
                segments.push((rank, source, target));
            }
            offset = budget.size(budget.sum(offset as u128, outputs.len() as u128)?)?;
            Ok::<(), super::Stop>(())
        },
    )?;
    offsets.push(offset);
    debug_assert_eq!(offset, shape.cochain_dim);
    debug_assert_eq!(offsets.len(), capacity);
    Ok(TupleOffsets { offsets, segments })
}

pub(crate) fn build_layout(
    algebra: &Algebra,
    shape: &Shape,
    tuple_offsets: TupleOffsets,
) -> Layout {
    let mut coordinates = Vec::with_capacity(shape.cochain_dim);
    for (rank, source, target) in tuple_offsets.segments {
        assert_eq!(coordinates.len(), tuple_offsets.offsets[rank]);
        coordinates.extend(algebra.paths_between(source, target).iter().map(|&output| {
            BarCoordinate {
                tuple_rank: rank,
                output,
            }
        }));
    }
    assert_eq!(coordinates.len(), shape.cochain_dim);
    assert_eq!(tuple_offsets.offsets.len(), shape.tuples + 1);
    Layout {
        coordinates,
        offsets: tuple_offsets.offsets,
    }
}
