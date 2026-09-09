use crate::algebra::{Algebra, BasisIdx};
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;

use super::super::cochain::next_usize;
use super::super::limits::BarStage;
use super::tuple;
use super::{BuildResult, Layout, Ledger, Shape};

struct DifferentialPlan(usize, usize, usize);

struct DifferentialContext<'a> {
    algebra: &'a Algebra,
    degree: usize,
    target_degree: usize,
    shape: &'a Shape,
    source_layout: &'a Layout,
    target_offsets: &'a [usize],
    starts: &'a [Vec<usize>],
    field: &'a PrimeField,
}

fn differential_plan(
    algebra: &Algebra,
    degree: usize,
    cochain_dim: usize,
    target_offsets: &[usize],
    ledger: &mut Ledger,
) -> BuildResult<DifferentialPlan> {
    let stage = BarStage::Differential;
    let target_dim = *target_offsets
        .last()
        .expect("a tuple offset table has its final offset");
    let target_degree = next_usize(ledger, degree, stage, degree)?;
    let term_count = next_usize(ledger, target_degree, stage, target_degree)?;
    let algebra_dimension = next_usize(ledger, degree, stage, algebra.dim())?;
    let budget = ledger.budget(degree, stage);
    let entries = budget.size(budget.product([cochain_dim as u128, target_dim as u128])?)?;
    ledger.scratch(degree, stage, entries)?;
    ledger.work(degree, stage, entries as u128)?;
    let target_tuples = ledger.checked_usize(degree, stage, target_offsets.len().checked_sub(1))?;
    let term_work = ledger.budget(degree, stage).product([
        cochain_dim as u128,
        target_tuples as u128,
        term_count as u128,
        algebra_dimension as u128,
    ])?;
    ledger
        .work(degree, stage, term_work)
        .and(Ok(DifferentialPlan(target_dim, target_degree, entries)))
}

pub(crate) fn build_differential(
    algebra: &Algebra,
    degree: usize,
    shape: &Shape,
    source_layout: &Layout,
    target_offsets: &[usize],
    starts: &[Vec<usize>],
    ledger: &mut Ledger,
) -> BuildResult<DenseMat> {
    let stage = BarStage::Differential;
    let plan = differential_plan(algebra, degree, shape.cochain_dim, target_offsets, ledger)?;
    let field = algebra.field();
    let mut differential = DenseMat::zero(shape.cochain_dim, plan.0);
    if differential_is_empty(shape, &plan) {
        ledger.retain(degree, stage, plan.2)?;
        return Ok(differential);
    }
    fill_differential(
        &DifferentialContext {
            algebra,
            degree,
            target_degree: plan.1,
            shape,
            source_layout,
            target_offsets,
            starts,
            field: &field,
        },
        &mut differential,
    );
    ledger.retain(degree, stage, plan.2)?;
    Ok(differential)
}

fn differential_is_empty(shape: &Shape, plan: &DifferentialPlan) -> bool {
    shape.cochain_dim == 0 || plan.0 == 0
}

fn fill_differential(context: &DifferentialContext<'_>, differential: &mut DenseMat) {
    tuple::walk_tuples(
        context.algebra,
        context.degree,
        context.shape.tuples,
        context.starts,
        |source_rank, source, source_start, _source_end| {
            let row_start = context.source_layout.offsets[source_rank];
            for row in row_start..context.source_layout.offsets[source_rank + 1] {
                let output = context.source_layout.coordinates[row].output;
                tuple::walk_tuples(
                    context.algebra,
                    context.target_degree,
                    context.target_offsets.len() - 1,
                    context.starts,
                    |target_rank, target, target_start, target_end| {
                        fill_target_tuple(
                            context,
                            source,
                            source_start,
                            target,
                            (target_rank, target_start, target_end),
                            (row, output),
                            differential,
                        );
                        Ok::<(), ()>(())
                    },
                )
                .expect("the differential callback cannot fail");
            }
            Ok::<(), ()>(())
        },
    )
    .expect("the differential callback cannot fail");
}

fn fill_target_tuple(
    context: &DifferentialContext,
    source: &[BasisIdx],
    source_start: u32,
    target: &[BasisIdx],
    target_coordinates: (usize, u32, u32),
    row_output: (usize, BasisIdx),
    differential: &mut DenseMat,
) {
    let (target_rank, target_start, target_end) = target_coordinates;
    let (row, output) = row_output;
    let coordinate = TargetCoordinate {
        algebra: context.algebra,
        offsets: context.target_offsets,
        tuple_rank: target_rank,
        source: target_start,
        target: target_end,
        field: context.field,
    };
    if context.degree == 0 {
        if source_start == coordinate.target {
            coordinate.add_product(differential, row, target[0], output, false);
        }
        if source_start == coordinate.source {
            coordinate.add_product(differential, row, output, target[0], true);
        }
        return;
    }
    if source == &target[1..] {
        coordinate.add_product(differential, row, target[0], output, false);
    }
    for i in 1..=context.degree {
        for &(middle, coefficient) in &coordinate.algebra.mul_basis(target[i - 1], target[i]) {
            if matches_middle(source, target, i, middle) {
                coordinate.add(
                    differential,
                    row,
                    output,
                    signed(coefficient, i % 2 == 1, context.field),
                );
            }
        }
    }
    if source == &target[..context.degree] {
        let final_word = target[context.degree];
        coordinate.add_product(
            differential,
            row,
            output,
            final_word,
            context.target_degree % 2 == 1,
        );
    }
}

fn matches_middle(source: &[BasisIdx], target: &[BasisIdx], i: usize, middle: BasisIdx) -> bool {
    source[..i - 1] == target[..i - 1] && source[i - 1] == middle && source[i..] == target[i + 1..]
}

fn signed(value: Fp, negative: bool, field: &PrimeField) -> Fp {
    if negative { field.neg(value) } else { value }
}

struct TargetCoordinate<'a> {
    algebra: &'a Algebra,
    offsets: &'a [usize],
    tuple_rank: usize,
    source: u32,
    target: u32,
    field: &'a PrimeField,
}

impl TargetCoordinate<'_> {
    fn add(&self, matrix: &mut DenseMat, row: usize, output: BasisIdx, value: Fp) {
        let position = self
            .algebra
            .paths_between(self.source, self.target)
            .binary_search(&output)
            .expect("a bar differential stays in the target component");
        let column = self.offsets[self.tuple_rank] + position;
        matrix.set(row, column, self.field.add(matrix.get(row, column), value));
    }

    fn add_product(
        &self,
        matrix: &mut DenseMat,
        row: usize,
        left: BasisIdx,
        right: BasisIdx,
        negative: bool,
    ) {
        for &(output, value) in self.algebra.mul_basis(left, right).iter() {
            self.add(matrix, row, output, signed(value, negative, self.field));
        }
    }
}
