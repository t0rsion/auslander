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

/// A source tuple with at least one cochain row.
struct SourceTuple {
    words: Vec<BasisIdx>,
    start: u32,
    rows: std::ops::Range<usize>,
}

/// Every entry is a sum over (source row, target tuple) pairs, so the fill
/// order does not change the matrix. Target tuples run outermost: each one
/// is decoded, and its adjacent products are taken, once for all rows.
fn fill_differential(context: &DifferentialContext<'_>, differential: &mut DenseMat) {
    let sources = source_tuples(context);
    let mut products = Vec::with_capacity(context.degree);
    tuple::walk_tuples(
        context.algebra,
        context.target_degree,
        context.target_offsets.len() - 1,
        context.starts,
        |target_rank, target, target_start, target_end| {
            let coordinate = TargetCoordinate {
                algebra: context.algebra,
                offsets: context.target_offsets,
                tuple_rank: target_rank,
                source: target_start,
                target: target_end,
                field: context.field,
            };
            products.clear();
            products.extend(
                (1..=context.degree).map(|i| context.algebra.mul_basis(target[i - 1], target[i])),
            );
            for source in &sources {
                fill_source(
                    context,
                    &coordinate,
                    source,
                    target,
                    &products,
                    differential,
                );
            }
            Ok::<(), ()>(())
        },
    )
    .expect("the differential callback cannot fail");
}

fn source_tuples(context: &DifferentialContext<'_>) -> Vec<SourceTuple> {
    let mut sources = Vec::new();
    tuple::walk_tuples(
        context.algebra,
        context.degree,
        context.shape.tuples,
        context.starts,
        |rank, words, start, _end| {
            let offsets = &context.source_layout.offsets;
            if offsets[rank] < offsets[rank + 1] {
                sources.push(SourceTuple {
                    words: words.to_vec(),
                    start,
                    rows: offsets[rank]..offsets[rank + 1],
                });
            }
            Ok::<(), ()>(())
        },
    )
    .expect("the source callback cannot fail");
    sources
}

/// Degree zero has vertex sources: the endpoint tests are then the whole
/// face condition, and in positive degree the word tests imply them.
fn fill_source(
    context: &DifferentialContext,
    coordinate: &TargetCoordinate,
    source: &SourceTuple,
    target: &[BasisIdx],
    products: &[Vec<(BasisIdx, Fp)>],
    differential: &mut DenseMat,
) {
    let (words, degree) = (source.words.as_slice(), context.degree);
    let first =
        words == &target[1..] && source.start == context.algebra.basis()[target[0]].target();
    let last = words == &target[..degree] && source.start == coordinate.source;
    let middles = middle_coefficients(context, words, target, products);
    if !first && !last && middles.is_empty() {
        return;
    }
    for row in source.rows.clone() {
        let output = context.source_layout.coordinates[row].output;
        if first {
            coordinate.add_product(differential, row, target[0], output, false);
        }
        for &value in &middles {
            coordinate.add(differential, row, output, value);
        }
        if last {
            let negative = context.target_degree % 2 == 1;
            coordinate.add_product(differential, row, output, target[degree], negative);
        }
    }
}

/// The signed coefficients of the inner faces of `target` that equal `source`.
fn middle_coefficients(
    context: &DifferentialContext,
    source: &[BasisIdx],
    target: &[BasisIdx],
    products: &[Vec<(BasisIdx, Fp)>],
) -> Vec<Fp> {
    let mut values = Vec::new();
    for (i, product) in (1..=context.degree).zip(products) {
        for &(middle, coefficient) in product {
            if matches_middle(source, target, i, middle) {
                values.push(signed(coefficient, i % 2 == 1, context.field));
            }
        }
    }
    values
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
