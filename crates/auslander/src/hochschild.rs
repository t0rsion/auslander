//! Relative normalized bar Hochschild cohomology with typed resource cuts.
//!
//! The complex uses `S = product_v F_p e_v` and `J = rad A`. For a bound
//! quiver algebra, `S` is separable and the nontrivial normal words form a
//! basis of `J`, so this computes ordinary Hochschild cohomology. Degree `n`
//! inputs are composable `n`-tuples of nontrivial normal words. The tuples
//! are streamed in lexicographic basis-index order. Only coordinate ranks and
//! output indices remain in a completed result.
//!
//! [`BarLimits`] has four independent ceilings: tensor tuples per degree,
//! cochain dimension per degree, retained matrix entries plus live scratch,
//! and work units across the request. A cut keeps only degrees that finished
//! before the rejected reservation.

use std::sync::Arc;

use crate::algebra::{Algebra, BasisIdx};
use crate::field::{Fp, PrimeField};
use crate::homspace::deterministic_complement;
use crate::linalg::DenseMat;

/// Resource ceilings for one bar cohomology computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BarLimits {
    /// Maximum number of tensor tuples at one degree.
    pub max_tensor_tuples: usize,
    /// Maximum number of cochain coordinates at one degree.
    pub max_cochain_dim: usize,
    /// Maximum retained matrix entries plus one live scratch reservation.
    pub max_matrix_entries: usize,
    /// Maximum deterministic work units across the request.
    pub max_work_units: u64,
}

/// A caller-controlled bar resource ceiling.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BarLimit {
    TensorTuples,
    CochainDimension,
    MatrixEntries,
    WorkUnits,
}

/// Why a bar computation stopped before the requested degree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BarCutReason {
    Limit(BarLimit),
    SizeOverflow,
}

/// The reservation that stopped a bar computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BarStage {
    DegreeRecord,
    Shape,
    Layout,
    Differential,
    Square,
    Cocycles,
    Coboundaries,
    Complement,
}

/// Typed diagnostics for a bar computation that ran out of resources.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BarBudgetDiagnostics {
    /// The limit or arithmetic overflow that stopped the computation.
    pub reason: BarCutReason,
    /// The operation whose reservation stopped the computation.
    pub stage: BarStage,
    /// The requested last cohomological degree.
    pub requested_degree: usize,
    /// The number of exact leading degrees retained in the cut result.
    pub completed_degree_count: usize,
    /// The first differential that did not finish.
    pub first_uncomputed_differential: usize,
    /// Work units reserved before the rejected reservation.
    pub work_units: u64,
    /// Matrix entries retained before the rejected reservation.
    pub matrix_entries: usize,
    /// The count already used by the rejected resource.
    pub used: u128,
    /// The rejected count after the proposed reservation.
    pub proposed: u128,
    /// The caller ceiling, or `None` for checked arithmetic overflow.
    pub ceiling: Option<u128>,
}

/// The final counters of a completed bar computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BarRunDiagnostics {
    /// Work units reserved by the completed request.
    pub work_units: u64,
    /// Matrix entries retained by the completed request.
    pub matrix_entries: usize,
}

/// One cochain coordinate in a relative bar basis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BarCoordinate {
    /// The lexicographic rank of the input tuple.
    pub tuple_rank: usize,
    /// The normal-word output basis index.
    pub output: BasisIdx,
}

/// A relative bar input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BarInput {
    /// The tagged empty tuple at this vertex, used only in degree zero.
    Vertex(u32),
    /// A positive-degree tuple of nontrivial normal-word basis indices.
    Tuple(Vec<BasisIdx>),
}

/// Rejected Hochschild cohomology input, or an internal differential defect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HochschildError {
    /// The internally constructed differential square is nonzero.
    DifferentialSquare { degree: usize },
    /// A cochain coordinate vector has the wrong length.
    CoordinateCount { expected: usize, got: usize },
    /// The input has the wrong cohomological degree.
    WrongInputDegree { expected: usize, got: usize },
    /// A degree-zero input names a vertex outside the quiver.
    VertexOutOfRange { vertex: u32, num_vertices: u32 },
    /// A positive-degree input names a basis index outside the algebra basis.
    BasisOutOfRange { position: usize, index: usize },
    /// A positive-degree input contains a vertex idempotent.
    TrivialInput { position: usize },
    /// Adjacent input words do not compose.
    NonComposableInput { position: usize },
}

display_error! { error HochschildError {
    Self::DifferentialSquare { degree } => "the bar differential square is nonzero at degree {degree}";
    Self::CoordinateCount { expected, got } => "cochain has {got} coordinates, expected {expected}";
    Self::WrongInputDegree { expected, got } => "bar input has degree {got}, expected {expected}";
    Self::VertexOutOfRange { vertex, num_vertices } => "vertex {vertex} is outside 0..{num_vertices}";
    Self::BasisOutOfRange { position, index } => "bar input index {index} at position {position} is outside the basis";
    Self::TrivialInput { position } => "bar input at position {position} is a vertex idempotent";
    Self::NonComposableInput { position } => "bar input words at positions {position} and {} do not compose", position + 1;
}}

/// Exact Hochschild cohomology through the requested degree.
#[derive(Clone, Debug)]
pub struct HochschildCohomology {
    algebra: Arc<Algebra>,
    requested_degree: usize,
    limits: BarLimits,
    degrees: Vec<HochschildDegree>,
    diagnostics: BarRunDiagnostics,
}

impl HochschildCohomology {
    accessor_methods! {
        /// The algebra whose Hochschild cohomology this stores.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The requested last degree.
        pub requested_degree() -> usize = |this| this.requested_degree;
        /// The effective resource ceilings.
        pub limits() -> BarLimits = |this| this.limits;
        /// The exact spaces `H^0` through `H^requested_degree`.
        pub degrees() -> &[HochschildDegree] = |this| &this.degrees;
        /// The resource counters of the completed request.
        pub diagnostics() -> BarRunDiagnostics = |this| this.diagnostics;
        /// The exact space at one completed degree.
        pub degree(degree: usize) -> Option<&HochschildDegree> = |this| this.degrees.get(degree);
        /// Rebuilds the request and compares every stored coordinate and matrix.
        pub verify() -> bool = |this| matches!(
            build(&this.algebra, this.requested_degree, this.limits),
            Ok(HochschildOutcome::Complete(rebuilt)) if same_complete(this, &rebuilt)
        );
    }
}

/// The exact prefix retained by a typed bar resource cut.
#[derive(Clone, Debug)]
pub struct IncompleteHochschildCohomology {
    algebra: Arc<Algebra>,
    requested_degree: usize,
    limits: BarLimits,
    degrees: Vec<HochschildDegree>,
    diagnostics: BarBudgetDiagnostics,
}

impl IncompleteHochschildCohomology {
    accessor_methods! {
        /// The algebra whose computation was cut.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The requested last degree.
        pub requested_degree() -> usize = |this| this.requested_degree;
        /// The effective resource ceilings.
        pub limits() -> BarLimits = |this| this.limits;
        /// The completed exact prefix.
        pub completed_degrees() -> &[HochschildDegree] = |this| &this.degrees;
        /// The typed cut diagnostics.
        pub diagnostics() -> &BarBudgetDiagnostics = |this| &this.diagnostics;
        /// Rebuilds the request and compares the prefix and the first cut.
        pub verify() -> bool = |this| matches!(
            build(&this.algebra, this.requested_degree, this.limits),
            Ok(HochschildOutcome::Cut(rebuilt)) if same_cut(this, &rebuilt)
        );
    }
}

/// A complete bar result or an exact prefix with a typed cut.
#[derive(Clone, Debug)]
pub enum HochschildOutcome {
    Complete(HochschildCohomology),
    Cut(IncompleteHochschildCohomology),
}

#[derive(Clone, Debug)]
struct DegreeInner {
    algebra: Arc<Algebra>,
    degree: usize,
    limits: BarLimits,
    layout: Layout,
    differential: DenseMat,
    cocycles: DenseMat,
    coboundaries: DenseMat,
    complement: DenseMat,
}

/// One exact Hochschild cohomology space.
#[derive(Clone, Debug)]
pub struct HochschildDegree(Arc<DegreeInner>);

impl HochschildDegree {
    accessor_methods! {
        /// The algebra whose normalized bar basis this degree uses.
        pub algebra() -> &Arc<Algebra> = |this| &this.0.algebra;
        /// The cohomological degree.
        pub degree() -> usize = |this| this.0.degree;
        /// The dimension of this Hochschild cohomology space.
        pub dim() -> usize = |this| this.0.complement.rows();
        /// The deterministic cochain coordinate basis.
        pub cochain_basis() -> &[BarCoordinate] = |this| &this.0.layout.coordinates;
        /// The RREF cocycle basis in cochain coordinates.
        pub cocycle_basis() -> &DenseMat = |this| &this.0.cocycles;
        /// The RREF coboundary basis in cochain coordinates.
        pub coboundary_basis() -> &DenseMat = |this| &this.0.coboundaries;
        /// The deterministic complement basis of coboundaries in cocycles.
        pub complement_basis() -> &DenseMat = |this| &this.0.complement;
        /// The row-action differential `D_n`.
        pub differential() -> &DenseMat = |this| &this.0.differential;
    }

    /// Decodes one tuple rank from the deterministic normalized bar basis.
    pub fn input_for_rank(&self, tuple_rank: usize) -> Option<BarInput> {
        if tuple_rank >= self.0.layout.offsets.len() - 1 {
            return None;
        }
        if self.0.degree == 0 {
            return Some(BarInput::Vertex(tuple_rank as u32));
        }
        let starts = tuple_starts(&self.0.algebra, self.0.degree);
        let mut tuple = Vec::with_capacity(self.0.degree);
        decode_tuple(
            &self.0.algebra,
            self.0.degree,
            tuple_rank,
            &starts,
            &mut tuple,
        );
        Some(BarInput::Tuple(tuple))
    }

    /// The zero class.
    pub fn zero_class(&self) -> HochschildClass {
        HochschildClass {
            degree: self.clone(),
            coordinates: vec![self.0.algebra.field().zero(); self.dim()],
        }
    }

    /// Builds a class from deterministic complement coordinates.
    pub fn class_from_coordinates(
        &self,
        coordinates: Vec<Fp>,
    ) -> Result<HochschildClass, HochschildError> {
        if coordinates.len() != self.dim() {
            return Err(HochschildError::CoordinateCount {
                expected: self.dim(),
                got: coordinates.len(),
            });
        }
        Ok(HochschildClass {
            degree: self.clone(),
            coordinates,
        })
    }

    /// Rebuilds through this degree and compares its stored data.
    pub fn verify(&self) -> bool {
        match build(&self.0.algebra, self.0.degree, self.0.limits) {
            Ok(HochschildOutcome::Complete(rebuilt)) => rebuilt
                .degree(self.0.degree)
                .is_some_and(|degree| same_degree(self, degree)),
            Ok(HochschildOutcome::Cut(_)) | Err(_) => false,
        }
    }
}

/// A Hochschild class in deterministic complement coordinates.
#[derive(Clone, Debug)]
pub struct HochschildClass {
    degree: HochschildDegree,
    coordinates: Vec<Fp>,
}

impl HochschildClass {
    accessor_methods! {
        /// The Hochschild degree this class belongs to.
        pub degree() -> &HochschildDegree = |this| &this.degree;
        /// The deterministic complement coordinates.
        pub coordinates() -> &[Fp] = |this| &this.coordinates;
        /// Whether this is the zero class.
        pub is_zero() -> bool = |this| this.coordinates.iter().all(|value| value.is_zero());
    }

    /// The representative cochain in the full coordinate basis.
    pub fn representative(&self) -> Vec<Fp> {
        row_times(
            &self.coordinates,
            &self.degree.0.complement,
            &self.degree.0.algebra.field(),
        )
    }

    /// Evaluates the representative on one normalized bar input.
    pub fn evaluate(&self, input: &BarInput) -> Result<Vec<(BasisIdx, Fp)>, HochschildError> {
        let inner = &self.degree.0;
        let rank = input_rank(&inner.algebra, inner.degree, input)?;
        let representative = self.representative();
        let start = inner.layout.offsets[rank];
        let end = inner.layout.offsets[rank + 1];
        Ok(inner.layout.coordinates[start..end]
            .iter()
            .enumerate()
            .filter_map(|(offset, coordinate)| {
                let value = representative[start + offset];
                (!value.is_zero()).then_some((coordinate.output, value))
            })
            .collect())
    }

    /// Rechecks the stored coordinate length and reconstructs its degree.
    pub fn verify(&self) -> bool {
        self.coordinates.len() == self.degree.dim() && self.degree.verify()
    }
}

#[derive(Clone, Debug)]
struct Layout {
    coordinates: Vec<BarCoordinate>,
    offsets: Vec<usize>,
}

#[derive(Clone, Debug)]
struct TupleOffsets {
    offsets: Vec<usize>,
    segments: Vec<(usize, u32, u32)>,
}

#[derive(Clone, Debug)]
struct Shape {
    tuples: usize,
    cochain_dim: usize,
    starts: Vec<usize>,
}

#[derive(Debug)]
struct Ledger {
    limits: BarLimits,
    requested_degree: usize,
    completed_degree_count: usize,
    work_units: u64,
    matrix_entries: usize,
    degrees: Vec<HochschildDegree>,
}

#[derive(Debug)]
struct Stop(BarBudgetDiagnostics);

type BuildResult<T> = Result<T, Stop>;

#[derive(Debug)]
enum BuildFailure {
    Stop(Stop),
    Defect(HochschildError),
}

type InnerResult<T> = Result<T, BuildFailure>;

from_variants!(BuildFailure { Stop => Stop });

impl Ledger {
    fn diagnostics(
        &self,
        reason: BarCutReason,
        stage: BarStage,
        degree: usize,
        used: u128,
        proposed: u128,
        ceiling: Option<u128>,
    ) -> Stop {
        Stop(BarBudgetDiagnostics {
            reason,
            stage,
            requested_degree: self.requested_degree,
            completed_degree_count: self.completed_degree_count,
            first_uncomputed_differential: degree,
            work_units: self.work_units,
            matrix_entries: self.matrix_entries,
            used,
            proposed,
            ceiling,
        })
    }

    fn overflow<T>(&self, degree: usize, stage: BarStage) -> BuildResult<T> {
        Err(self.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None))
    }

    fn checked_usize(
        &self,
        degree: usize,
        stage: BarStage,
        value: Option<usize>,
    ) -> BuildResult<usize> {
        value.ok_or_else(|| self.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None))
    }

    fn limit(
        &self,
        kind: BarLimit,
        stage: BarStage,
        degree: usize,
        used: u128,
        proposed: u128,
        ceiling: u128,
    ) -> BuildResult<()> {
        if proposed <= ceiling {
            Ok(())
        } else {
            Err(self.diagnostics(
                BarCutReason::Limit(kind),
                stage,
                degree,
                used,
                proposed,
                Some(ceiling),
            ))
        }
    }

    fn work(&mut self, degree: usize, stage: BarStage, units: u128) -> BuildResult<()> {
        let Some(units) = u64::try_from(units).ok() else {
            return self.overflow(degree, stage);
        };
        let Some(proposed) = self.work_units.checked_add(units) else {
            return self.overflow(degree, stage);
        };
        self.limit(
            BarLimit::WorkUnits,
            stage,
            degree,
            self.work_units.into(),
            proposed.into(),
            self.limits.max_work_units.into(),
        )?;
        self.work_units = proposed;
        Ok(())
    }

    fn per_degree(
        &self,
        degree: usize,
        stage: BarStage,
        kind: BarLimit,
        proposed: usize,
        ceiling: usize,
    ) -> BuildResult<()> {
        self.limit(kind, stage, degree, 0, proposed as u128, ceiling as u128)
    }

    fn shape(&self, degree: usize, tuples: usize, cochain_dim: usize) -> BuildResult<()> {
        self.per_degree(
            degree,
            BarStage::Shape,
            BarLimit::TensorTuples,
            tuples,
            self.limits.max_tensor_tuples,
        )?;
        self.per_degree(
            degree,
            BarStage::Shape,
            BarLimit::CochainDimension,
            cochain_dim,
            self.limits.max_cochain_dim,
        )
    }

    fn scratch(&self, degree: usize, stage: BarStage, entries: usize) -> BuildResult<()> {
        let Some(proposed) = self.matrix_entries.checked_add(entries) else {
            return self.overflow(degree, stage);
        };
        self.limit(
            BarLimit::MatrixEntries,
            stage,
            degree,
            self.matrix_entries as u128,
            proposed as u128,
            self.limits.max_matrix_entries as u128,
        )
    }

    fn work_elim(
        &mut self,
        degree: usize,
        stage: BarStage,
        rows: usize,
        cols: usize,
    ) -> BuildResult<()> {
        self.work(
            degree,
            stage,
            elimination_work(rows, cols, self, degree, stage)?,
        )
    }

    fn retain(&mut self, degree: usize, stage: BarStage, entries: usize) -> BuildResult<()> {
        self.scratch(degree, stage, entries)?;
        self.matrix_entries += entries;
        Ok(())
    }

    fn retain_matrix(
        &mut self,
        degree: usize,
        stage: BarStage,
        matrix: &DenseMat,
    ) -> BuildResult<()> {
        let budget = self.budget(degree, stage);
        let entries =
            budget.size(budget.product([matrix.rows() as u128, matrix.cols() as u128])?)?;
        self.retain(degree, stage, entries)
    }

    accessor_methods! {
        budget(degree: usize, stage: BarStage) -> Budget<'_> = |this| Budget {
            ledger: this,
            degree,
            stage,
        };
        scratch_u128(degree: usize, stage: BarStage, entries: u128) -> BuildResult<()> = |this|
            this.scratch(degree, stage, as_usize(this, degree, stage, entries)?);
    }
}

#[derive(Clone, Copy)]
struct Budget<'a> {
    ledger: &'a Ledger,
    degree: usize,
    stage: BarStage,
}

impl Budget<'_> {
    fn product<const N: usize>(&self, values: [u128; N]) -> BuildResult<u128> {
        checked_product(self.ledger, self.degree, self.stage, &values)
    }

    accessor_methods! {
        sum(left: u128, right: u128) -> BuildResult<u128> = |this|
            checked_add(this.ledger, this.degree, this.stage, left, right);
        size(value: u128) -> BuildResult<usize> = |this|
            as_usize(this.ledger, this.degree, this.stage, value);
    }
}

/// Computes normalized relative bar Hochschild cohomology through `max_degree`.
pub fn bar_hochschild(
    algebra: &Arc<Algebra>,
    max_degree: usize,
    limits: BarLimits,
) -> Result<HochschildOutcome, HochschildError> {
    build(algebra, max_degree, limits)
}

fn build(
    algebra: &Arc<Algebra>,
    max_degree: usize,
    limits: BarLimits,
) -> Result<HochschildOutcome, HochschildError> {
    let mut ledger = Ledger {
        limits,
        requested_degree: max_degree,
        completed_degree_count: 0,
        work_units: 0,
        matrix_entries: 0,
        degrees: Vec::new(),
    };
    match build_inner(algebra, max_degree, &mut ledger) {
        Ok(()) => Ok(HochschildOutcome::Complete(HochschildCohomology {
            algebra: algebra.clone(),
            requested_degree: max_degree,
            limits,
            degrees: std::mem::take(&mut ledger.degrees),
            diagnostics: BarRunDiagnostics {
                work_units: ledger.work_units,
                matrix_entries: ledger.matrix_entries,
            },
        })),
        Err(BuildFailure::Stop(Stop(diagnostics))) => {
            Ok(HochschildOutcome::Cut(IncompleteHochschildCohomology {
                algebra: algebra.clone(),
                requested_degree: max_degree,
                limits,
                degrees: std::mem::take(&mut ledger.degrees),
                diagnostics,
            }))
        }
        Err(BuildFailure::Defect(error)) => Err(error),
    }
}

fn build_inner(algebra: &Arc<Algebra>, max_degree: usize, ledger: &mut Ledger) -> InnerResult<()> {
    let field = algebra.field();
    let mut current = None;
    let mut shape = None;
    let mut offsets = None;
    let mut starts = Vec::new();
    let mut previous: Option<HochschildDegree> = None;
    for degree in 0..=max_degree {
        ledger.work(degree, BarStage::DegreeRecord, 1)?;
        if shape.is_none() {
            let measured = measure_identity_shape(algebra, ledger, degree)?;
            shape = Some(measured);
        }
        let mut current_shape = shape.take().expect("the first loop builds a shape");
        if degree == 0 {
            starts.push(std::mem::take(&mut current_shape.starts));
        }
        let next_degree = next_usize(ledger, degree, BarStage::Shape, degree)?;
        let next_power = advance_power(current.as_deref(), algebra, ledger, degree)?;
        let mut next_shape = measure_shape(algebra, &next_power, ledger, degree)?;
        starts.push(std::mem::take(&mut next_shape.starts));
        reserve_layout_work(&current_shape, &next_shape, degree, ledger)?;
        let current_offsets = offsets.take().map(Ok).unwrap_or_else(|| {
            build_tuple_offsets(algebra, degree, &current_shape, &starts, ledger)
        })?;
        let current_layout = build_layout(algebra, &current_shape, current_offsets);
        let next_offsets = build_tuple_offsets(algebra, next_degree, &next_shape, &starts, ledger)?;
        let differential = build_differential(
            algebra,
            degree,
            &current_shape,
            &current_layout,
            &next_offsets.offsets,
            &starts,
            ledger,
        )?;

        if let Some(previous) = &previous {
            check_square(
                &previous.0.differential,
                &differential,
                &field,
                degree,
                ledger,
            )?;
        }
        let cocycles = cocycles(&differential, &field, degree, ledger)?;
        let coboundaries = match &previous {
            Some(previous) => coboundaries(&previous.0.differential, &field, degree, ledger)?,
            None => DenseMat::zero(0, current_shape.cochain_dim),
        };
        let complement = complement(&cocycles, &coboundaries, &field, degree, ledger)?;
        let degree_value = HochschildDegree(Arc::new(DegreeInner {
            algebra: algebra.clone(),
            degree,
            limits: ledger.limits,
            layout: current_layout,
            differential,
            cocycles,
            coboundaries,
            complement,
        }));
        ledger.degrees.push(degree_value.clone());
        ledger.completed_degree_count += 1;
        previous = Some(degree_value);
        current = Some(next_power);
        shape = Some(next_shape);
        offsets = Some(next_offsets);
    }
    Ok(())
}

fn square_work(n: usize, ledger: &Ledger, degree: usize) -> BuildResult<u128> {
    let budget = ledger.budget(degree, BarStage::Shape);
    let square = budget.product([n as u128, n as u128])?;
    let cubic = budget.product([square, n as u128])?;
    budget.sum(cubic, square)
}

fn advance_power(
    current: Option<&[Vec<usize>]>,
    algebra: &Algebra,
    ledger: &mut Ledger,
    degree: usize,
) -> BuildResult<Vec<Vec<usize>>> {
    let vertices = algebra.quiver().num_vertices() as usize;
    ledger.work(
        degree,
        BarStage::Shape,
        square_work(vertices, ledger, degree)?,
    )?;
    let budget = ledger.budget(degree, BarStage::Shape);
    let entries = budget.product([vertices as u128, vertices as u128])?;
    let _ = budget.size(entries)?;
    let mut next = vec![vec![0; vertices]; vertices];
    for (source, next_row) in next.iter_mut().enumerate() {
        for (target, entry) in next_row.iter_mut().enumerate() {
            let mut total = 0u128;
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
            *entry = budget.size(total)?;
        }
    }
    Ok(next)
}

fn measure_shape(
    algebra: &Algebra,
    radical_power: &[Vec<usize>],
    ledger: &mut Ledger,
    degree: usize,
) -> BuildResult<Shape> {
    let budget = ledger.budget(degree, BarStage::Shape);
    let mut tuples = 0u128;
    let mut cochain_dim = 0u128;
    let mut starts = Vec::with_capacity(radical_power.len());
    for (source, row) in radical_power.iter().enumerate() {
        let mut from_source = 0u128;
        for (target, &count) in row.iter().enumerate() {
            tuples = budget.sum(tuples, count as u128)?;
            from_source = budget.sum(from_source, count as u128)?;
            let addend = budget.product([
                count as u128,
                algebra.paths_between(source as u32, target as u32).len() as u128,
            ])?;
            cochain_dim = budget.sum(cochain_dim, addend)?;
        }
        starts.push(budget.size(from_source)?);
    }
    let tuples = budget.size(tuples)?;
    let cochain_dim = budget.size(cochain_dim)?;
    ledger.shape(degree, tuples, cochain_dim)?;
    Ok(Shape {
        tuples,
        cochain_dim,
        starts,
    })
}

fn measure_identity_shape(
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

fn reserve_layout_work(
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

fn build_tuple_offsets(
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
            Ok::<(), Stop>(())
        },
    )?;
    offsets.push(offset);
    debug_assert_eq!(offset, shape.cochain_dim);
    debug_assert_eq!(offsets.len(), capacity);
    Ok(TupleOffsets { offsets, segments })
}

fn build_layout(algebra: &Algebra, shape: &Shape, tuple_offsets: TupleOffsets) -> Layout {
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

fn build_differential(
    algebra: &Algebra,
    degree: usize,
    shape: &Shape,
    source_layout: &Layout,
    target_offsets: &[usize],
    starts: &[Vec<usize>],
    ledger: &mut Ledger,
) -> BuildResult<DenseMat> {
    let stage = BarStage::Differential;
    let target_dim = *target_offsets
        .last()
        .expect("a tuple offset table has its final offset");
    let target_degree = next_usize(ledger, degree, stage, degree)?;
    let term_count = next_usize(ledger, target_degree, stage, target_degree)?;
    let algebra_dimension = next_usize(ledger, degree, stage, algebra.dim())?;
    let entries = {
        let budget = ledger.budget(degree, stage);
        budget.size(budget.product([shape.cochain_dim as u128, target_dim as u128])?)?
    };
    ledger.scratch(degree, stage, entries)?;
    ledger.work(degree, stage, entries as u128)?;
    let target_tuples = ledger.checked_usize(degree, stage, target_offsets.len().checked_sub(1))?;
    let term_work = ledger.budget(degree, stage).product([
        shape.cochain_dim as u128,
        target_tuples as u128,
        term_count as u128,
        algebra_dimension as u128,
    ])?;
    ledger.work(degree, stage, term_work)?;

    let field = algebra.field();
    let mut differential = DenseMat::zero(shape.cochain_dim, target_dim);
    if shape.cochain_dim == 0 || target_dim == 0 {
        ledger.retain(degree, stage, entries)?;
        return Ok(differential);
    }
    walk_tuples(
        algebra,
        degree,
        shape.tuples,
        starts,
        |source_rank, source, source_start, _source_end| {
            let row_start = source_layout.offsets[source_rank];
            for row in row_start..source_layout.offsets[source_rank + 1] {
                let output = source_layout.coordinates[row].output;
                walk_tuples(
                    algebra,
                    target_degree,
                    target_offsets.len() - 1,
                    starts,
                    |target_rank, target, target_start, target_end| {
                        let coordinate = TargetCoordinate {
                            algebra,
                            offsets: target_offsets,
                            tuple_rank: target_rank,
                            source: target_start,
                            target: target_end,
                            field: &field,
                        };
                        if degree == 0 {
                            if source_start == target_end {
                                coordinate.add_product(
                                    &mut differential,
                                    row,
                                    &algebra.mul_basis(target[0], output),
                                    false,
                                );
                            }
                            if source_start == target_start {
                                coordinate.add_product(
                                    &mut differential,
                                    row,
                                    &algebra.mul_basis(output, target[0]),
                                    true,
                                );
                            }
                            return Ok::<(), ()>(());
                        }
                        if source == &target[1..] {
                            coordinate.add_product(
                                &mut differential,
                                row,
                                &algebra.mul_basis(target[0], output),
                                false,
                            );
                        }
                        for i in 1..=degree {
                            for &(middle, coefficient) in
                                &algebra.mul_basis(target[i - 1], target[i])
                            {
                                if matches_middle(source, target, i, middle) {
                                    coordinate.add(
                                        &mut differential,
                                        row,
                                        output,
                                        signed(coefficient, i % 2 == 1, &field),
                                    );
                                }
                            }
                        }
                        if source == &target[..degree] {
                            coordinate.add_product(
                                &mut differential,
                                row,
                                &algebra.mul_basis(output, target[degree]),
                                target_degree % 2 == 1,
                            );
                        }
                        Ok::<(), ()>(())
                    },
                )
                .expect("the differential callback cannot fail");
            }
            Ok::<(), ()>(())
        },
    )
    .expect("the differential callback cannot fail");
    ledger.retain(degree, stage, entries)?;
    Ok(differential)
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
        product: &[(BasisIdx, Fp)],
        negative: bool,
    ) {
        for &(output, value) in product {
            self.add(matrix, row, output, signed(value, negative, self.field));
        }
    }
}

fn check_square(
    left: &DenseMat,
    right: &DenseMat,
    field: &PrimeField,
    degree: usize,
    ledger: &mut Ledger,
) -> InnerResult<()> {
    let work = ledger.budget(degree, BarStage::Square).product([
        left.rows() as u128,
        left.cols() as u128,
        right.cols() as u128,
    ])?;
    ledger.work(degree, BarStage::Square, work)?;
    for row in 0..left.rows() {
        for column in 0..right.cols() {
            let mut sum = field.zero();
            for middle in 0..left.cols() {
                sum = field.add(
                    sum,
                    field.mul(left.get(row, middle), right.get(middle, column)),
                );
            }
            if !sum.is_zero() {
                return Err(BuildFailure::Defect(HochschildError::DifferentialSquare {
                    degree,
                }));
            }
        }
    }
    Ok(())
}

fn cocycles(
    differential: &DenseMat,
    field: &PrimeField,
    degree: usize,
    ledger: &mut Ledger,
) -> BuildResult<DenseMat> {
    let (rows, cols) = (differential.rows(), differential.cols());
    let stage = BarStage::Cocycles;
    let budget = ledger.budget(degree, stage);
    let scratch = budget.sum(
        budget.product([2, rows as u128, cols as u128])?,
        budget.product([rows as u128, rows as u128])?,
    )?;
    ledger.scratch_u128(degree, stage, scratch)?;
    let kernel_product = budget.product([rows as u128, cols as u128])?;
    let elimination = elimination_work(cols, rows, ledger, degree, stage)?;
    let square = budget.product([rows as u128, rows as u128])?;
    let kernel_work = budget.sum(kernel_product, budget.sum(elimination, square)?)?;
    ledger.work(degree, stage, kernel_work)?;
    let raw = differential.left_kernel_basis(field);
    ledger.work_elim(degree, stage, raw.rows(), raw.cols())?;
    let cocycles = raw.into_row_space_basis(field);
    ledger.retain_matrix(degree, stage, &cocycles)?;
    Ok(cocycles)
}

fn coboundaries(
    differential: &DenseMat,
    field: &PrimeField,
    degree: usize,
    ledger: &mut Ledger,
) -> BuildResult<DenseMat> {
    let stage = BarStage::Coboundaries;
    let budget = ledger.budget(degree, stage);
    let entries =
        budget.size(budget.product([differential.rows() as u128, differential.cols() as u128])?)?;
    let scratch = budget.product([2, entries as u128])?;
    ledger.scratch_u128(degree, stage, scratch)?;
    ledger.work_elim(degree, stage, differential.rows(), differential.cols())?;
    let coboundaries = differential.row_space_basis(field);
    ledger.retain_matrix(degree, stage, &coboundaries)?;
    Ok(coboundaries)
}

fn complement(
    cocycles: &DenseMat,
    coboundaries: &DenseMat,
    field: &PrimeField,
    degree: usize,
    ledger: &mut Ledger,
) -> BuildResult<DenseMat> {
    let stage = BarStage::Complement;
    let rows = ledger.checked_usize(
        degree,
        stage,
        cocycles.rows().checked_add(coboundaries.rows()),
    )?;
    let width = cocycles.cols();
    let budget = ledger.budget(degree, stage);
    let scratch_rows = budget.sum(
        rows.min(width) as u128,
        budget.product([2, cocycles.rows() as u128])?,
    )?;
    let scratch = budget.product([scratch_rows, width as u128])?;
    ledger.scratch_u128(degree, stage, scratch)?;
    ledger.work_elim(degree, stage, rows, width)?;
    let complement = deterministic_complement(cocycles, coboundaries, field);
    ledger.retain_matrix(degree, stage, &complement)?;
    Ok(complement)
}

fn elimination_work(
    rows: usize,
    cols: usize,
    ledger: &Ledger,
    degree: usize,
    stage: BarStage,
) -> BuildResult<u128> {
    let budget = ledger.budget(degree, stage);
    let pivot = rows.min(cols) as u128;
    let inner = budget.sum(1, budget.product([2, cols as u128])?)?;
    let next_cols = next_usize(ledger, degree, stage, cols)?;
    let updates = budget.product([2, rows as u128, next_cols as u128])?;
    let per_pivot = budget.sum(inner, updates)?;
    let body = budget.product([pivot, per_pivot])?;
    budget.sum(budget.product([rows as u128, cols as u128])?, body)
}

fn checked_product(
    ledger: &Ledger,
    degree: usize,
    stage: BarStage,
    values: &[u128],
) -> BuildResult<u128> {
    values.iter().try_fold(1u128, |total, &value| {
        total.checked_mul(value).ok_or_else(|| {
            ledger.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None)
        })
    })
}

fn checked_add(
    ledger: &Ledger,
    degree: usize,
    stage: BarStage,
    left: u128,
    right: u128,
) -> BuildResult<u128> {
    left.checked_add(right)
        .ok_or_else(|| ledger.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None))
}

fn as_usize(ledger: &Ledger, degree: usize, stage: BarStage, value: u128) -> BuildResult<usize> {
    usize::try_from(value)
        .map_err(|_| ledger.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, value, None))
}

fn next_usize(ledger: &Ledger, degree: usize, stage: BarStage, value: usize) -> BuildResult<usize> {
    value
        .checked_add(1)
        .ok_or_else(|| ledger.diagnostics(BarCutReason::SizeOverflow, stage, degree, 0, 0, None))
}

fn tuple_starts(algebra: &Algebra, degree: usize) -> Vec<Vec<usize>> {
    let vertices = algebra.quiver().num_vertices() as usize;
    let mut starts = vec![vec![1; vertices]];
    for _ in 0..degree {
        let previous = starts.last().expect("degree zero starts exist");
        let next = (0..vertices)
            .map(|source| {
                algebra.paths_from(source as u32)[1..]
                    .iter()
                    .try_fold(0usize, |total, &word| {
                        total.checked_add(previous[algebra.basis()[word].target() as usize])
                    })
                    .expect("a completed tuple count fits usize")
            })
            .collect();
        starts.push(next);
    }
    starts
}

fn select_word(
    algebra: &Algebra,
    candidates: impl Iterator<Item = BasisIdx>,
    remaining: &[usize],
    rank: &mut usize,
) -> Option<BasisIdx> {
    for word in candidates {
        let block = remaining[algebra.basis()[word].target() as usize];
        if *rank < block {
            return Some(word);
        }
        *rank -= block;
    }
    None
}

fn decode_tuple(
    algebra: &Algebra,
    degree: usize,
    tuple_rank: usize,
    starts: &[Vec<usize>],
    tuple: &mut Vec<BasisIdx>,
) {
    let first_word = algebra.quiver().num_vertices() as usize;
    tuple.clear();
    let mut suffix_rank = tuple_rank;
    for position in 0..degree {
        let remaining = &starts[degree - position - 1];
        let word = if let Some(&previous) = tuple.last() {
            let source = algebra.basis()[previous].target();
            select_word(
                algebra,
                algebra.paths_from(source)[1..].iter().copied(),
                remaining,
                &mut suffix_rank,
            )
        } else {
            select_word(
                algebra,
                first_word..algebra.dim(),
                remaining,
                &mut suffix_rank,
            )
        };
        tuple.push(word.expect("a measured tuple rank decodes"));
    }
}

fn walk_tuples<E>(
    algebra: &Algebra,
    degree: usize,
    tuples: usize,
    starts: &[Vec<usize>],
    mut callback: impl FnMut(usize, &[BasisIdx], u32, u32) -> Result<(), E>,
) -> Result<(), E> {
    let vertices = algebra.quiver().num_vertices();
    if degree == 0 {
        for vertex in 0..vertices {
            callback(vertex as usize, &[], vertex, vertex)?;
        }
        return Ok(());
    }
    let mut tuple: Vec<BasisIdx> = Vec::with_capacity(degree);
    for tuple_rank in 0..tuples {
        decode_tuple(algebra, degree, tuple_rank, starts, &mut tuple);
        let first = &algebra.basis()[tuple[0]];
        let last = &algebra.basis()[*tuple.last().expect("positive-degree tuple")];
        callback(tuple_rank, &tuple, first.source(), last.target())?;
    }
    Ok(())
}

fn input_rank(
    algebra: &Algebra,
    degree: usize,
    input: &BarInput,
) -> Result<usize, HochschildError> {
    match (degree, input) {
        (0, BarInput::Vertex(vertex)) => {
            if *vertex >= algebra.quiver().num_vertices() {
                Err(HochschildError::VertexOutOfRange {
                    vertex: *vertex,
                    num_vertices: algebra.quiver().num_vertices(),
                })
            } else {
                Ok(*vertex as usize)
            }
        }
        (0, BarInput::Tuple(words)) => Err(HochschildError::WrongInputDegree {
            expected: 0,
            got: words.len(),
        }),
        (_, BarInput::Vertex(_)) => Err(HochschildError::WrongInputDegree {
            expected: degree,
            got: 0,
        }),
        (_, BarInput::Tuple(words)) => {
            if words.len() != degree {
                return Err(HochschildError::WrongInputDegree {
                    expected: degree,
                    got: words.len(),
                });
            }
            let vertices = algebra.quiver().num_vertices() as usize;
            for (position, &word) in words.iter().enumerate() {
                if word >= algebra.dim() {
                    return Err(HochschildError::BasisOutOfRange {
                        position,
                        index: word,
                    });
                }
                if word < vertices {
                    return Err(HochschildError::TrivialInput { position });
                }
                if position > 0
                    && algebra.basis()[words[position - 1]].target()
                        != algebra.basis()[word].source()
                {
                    return Err(HochschildError::NonComposableInput {
                        position: position - 1,
                    });
                }
            }
            let starts = tuple_starts(algebra, degree);
            let tuples = starts[degree]
                .iter()
                .try_fold(0usize, |total, &count| total.checked_add(count))
                .expect("a completed tuple count fits usize");
            let mut tuple = Vec::with_capacity(degree);
            for rank in 0..tuples {
                decode_tuple(algebra, degree, rank, &starts, &mut tuple);
                if tuple.as_slice() == words.as_slice() {
                    return Ok(rank);
                }
            }
            panic!("a validated tuple occurs in the streamed basis")
        }
    }
}

fn row_times(row: &[Fp], matrix: &DenseMat, field: &PrimeField) -> Vec<Fp> {
    let mut output = vec![field.zero(); matrix.cols()];
    for (source, &coefficient) in row.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        for (target, value) in output.iter_mut().enumerate() {
            *value = field.add(*value, field.mul(coefficient, matrix.get(source, target)));
        }
    }
    output
}

fn same_degree(left: &HochschildDegree, right: &HochschildDegree) -> bool {
    let (left, right) = (&left.0, &right.0);
    same_algebra(&left.algebra, &right.algebra)
        && left.degree == right.degree
        && left.limits == right.limits
        && left.layout.coordinates == right.layout.coordinates
        && left.layout.offsets == right.layout.offsets
        && left.differential == right.differential
        && left.cocycles == right.cocycles
        && left.coboundaries == right.coboundaries
        && left.complement == right.complement
}

fn same_complete(left: &HochschildCohomology, right: &HochschildCohomology) -> bool {
    same_algebra(&left.algebra, &right.algebra)
        && left.requested_degree == right.requested_degree
        && left.limits == right.limits
        && left.diagnostics == right.diagnostics
        && same_degrees(&left.degrees, &right.degrees)
}

fn same_cut(left: &IncompleteHochschildCohomology, right: &IncompleteHochschildCohomology) -> bool {
    same_algebra(&left.algebra, &right.algebra)
        && left.requested_degree == right.requested_degree
        && left.limits == right.limits
        && left.diagnostics == right.diagnostics
        && same_degrees(&left.degrees, &right.degrees)
}

fn same_degrees(left: &[HochschildDegree], right: &[HochschildDegree]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(a, b)| same_degree(a, b))
}

fn same_algebra(left: &Arc<Algebra>, right: &Arc<Algebra>) -> bool {
    Arc::ptr_eq(left, right)
        || (left.field() == right.field()
            && left.quiver() == right.quiver()
            && left.basis() == right.basis()
            && (0..left.dim())
                .all(|p| (0..left.dim()).all(|q| left.mul_basis(p, q) == right.mul_basis(p, q))))
}

#[cfg(test)]
mod tests {
    use std::env;
    use std::process::Command;

    use super::*;
    use crate::algebra::{
        Algebra, commutative_square, dual_numbers, linear_an, path_algebra, truncated_poly,
    };
    use crate::completion::CompletionLimits;
    use crate::quiver::{ArrowId, Quiver};
    use crate::relation::{Presentation, Relation};

    fn field(p: u64) -> PrimeField {
        PrimeField::new(p).unwrap()
    }

    fn generous() -> BarLimits {
        BarLimits {
            max_tensor_tuples: 10_000,
            max_cochain_dim: 100_000,
            max_matrix_entries: 10_000_000,
            max_work_units: 1_000_000_000,
        }
    }

    fn complete(outcome: HochschildOutcome) -> HochschildCohomology {
        match outcome {
            HochschildOutcome::Complete(value) => value,
            HochschildOutcome::Cut(cut) => panic!("unexpected cut: {:?}", cut.diagnostics()),
        }
    }

    fn add_entry(matrix: &mut DenseMat, row: usize, column: usize, value: Fp, field: &PrimeField) {
        matrix.set(row, column, field.add(matrix.get(row, column), value));
    }

    fn full_signed(value: Fp, negative: bool, field: &PrimeField) -> Fp {
        if negative { field.neg(value) } else { value }
    }

    fn full_tuples(dimension: usize, degree: usize) -> Vec<Vec<BasisIdx>> {
        let mut tuples = vec![Vec::new()];
        for _ in 0..degree {
            let mut next = Vec::with_capacity(tuples.len() * dimension);
            for tuple in tuples {
                for basis in 0..dimension {
                    let mut extended = tuple.clone();
                    extended.push(basis);
                    next.push(extended);
                }
            }
            tuples = next;
        }
        tuples
    }

    fn full_rank(tuple: &[BasisIdx], dimension: usize) -> usize {
        tuple
            .iter()
            .fold(0, |rank, &basis| rank * dimension + basis)
    }

    fn add_full_product(
        matrix: &mut DenseMat,
        row: usize,
        target_rank: usize,
        dimension: usize,
        product: &[(BasisIdx, Fp)],
        negative: bool,
        field: &PrimeField,
    ) {
        for &(output, coefficient) in product {
            add_entry(
                matrix,
                row,
                target_rank * dimension + output,
                full_signed(coefficient, negative, field),
                field,
            );
        }
    }

    fn full_differential(algebra: &Algebra, degree: usize) -> DenseMat {
        let field = algebra.field();
        let dimension = algebra.dim();
        let source = full_tuples(dimension, degree);
        let target = full_tuples(dimension, degree + 1);
        let mut differential = DenseMat::zero(source.len() * dimension, target.len() * dimension);
        for (target_rank, tuple) in target.iter().enumerate() {
            for output in 0..dimension {
                if degree == 0 {
                    add_full_product(
                        &mut differential,
                        output,
                        target_rank,
                        dimension,
                        &algebra.mul_basis(tuple[0], output),
                        false,
                        &field,
                    );
                    add_full_product(
                        &mut differential,
                        output,
                        target_rank,
                        dimension,
                        &algebra.mul_basis(output, tuple[0]),
                        true,
                        &field,
                    );
                    continue;
                }
                let first = full_rank(&tuple[1..], dimension) * dimension + output;
                add_full_product(
                    &mut differential,
                    first,
                    target_rank,
                    dimension,
                    &algebra.mul_basis(tuple[0], output),
                    false,
                    &field,
                );
                for i in 1..=degree {
                    let mut shortened = Vec::with_capacity(degree);
                    shortened.extend_from_slice(&tuple[..i - 1]);
                    for &(middle, coefficient) in &algebra.mul_basis(tuple[i - 1], tuple[i]) {
                        shortened.push(middle);
                        shortened.extend_from_slice(&tuple[i + 1..]);
                        let row = full_rank(&shortened, dimension) * dimension + output;
                        add_entry(
                            &mut differential,
                            row,
                            target_rank * dimension + output,
                            full_signed(coefficient, i % 2 == 1, &field),
                            &field,
                        );
                        shortened.truncate(i - 1);
                    }
                }
                let last = full_rank(&tuple[..degree], dimension) * dimension + output;
                add_full_product(
                    &mut differential,
                    last,
                    target_rank,
                    dimension,
                    &algebra.mul_basis(output, tuple[degree]),
                    (degree + 1) % 2 == 1,
                    &field,
                );
            }
        }
        differential
    }

    fn full_bar_dimensions(algebra: &Algebra, max_degree: usize) -> Vec<usize> {
        let field = algebra.field();
        let mut dimensions = Vec::with_capacity(max_degree + 1);
        let mut previous: Option<DenseMat> = None;
        for degree in 0..=max_degree {
            let differential = full_differential(algebra, degree);
            if let Some(previous) = &previous {
                assert!(
                    previous
                        .mul(&differential, &field)
                        .entries_u64()
                        .iter()
                        .flatten()
                        .all(|&x| x == 0)
                );
            }
            let cocycles = differential.left_kernel_basis(&field);
            let coboundaries =
                previous.map_or(0, |matrix: DenseMat| matrix.row_space_basis(&field).rows());
            dimensions.push(cocycles.rows() - coboundaries);
            previous = Some(differential);
        }
        dimensions
    }

    fn center_dimension(algebra: &Algebra) -> usize {
        let field = algebra.field();
        let dimension = algebra.dim();
        let mut equations = DenseMat::zero(dimension, dimension * dimension);
        for central in 0..dimension {
            for basis in 0..dimension {
                for &(output, coefficient) in &algebra.mul_basis(central, basis) {
                    add_entry(
                        &mut equations,
                        central,
                        basis * dimension + output,
                        coefficient,
                        &field,
                    );
                }
                for &(output, coefficient) in &algebra.mul_basis(basis, central) {
                    add_entry(
                        &mut equations,
                        central,
                        basis * dimension + output,
                        field.neg(coefficient),
                        &field,
                    );
                }
            }
        }
        equations.left_kernel_basis(&field).rows()
    }

    fn outer_derivation_dimension(algebra: &Algebra) -> usize {
        let field = algebra.field();
        let dimension = algebra.dim();
        let mut equations =
            DenseMat::zero(dimension * dimension, dimension * dimension * dimension);
        for left in 0..dimension {
            for right in 0..dimension {
                for &(middle, coefficient) in &algebra.mul_basis(left, right) {
                    for output in 0..dimension {
                        add_entry(
                            &mut equations,
                            middle * dimension + output,
                            (left * dimension + right) * dimension + output,
                            coefficient,
                            &field,
                        );
                    }
                }
                for output in 0..dimension {
                    for &(product, coefficient) in &algebra.mul_basis(output, right) {
                        add_entry(
                            &mut equations,
                            left * dimension + output,
                            (left * dimension + right) * dimension + product,
                            field.neg(coefficient),
                            &field,
                        );
                    }
                    for &(product, coefficient) in &algebra.mul_basis(left, output) {
                        add_entry(
                            &mut equations,
                            right * dimension + output,
                            (left * dimension + right) * dimension + product,
                            field.neg(coefficient),
                            &field,
                        );
                    }
                }
            }
        }
        let derivations = equations.left_kernel_basis(&field);
        let mut inner = DenseMat::zero(dimension, dimension * dimension);
        for generator in 0..dimension {
            for input in 0..dimension {
                for &(output, coefficient) in &algebra.mul_basis(input, generator) {
                    add_entry(
                        &mut inner,
                        generator,
                        input * dimension + output,
                        coefficient,
                        &field,
                    );
                }
                for &(output, coefficient) in &algebra.mul_basis(generator, input) {
                    add_entry(
                        &mut inner,
                        generator,
                        input * dimension + output,
                        field.neg(coefficient),
                        &field,
                    );
                }
            }
        }
        let inner = inner.row_space_basis(&field);
        assert!(
            inner
                .mul(&equations, &field)
                .entries_u64()
                .iter()
                .flatten()
                .all(|&value| value == 0)
        );
        assert!(inner.rows() <= derivations.rows());
        derivations.rows() - inner.rows()
    }

    fn inhomogeneous_dual_numbers(field: PrimeField) -> Arc<Algebra> {
        let quiver = Quiver::new(1, &[(0, 0)]).unwrap();
        let relation = Relation::new(
            &quiver,
            field,
            vec![
                (field.one(), vec![ArrowId(0), ArrowId(0)]),
                (field.one(), vec![ArrowId(0), ArrowId(0), ArrowId(0)]),
            ],
        )
        .unwrap();
        let nilpotence = Relation::new(
            &quiver,
            field,
            vec![(
                field.one(),
                vec![ArrowId(0), ArrowId(0), ArrowId(0), ArrowId(0)],
            )],
        )
        .unwrap();
        Algebra::new(
            Presentation::new(quiver, field, vec![relation, nilpotence]).unwrap(),
            &CompletionLimits::default(),
        )
        .unwrap()
    }

    fn bar_record() -> String {
        let exact = complete(bar_hochschild(&commutative_square(field(5)), 2, generous()).unwrap());
        let degrees: Vec<_> = exact
            .degrees()
            .iter()
            .map(|degree| {
                (
                    degree.dim(),
                    degree.cochain_basis(),
                    degree.differential().entries_u64(),
                    degree.cocycle_basis().entries_u64(),
                    degree.coboundary_basis().entries_u64(),
                    degree.complement_basis().entries_u64(),
                )
            })
            .collect();
        let limits = BarLimits {
            max_work_units: 0,
            ..generous()
        };
        let HochschildOutcome::Cut(cut) =
            bar_hochschild(&dual_numbers(field(5)), 0, limits).unwrap()
        else {
            panic!("zero work must cut")
        };
        format!("{degrees:?}|{:?}", cut.diagnostics())
    }

    #[test]
    fn semisimple_algebra_has_only_degree_zero_cohomology() {
        let quiver = Quiver::new(2, &[]).unwrap();
        let algebra = path_algebra(quiver, field(5)).unwrap();
        let result = complete(bar_hochschild(&algebra, 2, generous()).unwrap());
        assert_eq!(
            result
                .degrees()
                .iter()
                .map(HochschildDegree::dim)
                .collect::<Vec<_>>(),
            [2, 0, 0]
        );
        assert!(result.verify());
    }

    #[test]
    fn dual_numbers_pin_the_characteristic_two_sign() {
        let f5 = complete(bar_hochschild(&dual_numbers(field(5)), 3, generous()).unwrap());
        let f2 = complete(bar_hochschild(&dual_numbers(field(2)), 3, generous()).unwrap());
        assert_eq!(
            f5.degrees()
                .iter()
                .map(HochschildDegree::dim)
                .collect::<Vec<_>>(),
            [2, 1, 1, 1]
        );
        assert_eq!(
            f2.degrees()
                .iter()
                .map(HochschildDegree::dim)
                .collect::<Vec<_>>(),
            [2, 2, 2, 2]
        );
    }

    #[test]
    fn a_work_cut_keeps_an_exact_prefix() {
        let algebra = dual_numbers(field(5));
        let degree_zero = complete(bar_hochschild(&algebra, 0, generous()).unwrap());
        let mut limits = generous();
        limits.max_work_units = degree_zero.diagnostics().work_units;
        let HochschildOutcome::Cut(cut) = bar_hochschild(&algebra, 1, limits).unwrap() else {
            panic!("degree one must exceed the degree-zero work ceiling")
        };
        assert_eq!(cut.completed_degrees().len(), 1);
        assert_eq!(cut.diagnostics().stage, BarStage::DegreeRecord);
        assert_eq!(
            cut.completed_degrees()[0].dim(),
            degree_zero.degrees()[0].dim()
        );
        assert!(cut.verify());
    }

    #[test]
    fn classes_evaluate_on_vertex_and_tuple_inputs() {
        let algebra = dual_numbers(field(5));
        let result = complete(bar_hochschild(&algebra, 1, generous()).unwrap());
        let one = algebra.field().one();
        let h0 = result
            .degree(0)
            .unwrap()
            .class_from_coordinates(vec![one, algebra.field().zero()])
            .unwrap();
        assert_eq!(h0.evaluate(&BarInput::Vertex(0)).unwrap().len(), 1);
        let h1 = result
            .degree(1)
            .unwrap()
            .class_from_coordinates(vec![one])
            .unwrap();
        assert_eq!(h1.evaluate(&BarInput::Tuple(vec![1])).unwrap().len(), 1);
        assert!(matches!(
            h1.evaluate(&BarInput::Tuple(vec![0])),
            Err(HochschildError::TrivialInput { .. })
        ));
        assert!(matches!(
            h1.evaluate(&BarInput::Tuple(vec![1, 1])),
            Err(HochschildError::WrongInputDegree { .. })
        ));
        assert!(matches!(
            h1.evaluate(&BarInput::Tuple(vec![2])),
            Err(HochschildError::BasisOutOfRange { .. })
        ));
        assert!(matches!(
            h0.evaluate(&BarInput::Vertex(1)),
            Err(HochschildError::VertexOutOfRange { .. })
        ));
        let a2 = complete(bar_hochschild(&linear_an(2, field(5)), 2, generous()).unwrap());
        assert!(matches!(
            a2.degree(2)
                .unwrap()
                .zero_class()
                .evaluate(&BarInput::Tuple(vec![2, 2])),
            Err(HochschildError::NonComposableInput { .. })
        ));
    }

    #[test]
    fn nonmonomial_differentials_square_to_zero() {
        let result =
            complete(bar_hochschild(&commutative_square(field(5)), 2, generous()).unwrap());
        assert!(result.verify());
    }

    #[test]
    fn normalized_bar_agrees_with_full_bar_and_low_degree_checks() {
        let fixtures: Vec<(&str, Arc<Algebra>, usize)> = vec![
            (
                "F5 squared",
                path_algebra(Quiver::new(2, &[]).unwrap(), field(5)).unwrap(),
                2,
            ),
            ("A2", linear_an(2, field(5)), 2),
            ("dual numbers", dual_numbers(field(5)), 3),
            ("x cubed", truncated_poly(3, field(5)).unwrap(), 2),
            ("commutative square", commutative_square(field(5)), 1),
            ("inhomogeneous", inhomogeneous_dual_numbers(field(5)), 2),
        ];
        for (name, algebra, max_degree) in fixtures {
            let normalized = complete(bar_hochschild(&algebra, max_degree, generous()).unwrap());
            let dimensions: Vec<_> = normalized
                .degrees()
                .iter()
                .map(HochschildDegree::dim)
                .collect();
            assert_eq!(
                dimensions,
                full_bar_dimensions(&algebra, max_degree),
                "{name}"
            );
            assert_eq!(dimensions[0], center_dimension(&algebra), "{name}: center");
            if max_degree > 0 {
                assert_eq!(
                    dimensions[1],
                    outer_derivation_dimension(&algebra),
                    "{name}: derivations"
                );
            }
        }
    }

    #[test]
    fn hand_derived_fixtures_pin_dimensions() {
        for vertices in [1, 2, 3] {
            let algebra = path_algebra(Quiver::new(vertices, &[]).unwrap(), field(5)).unwrap();
            let result = complete(bar_hochschild(&algebra, 2, generous()).unwrap());
            assert_eq!(
                result
                    .degrees()
                    .iter()
                    .map(HochschildDegree::dim)
                    .collect::<Vec<_>>(),
                [vertices as usize, 0, 0]
            );
        }
        for vertices in [1, 2, 3] {
            let result =
                complete(bar_hochschild(&linear_an(vertices, field(5)), 2, generous()).unwrap());
            assert_eq!(
                result
                    .degrees()
                    .iter()
                    .map(HochschildDegree::dim)
                    .collect::<Vec<_>>(),
                [1, 0, 0]
            );
        }
        let x_cubed =
            complete(bar_hochschild(&truncated_poly(3, field(5)).unwrap(), 2, generous()).unwrap());
        assert_eq!(
            x_cubed
                .degrees()
                .iter()
                .map(HochschildDegree::dim)
                .collect::<Vec<_>>(),
            [3, 2, 2]
        );
    }

    #[test]
    fn every_limit_cuts_before_its_first_unaffordable_operation() {
        let algebra = dual_numbers(field(5));
        let tensor = BarLimits {
            max_tensor_tuples: 0,
            ..generous()
        };
        let cochains = BarLimits {
            max_cochain_dim: 0,
            ..generous()
        };
        let matrix = BarLimits {
            max_matrix_entries: 0,
            ..generous()
        };
        let work = BarLimits {
            max_work_units: 0,
            ..generous()
        };
        for (limits, limit, stage) in [
            (tensor, BarLimit::TensorTuples, BarStage::Shape),
            (cochains, BarLimit::CochainDimension, BarStage::Shape),
            (matrix, BarLimit::MatrixEntries, BarStage::Differential),
            (work, BarLimit::WorkUnits, BarStage::DegreeRecord),
        ] {
            let HochschildOutcome::Cut(cut) = bar_hochschild(&algebra, 0, limits).unwrap() else {
                panic!("a zero ceiling must cut")
            };
            let diagnostics = cut.diagnostics();
            assert_eq!(diagnostics.reason, BarCutReason::Limit(limit));
            assert_eq!(diagnostics.stage, stage);
            assert_eq!(diagnostics.completed_degree_count, 0);
            assert_eq!(diagnostics.first_uncomputed_differential, 0);
            assert_eq!(diagnostics.ceiling, Some(0));
            assert!(diagnostics.proposed > diagnostics.used);
            assert!(cut.verify());
        }
    }

    #[test]
    fn matrix_limit_counts_left_kernel_scratch_for_zero_columns() {
        let algebra = path_algebra(Quiver::new(2, &[]).unwrap(), field(5)).unwrap();
        let limits = BarLimits {
            max_matrix_entries: 3,
            ..generous()
        };
        let HochschildOutcome::Cut(cut) = bar_hochschild(&algebra, 0, limits).unwrap() else {
            panic!("the kernel scratch must exceed the ceiling")
        };
        assert_eq!(
            cut.diagnostics().reason,
            BarCutReason::Limit(BarLimit::MatrixEntries)
        );
        assert_eq!(cut.diagnostics().stage, BarStage::Cocycles);
        assert_eq!(cut.diagnostics().used, 0);
        assert_eq!(cut.diagnostics().proposed, 4);
        assert!(cut.verify());
    }

    #[test]
    fn checked_size_arithmetic_cuts_without_wrapping() {
        let ledger = Ledger {
            limits: generous(),
            requested_degree: 0,
            completed_degree_count: 0,
            work_units: 0,
            matrix_entries: 0,
            degrees: Vec::new(),
        };
        for Stop(diagnostics) in [
            checked_product(&ledger, 0, BarStage::Shape, &[u128::MAX, 2])
                .expect_err("product overflow must cut"),
            checked_add(&ledger, 0, BarStage::Shape, u128::MAX, 1)
                .expect_err("sum overflow must cut"),
            as_usize(&ledger, 0, BarStage::Shape, u128::MAX).expect_err("usize overflow must cut"),
            next_usize(&ledger, 0, BarStage::Shape, usize::MAX)
                .expect_err("increment overflow must cut"),
        ] {
            assert_eq!(diagnostics.reason, BarCutReason::SizeOverflow);
            assert_eq!(diagnostics.stage, BarStage::Shape);
            assert!(diagnostics.ceiling.is_none());
        }
    }

    #[test]
    fn fresh_equal_algebras_compare_structurally() {
        let left = dual_numbers(field(5));
        let right = dual_numbers(field(5));
        assert!(!Arc::ptr_eq(&left, &right));
        let left = complete(bar_hochschild(&left, 2, generous()).unwrap());
        let right = complete(bar_hochschild(&right, 2, generous()).unwrap());
        assert!(same_complete(&left, &right));
        assert!(left.verify());
        assert!(right.verify());

        let limits = BarLimits {
            max_work_units: 0,
            ..generous()
        };
        let HochschildOutcome::Cut(left) =
            bar_hochschild(&dual_numbers(field(5)), 0, limits).unwrap()
        else {
            panic!("zero work must cut")
        };
        let HochschildOutcome::Cut(right) =
            bar_hochschild(&dual_numbers(field(5)), 0, limits).unwrap()
        else {
            panic!("zero work must cut")
        };
        assert!(same_cut(&left, &right));
    }

    #[test]
    fn verification_rejects_mutated_bar_records() {
        let algebra = dual_numbers(field(5));
        let result = complete(bar_hochschild(&algebra, 1, generous()).unwrap());

        let mut differential = result.clone();
        let inner = Arc::make_mut(&mut differential.degrees[0].0);
        inner.differential.set(0, 0, algebra.field().one());
        assert!(!differential.verify());

        let mut basis = result.clone();
        Arc::make_mut(&mut basis.degrees[0].0).layout.coordinates[0].output = 1;
        assert!(!basis.verify());

        let mut tuple_rank = result.clone();
        Arc::make_mut(&mut tuple_rank.degrees[1].0)
            .layout
            .coordinates[0]
            .tuple_rank = 1;
        assert!(!tuple_rank.verify());

        let mut offsets = result.clone();
        Arc::make_mut(&mut offsets.degrees[1].0).layout.offsets[1] -= 1;
        assert!(!offsets.verify());

        let mut cocycles = result.clone();
        Arc::make_mut(&mut cocycles.degrees[0].0)
            .cocycles
            .set(0, 0, algebra.field().zero());
        assert!(!cocycles.verify());

        let mut dimension = result.clone();
        let inner = Arc::make_mut(&mut dimension.degrees[0].0);
        inner.complement = DenseMat::zero(inner.complement.rows() - 1, inner.complement.cols());
        assert!(!dimension.verify());

        let mut requested_degree = result.clone();
        requested_degree.requested_degree += 1;
        assert!(!requested_degree.verify());

        let mut limits = result.clone();
        limits.limits.max_tensor_tuples += 1;
        assert!(!limits.verify());

        let mut degree_index = result.clone();
        Arc::make_mut(&mut degree_index.degrees[0].0).degree += 1;
        assert!(!degree_index.verify());

        let mut diagnostics = result;
        diagnostics.diagnostics.work_units += 1;
        assert!(!diagnostics.verify());

        let algebra = linear_an(2, field(5));
        let result = complete(bar_hochschild(&algebra, 1, generous()).unwrap());

        let mut coboundaries = result.clone();
        let coboundary = &mut Arc::make_mut(&mut coboundaries.degrees[1].0).coboundaries;
        let (row, column) = (0..coboundary.rows())
            .flat_map(|row| (0..coboundary.cols()).map(move |column| (row, column)))
            .find(|&(row, column)| !coboundary.get(row, column).is_zero())
            .expect("A2 has a nonzero degree-one coboundary");
        coboundary.set(row, column, algebra.field().zero());
        assert!(!coboundaries.verify());

        let mut sign = result.clone();
        let differential = &mut Arc::make_mut(&mut sign.degrees[0].0).differential;
        let (row, column) = (0..differential.rows())
            .flat_map(|row| (0..differential.cols()).map(move |column| (row, column)))
            .find(|&(row, column)| !differential.get(row, column).is_zero())
            .expect("A2 has a nonzero degree-zero differential");
        let value = differential.get(row, column);
        differential.set(row, column, algebra.field().neg(value));
        assert!(!sign.verify());

        let algebra = truncated_poly(3, field(5)).unwrap();
        let result = complete(bar_hochschild(&algebra, 1, generous()).unwrap());
        let product_entry = result.degree(1).unwrap().differential().get(5, 2);
        assert_eq!(product_entry, algebra.field().neg(algebra.field().one()));
        let mut product = result;
        Arc::make_mut(&mut product.degrees[1].0)
            .differential
            .set(5, 2, algebra.field().zero());
        assert!(!product.verify());
    }

    #[test]
    fn tuple_ranks_follow_normal_basis_lexicographic_order() {
        let algebra = truncated_poly(3, field(5)).unwrap();
        assert_eq!(input_rank(&algebra, 2, &BarInput::Tuple(vec![1, 1])), Ok(0));
        assert_eq!(input_rank(&algebra, 2, &BarInput::Tuple(vec![1, 2])), Ok(1));
        assert_eq!(input_rank(&algebra, 2, &BarInput::Tuple(vec![2, 1])), Ok(2));
        assert_eq!(input_rank(&algebra, 2, &BarInput::Tuple(vec![2, 2])), Ok(3));
        let result = complete(bar_hochschild(&algebra, 2, generous()).unwrap());
        let degree = result.degree(2).unwrap();
        assert_eq!(degree.algebra().basis(), algebra.basis());
        assert_eq!(degree.input_for_rank(0), Some(BarInput::Tuple(vec![1, 1])));
        assert_eq!(degree.input_for_rank(1), Some(BarInput::Tuple(vec![1, 2])));
        assert_eq!(degree.input_for_rank(2), Some(BarInput::Tuple(vec![2, 1])));
        assert_eq!(degree.input_for_rank(3), Some(BarInput::Tuple(vec![2, 2])));
        assert_eq!(degree.input_for_rank(4), None);
        assert_eq!(degree.input_for_rank(usize::MAX), None);

        let algebra = linear_an(3, field(5));
        let result = complete(bar_hochschild(&algebra, 2, generous()).unwrap());
        let degree = result.degree(2).unwrap();
        assert_eq!(degree.input_for_rank(0), Some(BarInput::Tuple(vec![3, 4])));
        assert_eq!(degree.input_for_rank(1), None);
    }

    const BAR_CHILD_ENV: &str = "AUSLANDER_HOCHSCHILD_CHILD";
    const BAR_MARKER: &str = "hochschild-record:";

    #[test]
    fn fresh_process_child_prints_bar_record() {
        if env::var(BAR_CHILD_ENV).is_ok() {
            println!("{BAR_MARKER}{}", bar_record());
        }
    }

    fn fresh_bar_record() -> String {
        let output = Command::new(env::current_exe().expect("path of this test binary"))
            .args([
                "--exact",
                "hochschild::tests::fresh_process_child_prints_bar_record",
                "--nocapture",
            ])
            .env(BAR_CHILD_ENV, "1")
            .output()
            .expect("spawn a fresh test process");
        assert!(output.status.success(), "fresh test process failed");
        String::from_utf8(output.stdout)
            .expect("test output is UTF-8")
            .lines()
            .find_map(|line| line.find(BAR_MARKER).map(|index| line[index..].to_owned()))
            .expect("fresh test process printed the bar record")
    }

    #[test]
    fn fresh_processes_reproduce_bar_bases_and_cut_diagnostics() {
        let first = fresh_bar_record();
        let second = fresh_bar_record();
        assert_eq!(first, second);
        assert_eq!(first, format!("{BAR_MARKER}{}", bar_record()));
    }

    #[test]
    fn verification_rejects_a_mutated_cut_record() {
        let limits = BarLimits {
            max_work_units: 0,
            ..generous()
        };
        let HochschildOutcome::Cut(mut cut) =
            bar_hochschild(&dual_numbers(field(5)), 0, limits).unwrap()
        else {
            panic!("zero work must cut")
        };
        assert!(cut.verify());
        cut.diagnostics.proposed += 1;
        assert!(!cut.verify());
    }
}
