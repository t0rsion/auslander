use std::sync::Arc;

use crate::algebra::{Algebra, BasisIdx};
use crate::field::Fp;
use crate::linalg::DenseMat;

use super::bar::{Layout, bar_hochschild, decode_tuple, input_rank, tuple_starts};
use super::limits::{
    BarBudgetDiagnostics, BarCoordinate, BarInput, BarLimits, BarRunDiagnostics, HochschildError,
};
use super::verification::{row_times, same_complete, same_cut, same_degree};

/// Exact Hochschild cohomology through the requested degree.
#[derive(Clone, Debug)]
pub struct HochschildCohomology {
    pub(super) algebra: Arc<Algebra>,
    pub(super) requested_degree: usize,
    pub(super) limits: BarLimits,
    pub(super) degrees: Vec<HochschildDegree>,
    pub(super) diagnostics: BarRunDiagnostics,
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
            bar_hochschild(&this.algebra, this.requested_degree, this.limits),
            Ok(HochschildOutcome::Complete(rebuilt)) if same_complete(this, &rebuilt)
        );
    }
}

/// The exact prefix retained by a typed bar resource cut.
#[derive(Clone, Debug)]
pub struct IncompleteHochschildCohomology {
    pub(super) algebra: Arc<Algebra>,
    pub(super) requested_degree: usize,
    pub(super) limits: BarLimits,
    pub(super) degrees: Vec<HochschildDegree>,
    pub(super) diagnostics: BarBudgetDiagnostics,
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
            bar_hochschild(&this.algebra, this.requested_degree, this.limits),
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
pub(super) struct DegreeInner {
    pub(super) algebra: Arc<Algebra>,
    pub(super) degree: usize,
    pub(super) limits: BarLimits,
    pub(super) layout: Layout,
    pub(super) differential: DenseMat,
    pub(super) cocycles: DenseMat,
    pub(super) coboundaries: DenseMat,
    pub(super) complement: DenseMat,
}

/// One exact Hochschild cohomology space.
#[derive(Clone, Debug)]
pub struct HochschildDegree(pub(super) Arc<DegreeInner>);

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
        match bar_hochschild(&self.0.algebra, self.0.degree, self.0.limits) {
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
