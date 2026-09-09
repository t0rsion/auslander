//! Split target presentations from exceptional tilting complexes.

use std::sync::{Arc, OnceLock};

use crate::algebra::Algebra;
use crate::certificate::Certificate;
use crate::field::{Fp, PrimeField};
use crate::homotopy::{ChainMap, ChainMapError, HomotopyHom, HomotopyHomQuotient};
use crate::linalg::DenseMat;
use crate::target::{
    CoordinateAlgebra, CoordinateTargetData, CoordinateTargetOutcome, TargetCutReason, TargetError,
    TargetLimits, TargetWork, recover_coordinate_target, verify_coordinate_target_data,
};
use crate::tilting_complex::CertifiedTiltingComplex;

#[derive(Clone, Debug)]
struct EndBlock {
    source: usize,
    target: usize,
    offset: usize,
    quotient: HomotopyHomQuotient,
}

/// The checked coordinate algebra `End_K(T)`.
#[derive(Clone)]
pub struct HomotopyEndomorphismAlgebra {
    tilting: CertifiedTiltingComplex,
    field: PrimeField,
    blocks: Vec<EndBlock>,
    basis_blocks: Vec<(usize, usize)>,
    ids: Vec<Vec<Fp>>,
    one: Vec<Fp>,
    radical: DenseMat,
    table: OnceLock<Vec<Vec<Fp>>>,
}

impl std::fmt::Debug for HomotopyEndomorphismAlgebra {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("HomotopyEndomorphismAlgebra")
            .field("summands", &self.tilting.candidate().len())
            .field("dimension", &self.dim())
            .field("radical_dimension", &self.radical.rows())
            .finish()
    }
}

impl HomotopyEndomorphismAlgebra {
    /// Builds every degree-zero homotopy Hom block in summand order.
    pub fn new(
        tilting: &CertifiedTiltingComplex,
    ) -> Result<HomotopyEndomorphismAlgebra, ChainMapError> {
        let count = tilting.candidate().len();
        let field = tilting.candidate().algebra().field();
        let mut blocks = Vec::with_capacity(count * count);
        let mut basis_blocks = Vec::new();
        let mut offset = 0usize;
        for source in 0..count {
            for target in 0..count {
                let quotient = HomotopyHom::new(
                    tilting.candidate().summands()[source].complex(),
                    tilting.candidate().summands()[target].complex(),
                    0,
                )?
                .quotient()?;
                for local in 0..quotient.dim() {
                    basis_blocks.push((blocks.len(), local));
                }
                let dimension = quotient.dim();
                blocks.push(EndBlock {
                    source,
                    target,
                    offset,
                    quotient,
                });
                offset += dimension;
            }
        }
        let dim = offset;
        let mut ids = Vec::with_capacity(count);
        for index in 0..count {
            let block = &blocks[index * count + index];
            let identity = ChainMap::identity(tilting.candidate().summands()[index].complex());
            let (coordinates, _) = block.quotient.reduce(&identity)?;
            let mut row = vec![field.zero(); dim];
            row[block.offset..block.offset + coordinates.len()].copy_from_slice(&coordinates);
            ids.push(row);
        }
        let mut one = vec![field.zero(); dim];
        for id in &ids {
            for (value, coefficient) in one.iter_mut().zip(id) {
                *value = field.add(*value, *coefficient);
            }
        }
        let radical_rows: Vec<Vec<Fp>> = basis_blocks
            .iter()
            .enumerate()
            .filter(|(_, (block, _))| blocks[*block].source != blocks[*block].target)
            .map(|(basis, _)| {
                let mut row = vec![field.zero(); dim];
                row[basis] = field.one();
                row
            })
            .collect();
        let radical = DenseMat::from_rows_with_cols(&radical_rows, dim);
        Ok(HomotopyEndomorphismAlgebra {
            tilting: tilting.clone(),
            field,
            blocks,
            basis_blocks,
            ids,
            one,
            radical,
            table: OnceLock::new(),
        })
    }

    accessor_methods! {
        /// The certified tilting complex.
        pub tilting() -> &CertifiedTiltingComplex = |this| &this.tilting;
        /// The base prime field.
        pub field() -> PrimeField = |this| this.field;
        /// The dimension of `End_K(T)`.
        pub dim() -> usize = |this| this.basis_blocks.len();
        /// Coordinates of the identity.
        pub one() -> &[Fp] = |this| &this.one;
        /// One primitive idempotent row per ordered summand.
        pub idempotents() -> &[Vec<Fp>] = |this| &this.ids;
        /// The exact radical basis in the exceptional domain.
        pub radical_basis() -> &DenseMat = |this| &this.radical;
    }

    /// The dimension of `Hom_K(T_source, T_target)`.
    pub fn block_dimension(&self, source: usize, target: usize) -> Option<usize> {
        let count = self.tilting.candidate().len();
        (source < count && target < count)
            .then(|| self.blocks[source * count + target].quotient.dim())
    }

    fn structure_table(&self) -> &Vec<Vec<Fp>> {
        self.table.get_or_init(|| {
            let dim = self.dim();
            let mut table = vec![vec![self.field.zero(); dim]; dim * dim];
            for (left, &(left_block, left_local)) in self.basis_blocks.iter().enumerate() {
                for (right, &(right_block, right_local)) in self.basis_blocks.iter().enumerate() {
                    let left_data = &self.blocks[left_block];
                    let right_data = &self.blocks[right_block];
                    if left_data.target != right_data.source {
                        continue;
                    }
                    let product = left_data
                        .quotient
                        .representative(&unit(self.field, left_data.quotient.dim(), left_local))
                        .then(&right_data.quotient.representative(&unit(
                            self.field,
                            right_data.quotient.dim(),
                            right_local,
                        )))
                        .expect("composable homotopy classes have matching middle terms");
                    let output = &self.blocks
                        [left_data.source * self.tilting.candidate().len() + right_data.target];
                    let coordinates = output
                        .quotient
                        .reduce(&product)
                        .expect("a composite reduces in its homotopy Hom block")
                        .0;
                    table[left * dim + right][output.offset..output.offset + coordinates.len()]
                        .copy_from_slice(&coordinates);
                }
            }
            table
        })
    }

    /// Multiplies coordinates in left-to-right chain-map order.
    pub fn multiply(&self, left: &[Fp], right: &[Fp]) -> Vec<Fp> {
        assert_eq!(left.len(), self.dim(), "left coordinate count");
        assert_eq!(right.len(), self.dim(), "right coordinate count");
        let mut output = vec![self.field.zero(); self.dim()];
        let table = self.structure_table();
        for (i, &a) in left.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, &b) in right.iter().enumerate() {
                if b.is_zero() {
                    continue;
                }
                let scale = self.field.mul(a, b);
                for (value, &coefficient) in output.iter_mut().zip(&table[i * self.dim() + j]) {
                    *value = self.field.add(*value, self.field.mul(scale, coefficient));
                }
            }
        }
        output
    }

    /// Recomputes every block, identity, radical row, and basis product.
    pub fn verify(&self) -> bool {
        if !self.tilting.verify() {
            return false;
        }
        let Ok(rebuilt) = HomotopyEndomorphismAlgebra::new(&self.tilting) else {
            return false;
        };
        self.dim() == rebuilt.dim()
            && self.ids == rebuilt.ids
            && self.radical == rebuilt.radical
            && (0..self.dim()).all(|left| {
                (0..self.dim()).all(|right| {
                    self.structure_table()[left * self.dim() + right]
                        == rebuilt.structure_table()[left * self.dim() + right]
                })
            })
    }
}

fn unit(field: PrimeField, length: usize, index: usize) -> Vec<Fp> {
    let mut row = vec![field.zero(); length];
    row[index] = field.one();
    row
}

impl CoordinateAlgebra for HomotopyEndomorphismAlgebra {
    fn field(&self) -> PrimeField {
        self.field
    }

    fn dim(&self) -> usize {
        self.dim()
    }

    fn radical_basis(&self) -> &DenseMat {
        &self.radical
    }

    fn radical_dim(&self) -> usize {
        self.radical.rows()
    }

    fn one(&self) -> &[Fp] {
        &self.one
    }

    fn multiply(&self, left: &[Fp], right: &[Fp]) -> Vec<Fp> {
        self.multiply(left, right)
    }
}

/// A checked target cut for one tilting complex.
#[derive(Clone, Debug)]
pub struct ComplexTargetCut {
    tilting: CertifiedTiltingComplex,
    limits: TargetLimits,
    reason: TargetCutReason,
}

impl ComplexTargetCut {
    accessor_methods! {
        /// The certified tilting complex.
        pub tilting() -> &CertifiedTiltingComplex = |this| &this.tilting;
        /// The effective target limits.
        pub limits() -> &TargetLimits = |this| &this.limits;
        /// The first rejected reservation.
        pub reason() -> &TargetCutReason = |this| &this.reason;
    }

    /// Repeats target recovery and requires the same cut.
    pub fn verify(&self) -> bool {
        matches!(
            present_complex_target(&self.tilting, &self.limits),
            Ok(ComplexTargetOutcome::Cut(cut)) if cut.reason == self.reason
        )
    }
}

/// A verified presentation of `End_K(T)^op`.
#[derive(Clone)]
pub struct VerifiedComplexTargetPresentation {
    tilting: CertifiedTiltingComplex,
    limits: TargetLimits,
    endo: HomotopyEndomorphismAlgebra,
    data: CoordinateTargetData,
}

impl std::fmt::Debug for VerifiedComplexTargetPresentation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("VerifiedComplexTargetPresentation")
            .field("endomorphism_dimension", &self.endo.dim())
            .field("target_dimension", &self.data.target.dim())
            .field("arrows", &self.data.target.quiver().num_arrows())
            .finish()
    }
}

impl VerifiedComplexTargetPresentation {
    accessor_methods! {
        /// The certified source tilting complex.
        pub tilting() -> &CertifiedTiltingComplex = |this| &this.tilting;
        /// The homotopy endomorphism algebra.
        pub endo() -> &HomotopyEndomorphismAlgebra = |this| &this.endo;
        /// The recovered algebra `End_K(T)^op`.
        pub target() -> &Arc<Algebra> = |this| &this.data.target;
        /// The target completion certificate.
        pub completion_certificate() -> &Certificate = |this| &this.data.completion;
        /// Primitive idempotent images in `End_K(T)`.
        pub idempotent_images() -> &DenseMat = |this| &this.data.idempotent_images;
        /// Target arrow images in `End_K(T)`.
        pub arrow_images() -> &DenseMat = |this| &this.data.arrow_images;
        /// Target normal-word images in `End_K(T)`.
        pub normal_word_images() -> &DenseMat = |this| &this.data.normal_word_images;
        /// The inverse normal-word coordinate map.
        pub normal_word_preimages() -> &DenseMat = |this| &this.data.normal_word_preimages;
        /// The radical nilpotency index.
        pub radical_nilpotency_index() -> usize = |this| this.data.radical_nilpotency_index;
        /// Exact target-recovery work.
        pub work() -> TargetWork = |this| this.data.work;
        /// The effective target limits.
        pub limits() -> &TargetLimits = |this| &this.limits;
    }

    /// Rebuilds the homotopy algebra and independently checks the target map.
    pub fn verify(&self) -> bool {
        let Ok(endo) = HomotopyEndomorphismAlgebra::new(&self.tilting) else {
            return false;
        };
        endo.verify()
            && verify_coordinate_target_data(&endo, endo.idempotents(), &self.limits, &self.data)
    }
}

/// Target recovery completed or stopped at a typed limit.
#[derive(Clone, Debug)]
pub enum ComplexTargetOutcome {
    /// A complete verified target presentation.
    Presented(Box<VerifiedComplexTargetPresentation>),
    /// A target budget stopped recovery.
    Cut(Box<ComplexTargetCut>),
}

/// Recovers `End_K(T)^op` from degree-zero homotopy Hom quotients.
pub fn present_complex_target(
    tilting: &CertifiedTiltingComplex,
    limits: &TargetLimits,
) -> Result<ComplexTargetOutcome, ComplexTargetError> {
    if !tilting.verify() {
        return Err(ComplexTargetError::InvalidTilting);
    }
    let endo = HomotopyEndomorphismAlgebra::new(tilting)?;
    match recover_coordinate_target(&endo, endo.idempotents(), limits)? {
        CoordinateTargetOutcome::Presented(data) => {
            let verified = VerifiedComplexTargetPresentation {
                tilting: tilting.clone(),
                limits: limits.clone(),
                endo,
                data: *data,
            };
            if !verified.verify() {
                return Err(ComplexTargetError::Defect {
                    reason: "the complex-target verifier rejected the presentation".to_string(),
                });
            }
            Ok(ComplexTargetOutcome::Presented(Box::new(verified)))
        }
        CoordinateTargetOutcome::Cut(reason) => {
            Ok(ComplexTargetOutcome::Cut(Box::new(ComplexTargetCut {
                tilting: tilting.clone(),
                limits: limits.clone(),
                reason,
            })))
        }
    }
}

/// A complex target failed construction or verification.
#[derive(Clone, Debug)]
pub enum ComplexTargetError {
    /// The supplied tilting certificate failed verification.
    InvalidTilting,
    /// A homotopy Hom block failed construction.
    Chain(ChainMapError),
    /// The shared target engine rejected the coordinate algebra.
    Target(TargetError),
    /// An internal cross-check failed.
    Defect { reason: String },
}

display_error! { ComplexTargetError {
    Self::InvalidTilting => "tilting-complex certificate does not verify";
    Self::Chain(error) => "homotopy endomorphism block failed: {error}";
    Self::Target(error) => "complex target failed: {error}";
    Self::Defect { reason } => "complex target cross-check failed: {reason}";
} }

error_source! { ComplexTargetError {
    Self::Chain(error) => Some(error),
    Self::Target(error) => Some(error),
    _ => None,
} }

from_variants! { ComplexTargetError {
    ChainMapError => Chain,
    TargetError => Target,
} }
