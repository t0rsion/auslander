//! Split bound quiver presentations of tilting target algebras.
//!
//! For a classical tilting right module `T`, the right-module target is
//! `End_A(T)^op`. A successful value stores a checked presentation of that
//! opposite algebra and the coordinate map back to `End_A(T)`.

use std::sync::Arc;

use crate::algebra::{Algebra, AlgebraBuildError};
use crate::basic::{BasicDecomposition, BasicError};
use crate::certificate::{Certificate, RelationData};
use crate::completion::{CompletionLimits, TruncationDiagnostics};
use crate::decompose::{Decomposition, Split, decompose_with_root_endo};
use crate::endo::EndoAlgebra;
use crate::field::{Fp, PrimeField};
use crate::homspace::{deterministic_complement, row_times};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::quiver::{ArrowId, PathWord, Quiver};
use crate::relation::{Presentation, Relation, RelationError};
use crate::tilting::{ClassicalTiltingModule, ClassicalTiltingResult, TiltingLimits};
use crate::verify::verify_certificate;

/// Independent limits for one target-presentation run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetLimits {
    /// Maximum dimension of `End_A(T)` before its multiplication table is built.
    pub max_endo_dimension: usize,
    /// Maximum calls to [`EndoAlgebra::multiply`] while building radical
    /// powers and their idempotent corners.
    pub max_radical_products: usize,
    /// Maximum enumerated paths of lengths `2..=lambda`.
    pub max_paths: usize,
    /// Maximum nonzero coefficients copied into the relation list.
    pub max_relation_terms: usize,
    /// Limits for the final bound quiver completion.
    pub completion: CompletionLimits,
}

impl Default for TargetLimits {
    fn default() -> TargetLimits {
        TargetLimits {
            max_endo_dimension: 4096,
            max_radical_products: 1_000_000,
            max_paths: 1_000_000,
            max_relation_terms: 1_000_000,
            completion: CompletionLimits::default(),
        }
    }
}

/// The stage at which a target budget rejected its next reservation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TargetCutStage {
    /// The endomorphism algebra exceeds `max_endo_dimension`.
    EndoDimension,
    /// Multiplication from `J^power` by `J` while building `J^(power + 1)`.
    RadicalPower { power: usize },
    /// Projection of `J^power` into the corner for a target arrow pair.
    RadicalCorner {
        source: u32,
        target: u32,
        power: usize,
    },
    /// Enumeration of paths at the named length.
    Paths { length: usize },
    /// Copying a kernel row into a relation for one endpoint pair.
    Relations { source: u32, target: u32 },
}

/// One rejected reservation against a target budget.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetBudgetCut {
    pub stage: TargetCutStage,
    /// Units already reserved before the rejection.
    pub used: usize,
    /// Units requested by the rejected reservation.
    pub requested: usize,
    /// The corresponding limit.
    pub limit: usize,
}

/// Why a target construction stopped at a caller limit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TargetCutReason {
    /// A radical-product, path, or relation-term budget stopped the run.
    Budget(TargetBudgetCut),
    /// The existing completion engine stopped the run.
    Completion(TruncationDiagnostics),
}

/// A self-verifying target cut with its complete input and limits.
#[derive(Clone, Debug)]
pub struct TargetPresentationCut {
    source: Module,
    tilting_limits: TiltingLimits,
    limits: TargetLimits,
    reason: TargetCutReason,
}

impl TargetPresentationCut {
    accessor_methods! {
        /// The source tilting module.
        pub source() -> &Module = |this| &this.source;
        /// The tilting limits carried by the successful source classification.
        pub tilting_limits() -> TiltingLimits = |this| this.tilting_limits;
        /// The target limits that stopped recovery.
        pub limits() -> &TargetLimits = |this| &this.limits;
        /// The first rejected reservation or completion cut.
        pub reason() -> &TargetCutReason = |this| &this.reason;
    }

    /// Repeats target recovery and requires the same cut reason.
    pub fn verify(&self) -> bool {
        let Ok(ClassicalTiltingResult::Tilting(tilting)) =
            ClassicalTiltingModule::classify(&self.source, self.tilting_limits)
        else {
            return false;
        };
        if !tilting.verify() {
            return false;
        }
        matches!(
            present_target(&tilting, &self.limits),
            Ok(TargetPresentationOutcome::Cut(cut)) if cut.reason == self.reason
        )
    }
}

/// Exact work completed by a successful target recovery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TargetWork {
    /// Dimension of `End_A(T)` before its multiplication table is built.
    pub endo_dimension: usize,
    /// Radical-power and corner products.
    pub radical_products: usize,
    /// Enumerated paths of lengths `2..=lambda`.
    pub paths: usize,
    /// Nonzero coefficients in the input relation list.
    pub relation_terms: usize,
}

/// Exact evidence that the tilting target is not split over the base field.
#[derive(Clone, Debug)]
pub struct NonSplitTarget {
    module: Module,
    tilting_limits: TiltingLimits,
    limits: TargetLimits,
    summand: usize,
    residue_degree: usize,
}

impl NonSplitTarget {
    accessor_methods! {
        /// The tilting module whose target is not split.
        pub module() -> &Module = |this| &this.module;
        /// The target limits used to find the non-split summand.
        pub limits() -> &TargetLimits = |this| &this.limits;
        /// The first non-split summand in deterministic decomposition order.
        pub summand() -> usize = |this| this.summand;
        /// The exact degree of that summand's residue field over the base field.
        pub residue_degree() -> usize = |this| this.residue_degree;
    }

    /// Recomputes the tilting classification and the first non-split summand.
    pub fn verify(&self) -> bool {
        let Ok(ClassicalTiltingResult::Tilting(tilting)) =
            ClassicalTiltingModule::classify(&self.module, self.tilting_limits)
        else {
            return false;
        };
        tilting.verify()
            && matches!(
                present_target(&tilting, &self.limits),
                Ok(TargetPresentationOutcome::Unsupported(value))
                    if value.summand == self.summand
                        && value.residue_degree == self.residue_degree
            )
    }
}

/// Rejected target input or a failed internal cross-check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TargetError {
    /// The basic decomposition could not be certified.
    Basic(BasicError),
    /// A recovered relation was rejected.
    Relation(RelationError),
    /// The final algebra constructor failed for a reason other than a cut.
    Algebra(AlgebraBuildError),
    /// A checked size calculation overflowed before allocation.
    SizeOverflow { stage: TargetCutStage },
    /// An invariant implied by the construction failed.
    Defect { reason: String },
}

display_error! { TargetError {
    Self::Basic(error) => "basic layer: {error}";
    Self::Relation(error) => "relation rejected: {error}";
    Self::Algebra(error) => "target algebra rejected: {error}";
    Self::SizeOverflow { stage } => "target size overflowed at {stage:?}";
    Self::Defect { reason } => "internal cross-check failed: {reason}";
} }

error_source! { TargetError {
    Self::Basic(error) => Some(error),
    Self::Relation(error) => Some(error),
    Self::Algebra(error) => Some(error),
    _ => None,
} }

from_variants! { TargetError {
    BasicError => Basic,
    RelationError => Relation,
} }

/// A verified presentation of `End_A(T)^op` and its map into `End_A(T)`.
#[derive(Clone)]
pub struct VerifiedTargetPresentation {
    source: Module,
    tilting_limits: TiltingLimits,
    limits: TargetLimits,
    target: Arc<Algebra>,
    endo: EndoAlgebra,
    split: Split,
    completion: Certificate,
    idempotent_images: DenseMat,
    arrow_images: DenseMat,
    normal_word_images: DenseMat,
    normal_word_preimages: DenseMat,
    radical_nilpotency_index: usize,
    work: TargetWork,
}

debug_fields!(VerifiedTargetPresentation |this| {
    "source_dim_vector" => this.source.dim_vector();
    "target_dim" => this.target.dim();
    "arrows" => this.target.quiver().num_arrows();
    "radical_nilpotency_index" => this.radical_nilpotency_index;
});

impl VerifiedTargetPresentation {
    accessor_methods! {
        /// The source tilting module `T`.
        pub source() -> &Module = |this| &this.source;
        /// The checked target algebra `End_A(T)^op`.
        pub target() -> &Arc<Algebra> = |this| &this.target;
        /// `End_A(T)` in the coordinates used by every stored image row.
        pub endo() -> &EndoAlgebra = |this| &this.endo;
        /// The verified decomposition that fixes target vertex order.
        pub split() -> &Split = |this| &this.split;
        /// Primitive idempotent images in `End_A(T)`, one row per target vertex.
        pub idempotent_images() -> &DenseMat = |this| &this.idempotent_images;
        /// Arrow images in `End_A(T)`, one row per target arrow.
        pub arrow_images() -> &DenseMat = |this| &this.arrow_images;
        /// Target normal-word images in `End_A(T)`, one row per target basis word.
        pub normal_word_images() -> &DenseMat = |this| &this.normal_word_images;
        /// The inverse normal-word image matrix, from `End_A(T)` to target coordinates.
        pub normal_word_preimages() -> &DenseMat = |this| &this.normal_word_preimages;
        /// The independently verified completion certificate for the target.
        pub completion_certificate() -> &Certificate = |this| &this.completion;
        /// The least `lambda` with `rad(End_A(T))^lambda = 0`.
        pub radical_nilpotency_index() -> usize = |this| this.radical_nilpotency_index;
        /// The limits used to build this value.
        pub limits() -> &TargetLimits = |this| &this.limits;
        /// Exact work used before successful completion.
        pub work() -> TargetWork = |this| this.work;
    }

    /// Maps target algebra coordinates to coordinates in `End_A(T)^op`.
    ///
    /// The underlying vector space is `End_A(T)`, so the returned row uses
    /// [`VerifiedTargetPresentation::endo`] coordinates.
    ///
    /// # Panics
    /// Panics unless `coordinates` has length [`Algebra::dim`] for the target.
    pub fn map_coordinates(&self, coordinates: &[Fp]) -> Vec<Fp> {
        assert_eq!(
            coordinates.len(),
            self.target.dim(),
            "map_coordinates: target coordinate count"
        );
        row_times(coordinates, &self.normal_word_images, &self.target.field())
    }

    /// Maps `End_A(T)` coordinates back to target algebra coordinates.
    ///
    /// # Panics
    /// Panics unless `coordinates` has length [`EndoAlgebra::dim`].
    pub fn preimage_coordinates(&self, coordinates: &[Fp]) -> Vec<Fp> {
        assert_eq!(
            coordinates.len(),
            self.endo.dim(),
            "preimage_coordinates: endomorphism coordinate count"
        );
        row_times(
            coordinates,
            &self.normal_word_preimages,
            &self.target.field(),
        )
    }

    /// Recomputes the source classification, target certificate, and algebra map.
    pub fn verify(&self) -> bool {
        verify_target(self)
    }
}

/// The three exact outcomes of target-presentation recovery.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum TargetPresentationOutcome {
    Presented(VerifiedTargetPresentation),
    Unsupported(NonSplitTarget),
    Cut(TargetPresentationCut),
}

impl TargetPresentationOutcome {
    optional_accessors! {
        /// The verified target, if recovery completed.
        pub presented() -> &VerifiedTargetPresentation = Self::Presented(value) => value;
        /// The non-split witness, if the target is unsupported.
        pub unsupported() -> &NonSplitTarget = Self::Unsupported(value) => value;
        /// The cut diagnostics, if a caller limit stopped recovery.
        pub cut() -> &TargetPresentationCut = Self::Cut(value) => value;
    }

    /// Recomputes the mathematical outcome and all stored certificate data.
    pub fn verify(&self) -> bool {
        match self {
            Self::Presented(value) => value.verify(),
            Self::Unsupported(value) => value.verify(),
            Self::Cut(value) => value.verify(),
        }
    }
}

fn source_data(
    module: &Module,
) -> Result<(EndoAlgebra, Decomposition, BasicDecomposition), TargetError> {
    let endo = EndoAlgebra::new(module);
    let decomposition = decompose_with_root_endo(module, Some(endo.clone()));
    let basic = BasicDecomposition::from_decomposition(module, &decomposition)
        .map_err(TargetError::from)?;
    Ok((endo, decomposition, basic))
}

fn bounded_source_data(
    module: &Module,
    limit: usize,
) -> Result<(EndoAlgebra, Decomposition, BasicDecomposition), TargetErrorOrCut> {
    let endo = EndoAlgebra::new(module);
    endo.dim()
        .checked_mul(endo.dim())
        .ok_or(TargetError::SizeOverflow {
            stage: TargetCutStage::EndoDimension,
        })?;
    if endo.dim() > limit {
        return Err(TargetCutReason::Budget(TargetBudgetCut {
            stage: TargetCutStage::EndoDimension,
            used: 0,
            requested: endo.dim(),
            limit,
        })
        .into());
    }
    let decomposition = decompose_with_root_endo(module, Some(endo.clone()));
    let basic = BasicDecomposition::from_decomposition(module, &decomposition)
        .map_err(TargetError::from)?;
    Ok((endo, decomposition, basic))
}

struct ProductCounter {
    used: usize,
    limit: usize,
}

impl ProductCounter {
    fn multiply(
        &mut self,
        endo: &EndoAlgebra,
        left: &[Fp],
        right: &[Fp],
        stage: TargetCutStage,
    ) -> Result<Vec<Fp>, TargetCutReason> {
        let Some(next) = self.used.checked_add(1) else {
            return Err(TargetCutReason::Budget(TargetBudgetCut {
                stage,
                used: self.used,
                requested: 1,
                limit: self.limit,
            }));
        };
        if next > self.limit {
            return Err(TargetCutReason::Budget(TargetBudgetCut {
                stage,
                used: self.used,
                requested: 1,
                limit: self.limit,
            }));
        }
        self.used = next;
        Ok(endo.multiply(left, right))
    }
}

fn radical_chain(
    endo: &EndoAlgebra,
    products: &mut ProductCounter,
) -> Result<Vec<DenseMat>, TargetCutReason> {
    let field = endo.field();
    let radical = endo.radical_basis().clone();
    let mut powers = vec![radical];
    while powers.last().expect("the chain starts at J").rows() != 0 {
        let power = powers.len();
        let current = powers.last().expect("the chain starts at J");
        let mut rows = Vec::new();
        for x in 0..current.rows() {
            for y in 0..endo.radical_dim() {
                rows.push(products.multiply(
                    endo,
                    current.row(x),
                    endo.radical_basis().row(y),
                    TargetCutStage::RadicalPower { power },
                )?);
            }
        }
        let next = DenseMat::from_rows_with_cols(&rows, endo.dim()).row_space_basis(&field);
        if next.rows() >= current.rows() && next.rows() != 0 {
            break;
        }
        powers.push(next);
    }
    Ok(powers)
}

fn corner(
    endo: &EndoAlgebra,
    power: &DenseMat,
    left: &[Fp],
    right: &[Fp],
    stage: TargetCutStage,
    products: &mut ProductCounter,
) -> Result<DenseMat, TargetCutReason> {
    let mut rows = Vec::with_capacity(power.rows());
    for r in 0..power.rows() {
        let first = products.multiply(endo, left, power.row(r), stage)?;
        rows.push(products.multiply(endo, &first, right, stage)?);
    }
    Ok(DenseMat::from_rows_with_cols(&rows, endo.dim()).row_space_basis(&endo.field()))
}

fn idempotents(endo: &EndoAlgebra, split: &Split) -> Vec<Vec<Fp>> {
    split
        .projections()
        .iter()
        .zip(split.inclusions())
        .map(|(projection, inclusion)| {
            endo.coords(
                &projection
                    .then(inclusion)
                    .expect("a split projection ends at its inclusion source"),
            )
        })
        .collect()
}

struct QuiverBuild {
    quiver: Quiver,
    arrow_images: DenseMat,
}

fn target_quiver(
    endo: &EndoAlgebra,
    split: &Split,
    powers: &[DenseMat],
    products: &mut ProductCounter,
) -> Result<QuiverBuild, TargetErrorOrCut> {
    let count = split.summands().len();
    let vertices = u32::try_from(count).map_err(|_| TargetError::Defect {
        reason: "the target vertex count exceeds u32".to_string(),
    })?;
    let zero = DenseMat::zero(0, endo.dim());
    let square = powers.get(1).unwrap_or(&zero);
    let ids = idempotents(endo, split);
    let mut arrows = Vec::new();
    let mut images = Vec::new();
    for source in 0..vertices {
        for target in 0..vertices {
            let radical = corner(
                endo,
                &powers[0],
                &ids[target as usize],
                &ids[source as usize],
                TargetCutStage::RadicalCorner {
                    source,
                    target,
                    power: 1,
                },
                products,
            )?;
            let radical_square = corner(
                endo,
                square,
                &ids[target as usize],
                &ids[source as usize],
                TargetCutStage::RadicalCorner {
                    source,
                    target,
                    power: 2,
                },
                products,
            )?;
            let complement = deterministic_complement(&radical, &radical_square, &endo.field());
            for r in 0..complement.rows() {
                u32::try_from(arrows.len()).map_err(|_| TargetError::Defect {
                    reason: "the target arrow count exceeds u32".to_string(),
                })?;
                arrows.push((source, target));
                images.push(complement.row(r).to_vec());
            }
        }
    }
    let expected = endo.radical_dim().saturating_sub(square.rows());
    if arrows.len() != expected {
        return Err(TargetError::Defect {
            reason: "the corner complements do not sum to rad(E)/rad(E)^2".to_string(),
        }
        .into());
    }
    let quiver = Quiver::new(vertices, &arrows).map_err(|error| TargetError::Defect {
        reason: format!("the recovered arrow endpoints were rejected: {error}"),
    })?;
    Ok(QuiverBuild {
        quiver,
        arrow_images: DenseMat::from_rows_with_cols(&images, endo.dim()),
    })
}

#[derive(Clone)]
struct EvaluatedPath {
    word: Vec<ArrowId>,
    image: Vec<Fp>,
}

struct PathBuild {
    between: Vec<Vec<Vec<EvaluatedPath>>>,
    count: usize,
}

fn target_paths(
    quiver: &Quiver,
    arrow_images: &DenseMat,
    endo: &EndoAlgebra,
    lambda: usize,
    limit: usize,
) -> Result<PathBuild, TargetErrorOrCut> {
    let n = quiver.num_vertices() as usize;
    let mut between: Vec<Vec<Vec<EvaluatedPath>>> = (0..n)
        .map(|_| (0..n).map(|_| Vec::new()).collect())
        .collect();
    let mut current = Vec::new();
    for source in 0..quiver.num_vertices() {
        for &arrow in quiver.arrows_from(source) {
            current.push(EvaluatedPath {
                word: vec![arrow],
                image: arrow_images.row(arrow.index()).to_vec(),
            });
        }
    }
    let mut used = 0usize;
    for length in 2..=lambda {
        let mut next = Vec::new();
        for path in &current {
            let last = *path.word.last().expect("a current path is nonempty");
            let target = quiver.target(last);
            for &arrow in quiver.arrows_from(target) {
                let Some(reserved) = used.checked_add(1) else {
                    return Err(TargetError::SizeOverflow {
                        stage: TargetCutStage::Paths { length },
                    }
                    .into());
                };
                if reserved > limit {
                    return Err(TargetCutReason::Budget(TargetBudgetCut {
                        stage: TargetCutStage::Paths { length },
                        used,
                        requested: 1,
                        limit,
                    })
                    .into());
                }
                used = reserved;
                let mut word = path.word.clone();
                word.push(arrow);
                let image = endo.multiply(arrow_images.row(arrow.index()), &path.image);
                let evaluated = EvaluatedPath { word, image };
                let source = quiver.source(evaluated.word[0]) as usize;
                let target = quiver.target(
                    *evaluated
                        .word
                        .last()
                        .expect("an evaluated path is nonempty"),
                ) as usize;
                between[source][target].push(evaluated.clone());
                next.push(evaluated);
            }
        }
        current = next;
    }
    Ok(PathBuild {
        between,
        count: used,
    })
}

fn target_relations(
    quiver: &Quiver,
    field: PrimeField,
    endo_dim: usize,
    paths: &PathBuild,
    max_terms: usize,
) -> Result<(Vec<Relation>, usize), TargetErrorOrCut> {
    let mut relations = Vec::new();
    let mut used = 0usize;
    for source in 0..quiver.num_vertices() {
        for target in 0..quiver.num_vertices() {
            let entries = &paths.between[source as usize][target as usize];
            let rows: Vec<Vec<Fp>> = entries.iter().map(|path| path.image.clone()).collect();
            let evaluation = DenseMat::from_rows_with_cols(&rows, endo_dim);
            let kernel = evaluation.left_kernel_basis(&field);
            for r in 0..kernel.rows() {
                let term_count = kernel.row(r).iter().filter(|c| !c.is_zero()).count();
                let Some(reserved) = used.checked_add(term_count) else {
                    return Err(TargetError::SizeOverflow {
                        stage: TargetCutStage::Relations { source, target },
                    }
                    .into());
                };
                if reserved > max_terms {
                    return Err(TargetCutReason::Budget(TargetBudgetCut {
                        stage: TargetCutStage::Relations { source, target },
                        used,
                        requested: term_count,
                        limit: max_terms,
                    })
                    .into());
                }
                used = reserved;
                let terms = kernel
                    .row(r)
                    .iter()
                    .zip(entries)
                    .filter(|(coefficient, _)| !coefficient.is_zero())
                    .map(|(&coefficient, path)| (coefficient, path.word.clone()))
                    .collect();
                relations.push(Relation::new(quiver, field, terms)?);
            }
        }
    }
    Ok((relations, used))
}

enum TargetErrorOrCut {
    Error(TargetError),
    Cut(TargetCutReason),
}

impl From<TargetError> for TargetErrorOrCut {
    fn from(error: TargetError) -> Self {
        Self::Error(error)
    }
}

impl From<TargetCutReason> for TargetErrorOrCut {
    fn from(cut: TargetCutReason) -> Self {
        Self::Cut(cut)
    }
}

impl From<RelationError> for TargetErrorOrCut {
    fn from(error: RelationError) -> Self {
        Self::Error(TargetError::Relation(error))
    }
}

fn path_image(
    path: &PathWord,
    idempotents: &[Vec<Fp>],
    arrows: &DenseMat,
    endo: &EndoAlgebra,
) -> Option<Vec<Fp>> {
    if path.is_trivial() {
        return idempotents.get(path.source() as usize).cloned();
    }
    let mut word = path.arrows().iter();
    let first = word.next()?;
    if first.index() >= arrows.rows() {
        return None;
    }
    let mut image = arrows.row(first.index()).to_vec();
    for arrow in word {
        if arrow.index() >= arrows.rows() {
            return None;
        }
        image = endo.multiply(arrows.row(arrow.index()), &image);
    }
    Some(image)
}

fn normal_word_images(
    algebra: &Algebra,
    idempotents: &[Vec<Fp>],
    arrows: &DenseMat,
    endo: &EndoAlgebra,
) -> Option<DenseMat> {
    let images: Option<Vec<Vec<Fp>>> = algebra
        .basis()
        .iter()
        .map(|path| path_image(path, idempotents, arrows, endo))
        .collect();
    Some(DenseMat::from_rows_with_cols(&images?, endo.dim()))
}

/// Recovers and verifies the split target presentation of `tilting`.
pub fn present_target(
    tilting: &ClassicalTiltingModule,
    limits: &TargetLimits,
) -> Result<TargetPresentationOutcome, TargetError> {
    let module = tilting.module();
    let wrap_cut = |reason| {
        TargetPresentationOutcome::Cut(TargetPresentationCut {
            source: module.clone(),
            tilting_limits: tilting.limits(),
            limits: limits.clone(),
            reason,
        })
    };
    let (endo, decomposition, basic) = match bounded_source_data(module, limits.max_endo_dimension)
    {
        Ok(value) => value,
        Err(TargetErrorOrCut::Cut(reason)) => return Ok(wrap_cut(reason)),
        Err(TargetErrorOrCut::Error(error)) => return Err(error),
    };
    if let Some((summand, non_split)) = basic
        .summands()
        .iter()
        .enumerate()
        .find(|(_, summand)| summand.residue_degree() != 1)
    {
        return Ok(TargetPresentationOutcome::Unsupported(NonSplitTarget {
            module: module.clone(),
            tilting_limits: tilting.limits(),
            limits: limits.clone(),
            summand,
            residue_degree: non_split.residue_degree(),
        }));
    }
    let split = decomposition.split().clone();
    let mut products = ProductCounter {
        used: 0,
        limit: limits.max_radical_products,
    };
    let powers = match radical_chain(&endo, &mut products) {
        Ok(value) => value,
        Err(reason) => return Ok(wrap_cut(reason)),
    };
    let lambda = powers.len();
    if powers.last().is_none_or(|power| power.rows() != 0) {
        return Err(TargetError::Defect {
            reason: "the endomorphism radical power chain did not reach zero".to_string(),
        });
    }
    let quiver_build = match target_quiver(&endo, &split, &powers, &mut products) {
        Ok(value) => value,
        Err(TargetErrorOrCut::Cut(reason)) => return Ok(wrap_cut(reason)),
        Err(TargetErrorOrCut::Error(error)) => return Err(error),
    };
    let paths = match target_paths(
        &quiver_build.quiver,
        &quiver_build.arrow_images,
        &endo,
        lambda,
        limits.max_paths,
    ) {
        Ok(value) => value,
        Err(TargetErrorOrCut::Cut(reason)) => return Ok(wrap_cut(reason)),
        Err(TargetErrorOrCut::Error(error)) => return Err(error),
    };
    let square_dim = powers.get(1).map_or(0, DenseMat::rows);
    if paths.count < square_dim {
        return Err(TargetError::Defect {
            reason: "the length-at-least-two path images do not span rad(E)^2".to_string(),
        });
    }
    let (relations, relation_terms) = match target_relations(
        &quiver_build.quiver,
        endo.field(),
        endo.dim(),
        &paths,
        limits.max_relation_terms,
    ) {
        Ok(value) => value,
        Err(TargetErrorOrCut::Cut(reason)) => return Ok(wrap_cut(reason)),
        Err(TargetErrorOrCut::Error(error)) => return Err(error),
    };
    if relations.len() != paths.count - square_dim {
        return Err(TargetError::Defect {
            reason: "the relation count disagrees with the rank of rad(E)^2".to_string(),
        });
    }
    let presentation = Presentation::new(quiver_build.quiver, endo.field(), relations)?;
    let target = match Algebra::new(presentation, &limits.completion) {
        Ok(value) => value,
        Err(AlgebraBuildError::Truncated(diagnostics)) => {
            return Ok(wrap_cut(TargetCutReason::Completion(diagnostics)));
        }
        Err(error) => return Err(TargetError::Algebra(error)),
    };
    let ids = idempotents(&endo, &split);
    let Some(images) = normal_word_images(&target, &ids, &quiver_build.arrow_images, &endo) else {
        return Err(TargetError::Defect {
            reason: "a verified target normal word has no algebra image".to_string(),
        });
    };
    let Some(preimages) = images.inverse(&endo.field()) else {
        return Err(TargetError::Defect {
            reason: "the normal-word image matrix is singular".to_string(),
        });
    };
    let endo_dimension = endo.dim();
    let verified = VerifiedTargetPresentation {
        source: module.clone(),
        tilting_limits: tilting.limits(),
        limits: limits.clone(),
        completion: target.certificate().clone(),
        target,
        endo,
        split,
        idempotent_images: DenseMat::from_rows_with_cols(&ids, images.cols()),
        arrow_images: quiver_build.arrow_images,
        normal_word_images: images,
        normal_word_preimages: preimages,
        radical_nilpotency_index: lambda,
        work: TargetWork {
            endo_dimension,
            radical_products: products.used,
            paths: paths.count,
            relation_terms,
        },
    };
    if !verified.verify() {
        return Err(TargetError::Defect {
            reason: "the independent target verifier rejected the recovered presentation"
                .to_string(),
        });
    }
    Ok(TargetPresentationOutcome::Presented(verified))
}

fn add_scaled_row(target: &mut [Fp], source: &[Fp], scale: Fp, field: &PrimeField) {
    for (out, &value) in target.iter_mut().zip(source) {
        *out = field.add(*out, field.mul(scale, value));
    }
}

fn relation_image(
    relation: &RelationData,
    quiver: &Quiver,
    idempotents: &[Vec<Fp>],
    arrows: &DenseMat,
    endo: &EndoAlgebra,
) -> Option<Vec<Fp>> {
    let field = endo.field();
    let mut image = vec![Fp::ZERO; endo.dim()];
    for (coefficient, raw) in relation {
        let ids: Vec<ArrowId> = raw.iter().copied().map(ArrowId).collect();
        let path = PathWord::from_arrows(quiver, &ids).ok()?;
        let term = path_image(&path, idempotents, arrows, endo)?;
        add_scaled_row(&mut image, &term, field.elem(*coefficient as i64), &field);
    }
    Some(image)
}

fn same_algebra_data(left: &Algebra, right: &Algebra) -> bool {
    left.field() == right.field()
        && left.quiver() == right.quiver()
        && left.basis() == right.basis()
        && left.relations() == right.relations()
}

fn verify_idempotents(endo: &EndoAlgebra, ids: &[Vec<Fp>]) -> bool {
    let field = endo.field();
    let mut sum = vec![Fp::ZERO; endo.dim()];
    for (i, left) in ids.iter().enumerate() {
        add_scaled_row(&mut sum, left, Fp::ONE, &field);
        for (j, right) in ids.iter().enumerate() {
            let product = endo.multiply(left, right);
            if (i == j && product != *left)
                || (i != j && product.iter().any(|value| !value.is_zero()))
            {
                return false;
            }
        }
    }
    sum == endo.one()
}

fn unlimited_radical_chain(endo: &EndoAlgebra) -> Option<(Vec<DenseMat>, usize)> {
    let mut products = ProductCounter {
        used: 0,
        limit: usize::MAX,
    };
    let powers = radical_chain(endo, &mut products).ok()?;
    powers
        .last()
        .is_some_and(|power| power.rows() == 0)
        .then_some((powers, products.used))
}

fn expected_arrow_images(
    endo: &EndoAlgebra,
    split: &Split,
    powers: &[DenseMat],
) -> Option<(Quiver, DenseMat, usize)> {
    let mut products = ProductCounter {
        used: 0,
        limit: usize::MAX,
    };
    let built = target_quiver(endo, split, powers, &mut products).ok()?;
    Some((built.quiver, built.arrow_images, products.used))
}

fn verify_target(value: &VerifiedTargetPresentation) -> bool {
    let Ok(ClassicalTiltingResult::Tilting(tilting)) =
        ClassicalTiltingModule::classify(&value.source, value.tilting_limits)
    else {
        return false;
    };
    if !tilting.verify() || !value.split.verify() || !value.split.total().ptr_eq(&value.source) {
        return false;
    }
    let Ok((endo, decomposition, basic)) = source_data(&value.source) else {
        return false;
    };
    if endo.dim().checked_mul(endo.dim()).is_none()
        || endo.dim() > value.limits.max_endo_dimension
        || value.work.radical_products > value.limits.max_radical_products
        || value.work.paths > value.limits.max_paths
        || value.work.relation_terms > value.limits.max_relation_terms
    {
        return false;
    }
    if basic
        .summands()
        .iter()
        .any(|summand| summand.residue_degree() != 1)
    {
        return false;
    }
    if decomposition.split().summands().len() != value.split.summands().len() {
        return false;
    }
    let ids = idempotents(&endo, decomposition.split());
    let stored_ids: Vec<Vec<Fp>> = (0..value.idempotent_images.rows())
        .map(|row| value.idempotent_images.row(row).to_vec())
        .collect();
    if stored_ids != ids {
        return false;
    }
    if !verify_idempotents(&endo, &ids) {
        return false;
    }
    let Some((powers, chain_products)) = unlimited_radical_chain(&endo) else {
        return false;
    };
    if powers.len() != value.radical_nilpotency_index {
        return false;
    }
    let Some((expected_quiver, expected_arrows, corner_products)) =
        expected_arrow_images(&endo, decomposition.split(), &powers)
    else {
        return false;
    };
    if expected_quiver != *value.target.quiver() || expected_arrows != value.arrow_images {
        return false;
    }
    let Some(radical_products) = chain_products.checked_add(corner_products) else {
        return false;
    };
    let Ok(paths) = target_paths(
        &expected_quiver,
        &expected_arrows,
        &endo,
        powers.len(),
        usize::MAX,
    ) else {
        return false;
    };
    let relation_terms = value.completion.input_relations.iter().flatten().count();
    if value.work
        != (TargetWork {
            endo_dimension: endo.dim(),
            radical_products,
            paths: paths.count,
            relation_terms,
        })
    {
        return false;
    }
    if value.completion != *value.target.certificate() {
        return false;
    }
    let Ok(completion) = verify_certificate(value.completion.clone()) else {
        return false;
    };
    let Ok(rebuilt) = Algebra::from_verified_with_limits(completion, &value.limits.completion)
    else {
        return false;
    };
    if !same_algebra_data(&rebuilt, &value.target) {
        return false;
    }
    if value.completion.input_relations.iter().any(|relation| {
        relation_image(
            relation,
            value.target.quiver(),
            &ids,
            &value.arrow_images,
            &endo,
        )
        .is_none_or(|image| image.iter().any(|coefficient| !coefficient.is_zero()))
    }) {
        return false;
    }
    let Some(images) = normal_word_images(&value.target, &ids, &value.arrow_images, &endo) else {
        return false;
    };
    let Some(preimages) = images.inverse(&endo.field()) else {
        return false;
    };
    if images != value.normal_word_images
        || preimages != value.normal_word_preimages
        || images.rows() != images.cols()
        || images.cols() != endo.dim()
    {
        return false;
    }
    let n = value.target.quiver().num_vertices() as usize;
    let mut unit = vec![Fp::ZERO; endo.dim()];
    for i in 0..n {
        add_scaled_row(&mut unit, images.row(i), Fp::ONE, &endo.field());
    }
    if unit != endo.one() {
        return false;
    }
    for left in 0..value.target.dim() {
        for right in 0..value.target.dim() {
            let mut expected = vec![Fp::ZERO; endo.dim()];
            for (basis, coefficient) in value.target.mul_basis(left, right) {
                add_scaled_row(&mut expected, images.row(basis), coefficient, &endo.field());
            }
            let actual = endo.multiply(images.row(right), images.row(left));
            if actual != expected {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{an_with_relations, dual_numbers, linear_an};
    use crate::field::PrimeField;
    use crate::module::{Module, direct_sum};

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn tilting(module: &Module) -> ClassicalTiltingModule {
        let limits = TiltingLimits {
            max_projective_dimension: 4,
            max_generation_steps: 8,
        };
        let ClassicalTiltingResult::Tilting(value) =
            ClassicalTiltingModule::classify(module, limits).unwrap()
        else {
            panic!("the fixture is classical tilting")
        };
        value
    }

    fn regular(algebra: &Arc<Algebra>) -> Module {
        let parts: Vec<Module> = (0..algebra.quiver().num_vertices())
            .map(|vertex| Module::projective(algebra, vertex))
            .collect();
        match parts.as_slice() {
            [only] => only.clone(),
            _ => direct_sum(&parts.iter().collect::<Vec<_>>()).0,
        }
    }

    #[test]
    fn the_projective_generator_has_a_verified_split_target() {
        let algebra = linear_an(3, f5());
        let tilting = tilting(&regular(&algebra));
        let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
        let target = outcome.presented().expect("the regular target is split");
        assert!(target.verify());
        assert_eq!(target.target().dim(), algebra.dim());
        assert_eq!(target.split().summands().len(), 3);
        assert_eq!(target.normal_word_images().rows(), target.target().dim());
        let unit = vec![f5().one(); target.target().quiver().num_vertices() as usize];
        let mut coordinates = vec![f5().zero(); target.target().dim()];
        coordinates[..unit.len()].copy_from_slice(&unit);
        let image = target.map_coordinates(&coordinates);
        assert_eq!(image, target.endo().one());
        assert_eq!(target.preimage_coordinates(&image), coordinates);
        assert!(outcome.verify());
    }

    #[test]
    fn the_dual_numbers_target_keeps_its_quadratic_relation() {
        let algebra = dual_numbers(f5());
        let tilting = tilting(&regular(&algebra));
        let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
        let target = outcome.presented().expect("the regular target is split");
        assert!(target.verify());
        assert_eq!(target.target().quiver().num_arrows(), 1);
        assert!(
            target
                .completion_certificate()
                .input_relations
                .iter()
                .any(|relation| relation.iter().any(|(_, word)| word.len() == 2))
        );
        assert_eq!(
            target.work(),
            TargetWork {
                endo_dimension: 2,
                radical_products: 3,
                paths: 1,
                relation_terms: 1,
            }
        );
    }

    #[test]
    fn a_nontrivial_tilting_target_uses_the_opposite_orientation() {
        let algebra = linear_an(2, f5());
        let p0 = Module::projective(&algebra, 0);
        let s0 = Module::simple(&algebra, 0);
        let module = direct_sum(&[&p0, &s0]).0;
        let tilting = tilting(&module);
        let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
        let target = outcome.presented().expect("the tilting target is split");
        assert!(target.verify());
        assert_eq!(target.target().quiver().num_arrows(), 1);
        assert_eq!(target.target().quiver().arrows(), &[(1, 0)]);
    }

    #[test]
    fn the_private_mutation_corpus_rejects_every_target_claim() {
        let algebra = dual_numbers(f5());
        let tilting = tilting(&regular(&algebra));
        let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
        let target = outcome.presented().expect("the regular target is split");
        let mut corpus = Vec::new();

        let mut changed = target.clone();
        let entry = changed.idempotent_images.get(0, 0);
        changed
            .idempotent_images
            .set(0, 0, f5().add(entry, f5().one()));
        corpus.push(changed);

        let mut changed = target.clone();
        let entry = changed.arrow_images.get(0, 0);
        changed.arrow_images.set(0, 0, f5().add(entry, f5().one()));
        corpus.push(changed);

        let mut changed = target.clone();
        let entry = changed.normal_word_images.get(0, 0);
        changed
            .normal_word_images
            .set(0, 0, f5().add(entry, f5().one()));
        corpus.push(changed);

        let mut changed = target.clone();
        let entry = changed.normal_word_preimages.get(0, 0);
        changed
            .normal_word_preimages
            .set(0, 0, f5().add(entry, f5().one()));
        corpus.push(changed);

        let mut changed = target.clone();
        changed.work.endo_dimension += 1;
        corpus.push(changed);

        let mut changed = target.clone();
        changed.work.radical_products += 1;
        corpus.push(changed);

        let mut changed = target.clone();
        changed.work.paths += 1;
        corpus.push(changed);

        let mut changed = target.clone();
        changed.work.relation_terms += 1;
        corpus.push(changed);

        let mut changed = target.clone();
        changed.completion.input_relations[0][0].0 = 2;
        corpus.push(changed);

        for changed in corpus {
            assert!(!changed.verify());
        }
    }

    #[test]
    fn each_local_target_budget_has_a_typed_cut() {
        let algebra = dual_numbers(f5());
        let tilting = tilting(&regular(&algebra));

        let limits = TargetLimits {
            max_endo_dimension: 1,
            ..TargetLimits::default()
        };
        let outcome = present_target(&tilting, &limits).unwrap();
        let cut = outcome
            .cut()
            .expect("the endomorphism dimension exceeds one");
        assert!(matches!(
            cut.reason(),
            TargetCutReason::Budget(TargetBudgetCut {
                stage: TargetCutStage::EndoDimension,
                requested: 2,
                ..
            })
        ));
        assert!(cut.source().ptr_eq(tilting.module()));
        assert_eq!(cut.tilting_limits(), tilting.limits());
        assert_eq!(cut.limits(), &limits);
        assert!(outcome.verify());

        let limits = TargetLimits {
            max_radical_products: 0,
            ..TargetLimits::default()
        };
        let outcome = present_target(&tilting, &limits).unwrap();
        assert!(matches!(
            outcome.cut().expect("the radical budget is zero").reason(),
            TargetCutReason::Budget(TargetBudgetCut {
                stage: TargetCutStage::RadicalPower { .. },
                ..
            })
        ));
        assert!(outcome.verify());

        let limits = TargetLimits {
            max_paths: 0,
            ..TargetLimits::default()
        };
        let outcome = present_target(&tilting, &limits).unwrap();
        assert!(matches!(
            outcome.cut().expect("the path budget is zero").reason(),
            TargetCutReason::Budget(TargetBudgetCut {
                stage: TargetCutStage::Paths { length: 2 },
                ..
            })
        ));
        assert!(outcome.verify());

        let limits = TargetLimits {
            max_relation_terms: 0,
            ..TargetLimits::default()
        };
        let outcome = present_target(&tilting, &limits).unwrap();
        assert!(matches!(
            outcome.cut().expect("the relation budget is zero").reason(),
            TargetCutReason::Budget(TargetBudgetCut {
                stage: TargetCutStage::Relations { .. },
                ..
            })
        ));
        assert!(outcome.verify());
    }

    #[test]
    fn completion_exhaustion_keeps_its_diagnostics() {
        let algebra = dual_numbers(f5());
        let tilting = tilting(&regular(&algebra));
        let mut limits = TargetLimits::default();
        limits.completion.max_steps = 0;
        let outcome = present_target(&tilting, &limits).unwrap();
        assert!(matches!(
            outcome.cut().expect("completion must stop").reason(),
            TargetCutReason::Completion(_)
        ));
        assert!(outcome.verify());
    }

    #[test]
    fn the_pd2_dual_target_is_verified_over_f2_and_f5() {
        for field in [PrimeField::new(2).unwrap(), f5()] {
            let algebra = an_with_relations(3, &[(0, 2)], field).unwrap();
            let injectives: Vec<Module> = (0..3)
                .map(|vertex| Module::injective(&algebra, vertex))
                .collect();
            let module = direct_sum(&injectives.iter().collect::<Vec<_>>()).0;
            let tilting = tilting(&module);
            assert_eq!(tilting.projective_dimension(), 2);
            let outcome = present_target(&tilting, &TargetLimits::default()).unwrap();
            let target = outcome.presented().expect("the dual target is split");
            assert_eq!(target.target().dim(), algebra.dim());
            assert!(outcome.verify());
        }
    }
}
