use std::sync::Arc;

use crate::algebra::Algebra;
use crate::certificate::Certificate;
use crate::endo::EndoAlgebra;
use crate::field::{Fp, PrimeField};
use crate::homspace::deterministic_complement;
use crate::linalg::DenseMat;
use crate::quiver::{ArrowId, PathWord, Quiver};
use crate::relation::{Relation, RelationError};

use super::{TargetBudgetCut, TargetCutReason, TargetCutStage, TargetError, TargetWork};

pub(super) struct ProductCounter {
    pub(super) used: usize,
    pub(super) limit: usize,
}

pub(crate) trait CoordinateAlgebra {
    fn field(&self) -> PrimeField;
    fn dim(&self) -> usize;
    fn radical_basis(&self) -> &DenseMat;
    fn radical_dim(&self) -> usize;
    fn one(&self) -> &[Fp];
    fn multiply(&self, left: &[Fp], right: &[Fp]) -> Vec<Fp>;
}

impl CoordinateAlgebra for EndoAlgebra {
    fn field(&self) -> PrimeField {
        self.field()
    }

    fn dim(&self) -> usize {
        self.dim()
    }

    fn radical_basis(&self) -> &DenseMat {
        self.radical_basis()
    }

    fn radical_dim(&self) -> usize {
        self.radical_dim()
    }

    fn one(&self) -> &[Fp] {
        self.one()
    }

    fn multiply(&self, left: &[Fp], right: &[Fp]) -> Vec<Fp> {
        self.multiply(left, right)
    }
}

impl ProductCounter {
    pub(super) fn multiply<A: CoordinateAlgebra>(
        &mut self,
        endo: &A,
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
pub(super) struct QuiverBuild {
    pub(super) quiver: Quiver,
    pub(super) arrow_images: DenseMat,
}

pub(super) fn target_quiver<A: CoordinateAlgebra>(
    endo: &A,
    ids: &[Vec<Fp>],
    powers: &[DenseMat],
    products: &mut ProductCounter,
) -> Result<QuiverBuild, TargetErrorOrCut> {
    let count = ids.len();
    let vertices = u32::try_from(count).map_err(|_| TargetError::Defect {
        reason: "the target vertex count exceeds u32".to_string(),
    })?;
    let zero = DenseMat::zero(0, endo.dim());
    let square = powers.get(1).unwrap_or(&zero);
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
pub(super) struct EvaluatedPath {
    pub(super) word: Vec<ArrowId>,
    pub(super) image: Vec<Fp>,
}

pub(super) struct PathBuild {
    pub(super) between: Vec<Vec<Vec<EvaluatedPath>>>,
    pub(super) count: usize,
}

pub(super) fn target_paths<A: CoordinateAlgebra>(
    quiver: &Quiver,
    arrow_images: &DenseMat,
    endo: &A,
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

pub(super) fn target_relations(
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

pub(super) enum TargetErrorOrCut {
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

pub(super) fn path_image<A: CoordinateAlgebra>(
    path: &PathWord,
    idempotents: &[Vec<Fp>],
    arrows: &DenseMat,
    endo: &A,
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

pub(super) fn normal_word_images<A: CoordinateAlgebra>(
    algebra: &Algebra,
    idempotents: &[Vec<Fp>],
    arrows: &DenseMat,
    endo: &A,
) -> Option<DenseMat> {
    let images: Option<Vec<Vec<Fp>>> = algebra
        .basis()
        .iter()
        .map(|path| path_image(path, idempotents, arrows, endo))
        .collect();
    Some(DenseMat::from_rows_with_cols(&images?, endo.dim()))
}

pub(super) fn radical_chain<A: CoordinateAlgebra>(
    endo: &A,
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

fn corner<A: CoordinateAlgebra>(
    endo: &A,
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

#[derive(Clone)]
pub(crate) struct CoordinateTargetData {
    pub target: Arc<Algebra>,
    pub completion: Certificate,
    pub idempotent_images: DenseMat,
    pub arrow_images: DenseMat,
    pub normal_word_images: DenseMat,
    pub normal_word_preimages: DenseMat,
    pub radical_nilpotency_index: usize,
    pub work: TargetWork,
}

pub(crate) enum CoordinateTargetOutcome {
    Presented(Box<CoordinateTargetData>),
    Cut(TargetCutReason),
}
