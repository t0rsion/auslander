use std::sync::Arc;

use crate::ar::tau;
use crate::arquiver::IndecomposableCatalog;
use crate::ext::{ExtClass, ExtSpace};
use crate::hom::HomError;
use crate::indec::IndecomposableModule;
use crate::sequence::{NonSplitWitness, ShortExactSequence, SplitStatus};

use super::catalog::{self, CatalogWitness};
use super::errors::{AlmostSplitError, DefectKind, defect};
use super::stable::{action_matrices, socle_kernel, stable_end};
use super::types::{AlmostSplitOutcome, AlmostSplitSequence, AlmostSplitWitness, ArDualityWitness};

/// The shared output of the socle construction for a non-projective input.
pub(in crate::almost_split) struct SocleConstruction {
    pub(in crate::almost_split) tau_ind: IndecomposableModule,
    pub(in crate::almost_split) class: ExtClass,
    pub(in crate::almost_split) socle: crate::linalg::DenseMat,
    pub(in crate::almost_split) traces: Vec<Vec<crate::field::Fp>>,
    pub(in crate::almost_split) sequence: ShortExactSequence,
    pub(in crate::almost_split) non_split: NonSplitWitness,
}

type SocleData = (
    ExtClass,
    crate::linalg::DenseMat,
    Vec<Vec<crate::field::Fp>>,
    ShortExactSequence,
);

fn construction_start(
    m: &IndecomposableModule,
) -> Result<Option<IndecomposableModule>, AlmostSplitError> {
    let (projective, tau_module) = (m.is_projective(), tau(m.module())?);
    if tau_module.is_zero() != projective {
        return Err(defect(DefectKind::ProjectivityDisagreement {
            resolution_projective: projective,
            tau_zero: tau_module.is_zero(),
        }));
    }
    if projective {
        return Ok(None);
    }
    Ok(Some(IndecomposableModule::new(&tau_module)?))
}

fn checked_ext_space(
    m: &IndecomposableModule,
    tau_ind: &IndecomposableModule,
) -> Result<ExtSpace, AlmostSplitError> {
    let space = ExtSpace::new(m.module(), tau_ind.module(), 1)
        .expect("the translate lives over the module's algebra Arc");
    let stable = stable_end(m.module())?;
    if space.dim() != stable.dim() {
        return Err(defect(DefectKind::DualityDimensionMismatch {
            ext_dim: space.dim(),
            stable_end_dim: stable.dim(),
        }));
    }
    Ok(space)
}

fn socle_data(m: &IndecomposableModule, space: &ExtSpace) -> Result<SocleData, AlmostSplitError> {
    let (field, action) = (m.module().field(), action_matrices(m, space)?);
    let socle = socle_kernel(&action, space.dim(), &field);
    if socle.rows() != m.residue_degree() {
        return Err(defect(DefectKind::SocleDimensionMismatch {
            socle_dim: socle.rows(),
            residue_degree: m.residue_degree(),
        }));
    }
    let class = space.class_from_coordinates(socle.row(0))?;
    let traces = action
        .iter()
        .map(|matrix| crate::homspace::row_times(class.coordinates(), matrix, &field))
        .collect();
    let sequence = ShortExactSequence::from_ext1(&class)?;
    Ok((class, socle, traces, sequence))
}

fn build_nonprojective(
    m: &IndecomposableModule,
    tau_ind: IndecomposableModule,
) -> Result<Box<SocleConstruction>, AlmostSplitError> {
    let space = checked_ext_space(m, &tau_ind)?;
    let (class, socle, traces, sequence) = socle_data(m, &space)?;
    // The chosen class is a nonzero socle row, so the one-pass route expects
    // a non-split witness.
    let SplitStatus::NonSplit(non_split) = sequence.split_status_one_pass() else {
        return Err(defect(DefectKind::NonzeroClassSplit));
    };
    Ok(Box::new(SocleConstruction {
        tau_ind,
        class,
        socle,
        traces,
        sequence,
        non_split,
    }))
}

/// Socle construction of the module docs: double-route translate, action
/// matrices, socle kernel, dimension gates, chosen class, non-split witness.
fn construct(m: &IndecomposableModule) -> Result<Option<Box<SocleConstruction>>, AlmostSplitError> {
    construction_start(m)?
        .map(|tau_ind| build_nonprojective(m, tau_ind))
        .transpose()
}

/// The almost-split sequence ending at `m`, certified through the AR
/// duality route.
///
/// A projective input returns [`AlmostSplitOutcome::Projective`]. Otherwise
/// the socle construction runs and the result carries an [`ArDualityWitness`].
///
/// # Errors
/// [`AlmostSplitError::Tau`] when the translate fails,
/// [`AlmostSplitError::TauIndecomposability`] when the translate fails the
/// indecomposability gate, and [`AlmostSplitError::Defect`] when an internal
/// cross-check fails, which is a crate defect. The Hom, Ext, and sequence
/// layers report their own endpoint rejections through
/// [`AlmostSplitError::Hom`], [`AlmostSplitError::Space`],
/// [`AlmostSplitError::Ext`], and [`AlmostSplitError::Sequence`].
pub fn almost_split(m: &IndecomposableModule) -> Result<AlmostSplitOutcome, AlmostSplitError> {
    let Some(built) = construct(m)? else {
        return Ok(AlmostSplitOutcome::Projective);
    };
    let SocleConstruction {
        tau_ind: _,
        class,
        socle,
        traces,
        sequence,
        non_split,
    } = *built;
    let witness = ArDualityWitness {
        radical_coords: m.endo().radical_basis().clone(),
        action_traces: traces,
        socle_dim: socle.rows(),
        socle_rref: socle,
        chosen_row: 0,
        ext_dim: class.space().dim(),
        stable_end_dim: class.space().dim(),
        residue_degree: m.residue_degree(),
        non_split,
    };
    Ok(AlmostSplitOutcome::Sequence(AlmostSplitSequence {
        sequence,
        class,
        witness: AlmostSplitWitness::ArDuality(witness),
    }))
}

/// The almost-split sequence ending at `m`, certified against every entry
/// of an exhaustive catalog.
///
/// The construction is the one of [`almost_split`]; the witness instead
/// stores, for the right map `g: E -> M` and every catalog entry `X`, the
/// data behind `im(Hom(X, E) -> Hom(X, M)) = rad(X, M)`, and the dual left
/// data for `f: tau M -> E`.
///
/// # Errors
/// [`AlmostSplitError::Hom`] with [`HomError::DifferentAlgebras`] when `m`
/// and the catalog do not share one algebra; otherwise as
/// [`almost_split`].
pub fn almost_split_via_catalog(
    m: &IndecomposableModule,
    catalog: &IndecomposableCatalog,
) -> Result<AlmostSplitOutcome, AlmostSplitError> {
    Arc::ptr_eq(m.module().algebra(), catalog.algebra())
        .then_some(())
        .ok_or(AlmostSplitError::Hom(HomError::DifferentAlgebras))?;
    let Some(built) = construct(m)? else {
        return Ok(AlmostSplitOutcome::Projective);
    };
    let SocleConstruction {
        tau_ind,
        class,
        sequence,
        ..
    } = *built;
    let mut entries = Vec::with_capacity(catalog.len());
    for (entry, x) in catalog.entries().iter().enumerate() {
        entries.push(
            catalog::recompute_entry(m, &tau_ind, &sequence, x).and_then(|recomputed| {
                if recomputed.image != recomputed.rad {
                    return Err(defect(DefectKind::RightFactorizationMismatch { entry }));
                }
                if recomputed.left_image != recomputed.left_rad {
                    return Err(defect(DefectKind::LeftFactorizationMismatch { entry }));
                }
                recomputed.into_check()
            })?,
        );
    }
    Ok(AlmostSplitOutcome::Sequence(AlmostSplitSequence {
        sequence,
        class,
        witness: AlmostSplitWitness::ExhaustiveCatalog(CatalogWitness { entries }),
    }))
}
