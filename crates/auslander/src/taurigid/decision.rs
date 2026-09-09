use crate::context::VerificationContext;
use crate::decompose::decompose;
use crate::hom::hom_dim;
use crate::homspace::HomSpace;
use crate::module::Module;

use super::cache::TauCache;
use super::types::{NonTauRigidWitness, TauRigidError, TauRigidModule, TauRigidityOutcome};

/// Decides tau-rigidity of `M = X_1 + ... + X_s` from the summands, never
/// from the assembled module.
///
/// Each entry of `summands` is a caller label and the summand. The label
/// travels to [`NonTauRigidWitness`] and to
/// [`TauRigidModule::vanishing_pairs`]. `cache` keys on the identity of the
/// module value, not on the label, so `tau` runs once per module value. The
/// pairs are scanned in `(i, j)` lexicographic order over positions, so the
/// returned [`NonTauRigidWitness`] is the first nonzero `Hom(X_i, tau X_j)`
/// in that order.
///
/// An empty slice is the zero module: tau-rigid, with no pair to check.
///
/// Correctness is additivity of `tau` and of `Hom`, so the identity holds
/// for any direct-sum decomposition. Indecomposable summands reuse cache
/// entries. They are not what makes the answer right.
pub fn is_tau_rigid_summandwise(
    summands: &[(usize, Module)],
    cache: &mut TauCache,
) -> Result<TauRigidityOutcome, TauRigidError> {
    is_tau_rigid_summandwise_with(
        summands,
        |module| cache.tau_of(module).cloned().map_err(Into::into),
        |source, target| hom_dim(source, target).map_err(Into::into),
    )
}

pub(crate) fn is_tau_rigid_summandwise_with_context(
    summands: &[(usize, Module)],
    context: &VerificationContext,
) -> Result<TauRigidityOutcome, TauRigidError> {
    is_tau_rigid_summandwise_with(
        summands,
        |module| {
            context
                .tau_for(module)
                .map(|translate| translate.as_ref().clone())
                .map_err(Into::into)
        },
        |source, target| context.hom_dim_for(source, target).map_err(Into::into),
    )
}

fn is_tau_rigid_summandwise_with(
    summands: &[(usize, Module)],
    mut tau_of: impl FnMut(&Module) -> Result<Module, TauRigidError>,
    mut hom_dimension: impl FnMut(&Module, &Module) -> Result<usize, TauRigidError>,
) -> Result<TauRigidityOutcome, TauRigidError> {
    let mut translates = Vec::with_capacity(summands.len());
    for (_, x) in summands {
        translates.push(tau_of(x)?);
    }
    for (source_index, x) in summands {
        for (j, (target_index, y)) in summands.iter().enumerate() {
            // Hom(X_i, 0) is zero for every X_i, so a projective X_j needs no
            // Hom system.
            let translate = &translates[j];
            if translate.is_zero() {
                continue;
            }
            // A vanishing pair needs the dimension alone. The basis is built
            // only where a nonzero dimension says a morphism exists to hand
            // back.
            if hom_dimension(x, translate)? == 0 {
                continue;
            }
            let space = HomSpace::new(x, translate)?;
            return Ok(TauRigidityOutcome::NotTauRigid(NonTauRigidWitness {
                source_index: *source_index,
                target_index: *target_index,
                source: x.clone(),
                target_summand: y.clone(),
                translate: translate.clone(),
                morphism: space.basis()[0].clone(),
            }));
        }
    }
    Ok(TauRigidityOutcome::TauRigid(TauRigidModule {
        summands: summands.to_vec(),
        translates,
    }))
}

/// Decides tau-rigidity of an assembled module by decomposing it first.
///
/// The module goes through [`decompose`] and the summands go to
/// [`is_tau_rigid_summandwise`] with positions as labels, over a fresh
/// [`TauCache`] that is dropped on return. Use it for a one-off question.
///
/// In a hot loop, call [`is_tau_rigid_summandwise`] instead and keep one
/// [`TauCache`] across the whole walk. Working per summand avoids running the
/// double-route cross-check on a decomposable module, where it decomposes
/// both of its results.
pub fn is_tau_rigid(m: &Module) -> Result<TauRigidityOutcome, TauRigidError> {
    // decompose has no summand to return for the zero module, which is
    // tau-rigid with an empty summand list.
    let summands: Vec<_> = if m.is_zero() {
        Vec::new()
    } else {
        decompose(m)
            .summands()
            .iter()
            .cloned()
            .enumerate()
            .collect()
    };
    is_tau_rigid_summandwise(&summands, &mut TauCache::new())
}
