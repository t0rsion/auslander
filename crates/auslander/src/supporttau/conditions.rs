use std::sync::Arc;

use crate::basic::{BasicDecomposition, ProjectiveSupport};
use crate::context::VerificationContext;
use crate::module::Module;
use crate::taurigid::{
    TauCache, TauRigidError, TauRigidModule, TauRigidityOutcome, is_tau_rigid_summandwise,
    is_tau_rigid_summandwise_with_context,
};

use super::errors::{Checked, PairRejection, SupportTauError};

/// Runs conditions 1 to 4 in the order of `docs/support-tau-tilting.md` section 6.
///
/// `expected` is the required value of `|M| + |P|`. `summand_indices[i]` is
/// the caller's stable index for summand `i` of `module`. It is a label only,
/// carried into witnesses and the bindings. It does not key `cache`, which
/// keys on nominal module identity.
pub(super) fn check_conditions(
    module: &BasicDecomposition,
    projective: &ProjectiveSupport,
    expected: usize,
    summand_indices: &[usize],
    cache: Option<&mut TauCache>,
) -> Result<Checked, SupportTauError> {
    let mut owned = TauCache::new();
    let cache = cache.unwrap_or(&mut owned);
    check_conditions_with(module, projective, expected, summand_indices, |summands| {
        is_tau_rigid_summandwise(summands, cache)
    })
}

pub(super) fn check_conditions_with_context(
    module: &BasicDecomposition,
    projective: &ProjectiveSupport,
    expected: usize,
    summand_indices: &[usize],
    context: &VerificationContext,
) -> Result<Checked, SupportTauError> {
    check_conditions_with(module, projective, expected, summand_indices, |summands| {
        is_tau_rigid_summandwise_with_context(summands, context)
    })
}

fn check_conditions_with(
    module: &BasicDecomposition,
    projective: &ProjectiveSupport,
    expected: usize,
    summand_indices: &[usize],
    mut rigidity: impl FnMut(&[(usize, Module)]) -> Result<TauRigidityOutcome, TauRigidError>,
) -> Result<Checked, SupportTauError> {
    if summand_indices.len() != module.len() {
        return Err(SupportTauError::SummandIndexCount {
            indices: summand_indices.len(),
            summands: module.len(),
        });
    }
    if !Arc::ptr_eq(module.module().algebra(), projective.algebra()) {
        return Ok(Checked::Rejected(PairRejection::DifferentAlgebras));
    }
    // Condition 2 is arithmetic on the dimension vector, with no Hom space.
    // See `support_complement` for the identification Hom(P_v, M) = M_v.
    // ProjectiveSupport::new keeps its vertices below the vertex count of the
    // algebra the previous check just matched, so the index is in range.
    let dims = module.module().dim_vector();
    if let Some(&vertex) = projective
        .vertices()
        .iter()
        .find(|&&v| dims[v as usize] != 0)
    {
        return Ok(Checked::Rejected(PairRejection::HomFromProjectiveNonzero {
            vertex,
            dim: dims[vertex as usize],
        }));
    }
    let summands: Vec<(usize, Module)> = summand_indices
        .iter()
        .zip(module.summands())
        .map(|(&index, x)| (index, x.module().clone()))
        .collect();
    let rigid = match rigidity(&summands)? {
        TauRigidityOutcome::TauRigid(rigid) => rigid,
        TauRigidityOutcome::NotTauRigid(witness) => {
            return Ok(Checked::Rejected(PairRejection::NotTauRigid(witness)));
        }
    };
    if module.len() + projective.len() != expected {
        return Ok(Checked::Rejected(PairRejection::SummandCount {
            module: module.len(),
            projective: projective.len(),
            expected,
        }));
    }
    Ok(Checked::Accepted(rigid))
}

/// The number of vertices of the algebra the pair lives over.
pub(super) fn vertex_count(module: &BasicDecomposition) -> usize {
    module.module().algebra().quiver().num_vertices() as usize
}

/// Positional indices, the indexing a caller with no stable one uses.
pub(super) fn positional(module: &BasicDecomposition) -> Vec<usize> {
    (0..module.len()).collect()
}

/// The vertices outside the support of `module`, in increasing order.
///
/// These are exactly the vertices `v` with `Hom(P_v, module) = 0`. For right
/// modules `P_v = e_v A`, and evaluation at `e_v` is a bijection
/// `Hom(P_v, X) -> X e_v = X_v`: it is injective because `e_v A` is generated
/// by `e_v`, and surjective because every `m` in `X_v` gives the well defined
/// map `e_v a |-> m a`. So `dim Hom(P_v, X) = dim X_v`, and a basic
/// projective `P` has `Hom(P, module) = 0` exactly when its vertex set sits
/// inside this list.
pub(super) fn support_complement(module: &BasicDecomposition) -> Vec<u32> {
    module
        .module()
        .dim_vector()
        .iter()
        .enumerate()
        .filter(|&(_, &dim)| dim == 0)
        .map(|(vertex, _)| vertex as u32)
        .collect()
}

/// `vertices` as a projective support over the algebra of `module`.
///
/// Every caller passes a subset of [`support_complement`], so the vertices are
/// in range for that algebra.
pub(super) fn as_support(module: &BasicDecomposition, vertices: &[u32]) -> ProjectiveSupport {
    ProjectiveSupport::new(module.module().algebra(), vertices)
        .expect("the support complement lists vertices of the module's own algebra")
}

/// The vertices of the support complement of `module` that `projective` leaves
/// out, in increasing order.
///
/// Meaningful only after condition 2, which puts the vertex set of
/// `projective` inside the complement.
fn omitted_vertices(module: &BasicDecomposition, projective: &ProjectiveSupport) -> Vec<u32> {
    support_complement(module)
        .into_iter()
        .filter(|&v| !projective.contains(v))
        .collect()
}

pub(super) fn checked_omissions(
    module: &BasicDecomposition,
    projective: &ProjectiveSupport,
    limit: usize,
    subject: &str,
) -> Result<Vec<u32>, SupportTauError> {
    let omitted = omitted_vertices(module, projective);
    if omitted.len() > limit {
        return Err(SupportTauError::Defect {
            reason: format!(
                "{subject} with module dimension vectors {:?} and support {:?} left the vertices \
                 {omitted:?} out of the support complement",
                module.dim_vectors(),
                projective.vertices()
            ),
        });
    }
    Ok(omitted)
}

/// Rechecks conditions 3 and 4 against the live parts, and that the stored
/// tau-rigidity witness covers the live summands.
///
/// Conditions 1 and 2 have nothing left to recheck. One algebra value carries
/// both parts, and the support is derived from the support complement of the
/// module part, so it cannot meet the support of `M`. The caller runs
/// [`TauRigidModule::verify`] last.
pub(super) fn recheck_shared(
    module: &BasicDecomposition,
    projective_len: usize,
    rigid: &TauRigidModule,
    expected: usize,
) -> bool {
    verify_guard!(module.len() + projective_len == expected);
    verify_guard!(rigid.summands().len() == module.len());
    rigid
        .summands()
        .iter()
        .zip(module.summands())
        .all(|((_, stored), x)| stored.ptr_eq(x.module()))
}
