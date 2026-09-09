use crate::basic::{BasicDecomposition, BasicError};
use crate::decompose::{Certificate, Decomposition, decompose};
use crate::indec::IndecomposableModule;
use crate::iso::indecomposable_iso;
use crate::module::Module;
use crate::supporttau::SupportTauTiltingPair;

use super::error::{MutationDefect, MutationError, defect};
use super::witness::ExchangeShape;

/// The parts of the target pair the shape decision produces.
pub(super) struct BuiltTarget {
    pub(super) decomposition: BasicDecomposition,
    pub(super) vertices: Vec<u32>,
    pub(super) shape: ExchangeShape,
    // Y_1, present exactly for ExchangeShape::ReplacedByModule.
    pub(super) replacement: Option<Module>,
}

pub(super) fn validated_exchange(
    pair: &SupportTauTiltingPair,
    y: &Module,
) -> Result<(Decomposition, IndecomposableModule), MutationError> {
    let split = decompose(y);
    for certificate in split.certificates() {
        if let Certificate::Undetermined { attempts } = certificate {
            return Err(MutationError::Basic(BasicError::CertificationBlocked {
                reason: format!(
                    "a cokernel summand stayed undetermined after {attempts} split attempts"
                ),
            }));
        }
    }
    let exchange =
        IndecomposableModule::from_endo(split.endos()[0].clone()).map_err(MutationError::Indec)?;
    for (position, other) in split.summands().iter().enumerate().skip(1) {
        if indecomposable_iso(exchange.module(), other, exchange.endo()).is_none() {
            return Err(defect(MutationDefect::CokernelSummandsDiffer {
                summand: position,
            }));
        }
    }
    // AIR Theorem 2.30(b) puts Y outside add(T), so it differs from X_j.
    for (position, other) in pair.module().summands().iter().enumerate() {
        if indecomposable_iso(exchange.module(), other.module(), exchange.endo()).is_some() {
            return Err(defect(MutationDefect::ReplacementRepeatsSummand {
                summand: position,
            }));
        }
    }
    Ok((split, exchange))
}

/// The target parts, picked by the shape and cross-checked against AIR Theorem
/// 2.30.
///
/// `dropped` is `supp(M) \ supp(U)` and `y` is the cokernel of the
/// approximation. An empty `dropped` is the sincere case, where the cokernel
/// carries the exchange.
///
/// The target decomposition is built from `u_dec`, never decomposed again:
/// the module part is `U` itself, or `U` plus the one certified cokernel
/// summand `Y_1`.
pub(super) fn build_target(
    pair: &SupportTauTiltingPair,
    u_dec: &BasicDecomposition,
    y: &Module,
    dropped: &[u32],
) -> Result<BuiltTarget, MutationError> {
    if let Some((&vertex, rest)) = dropped.split_first() {
        if !rest.is_empty() {
            return Err(defect(MutationDefect::DroppedVertexCount {
                dropped: dropped.to_vec(),
            }));
        }
        if !y.is_zero() {
            return Err(defect(MutationDefect::CokernelNonzero {
                dim_vector: y.dim_vector().to_vec(),
            }));
        }
        let mut vertices = pair.projective().vertices().to_vec();
        vertices.push(vertex);
        vertices.sort_unstable();
        return Ok(BuiltTarget {
            decomposition: u_dec.clone(),
            vertices,
            shape: ExchangeShape::MovesToProjective { vertex },
            replacement: None,
        });
    }
    if y.is_zero() {
        return Err(defect(MutationDefect::CokernelZero));
    }
    let (split, exchange) = validated_exchange(pair, y)?;
    Ok(BuiltTarget {
        decomposition: u_dec
            .with_new_summand(&exchange)
            .map_err(MutationError::Basic)?,
        vertices: pair.projective().vertices().to_vec(),
        shape: ExchangeShape::ReplacedByModule {
            multiplicity: split.summands().len(),
        },
        replacement: Some(exchange.module().clone()),
    })
}
