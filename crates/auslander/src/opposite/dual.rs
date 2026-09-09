use crate::hom::Morphism;
use crate::module::{Module, same_representation};
use crate::profile::{Site, hit};
use crate::quiver::ArrowId;

use super::types::{OppositeError, OppositeMap};

/// The k-dual `D(M) = Hom_k(M, k)` of a module over either side of `op`, as a
/// module over the other side: same dimension vector, `DM(a^op) = M(a)ᵀ`.
/// `dual(&dual(m, op)?, op)?` restores `m` entry for entry, over the same
/// algebra [`std::sync::Arc`].
pub fn dual(m: &Module, op: &OppositeMap) -> Result<Module, OppositeError> {
    hit(Site::Dual);
    let target = op.other_side(m.algebra())?.clone();
    let maps = (0..m.algebra().quiver().num_arrows())
        .map(|i| m.map(ArrowId(i as u32)).transpose())
        .collect();
    Ok(Module::new(target, m.dim_vector().to_vec(), maps)
        .expect("a reversed relation acts by the transposed original combination, which is zero"))
}

/// The dual `D(f): D(N) → D(M)` of `f: M → N`, with matrix `f_vᵀ` at each
/// vertex.
///
/// Module identity is nominal, so the caller passes its own dual modules
/// `dual_of_target = D(N)` and `dual_of_source = D(M)`. Both are checked entry
/// for entry against [`dual`]. Dualized composites then share endpoints and
/// compose. Contravariance: dualizing `f.then(g)` against the outer duals
/// equals `dual_morphism` of `g` followed by that of `f` through the shared
/// dual of the middle module.
pub fn dual_morphism(
    f: &Morphism,
    dual_of_target: &Module,
    dual_of_source: &Module,
    op: &OppositeMap,
) -> Result<Morphism, OppositeError> {
    if !same_representation(dual_of_target, &dual(f.target(), op)?) {
        return Err(OppositeError::NotDualOfTarget);
    }
    if !same_representation(dual_of_source, &dual(f.source(), op)?) {
        return Err(OppositeError::NotDualOfSource);
    }
    let maps = (0..f.source().algebra().quiver().num_vertices())
        .map(|v| f.map_at(v).transpose())
        .collect();
    Ok(Morphism::new(dual_of_target, dual_of_source, maps)
        .expect("transposing every matrix of an A-linearity square transposes the square"))
}
