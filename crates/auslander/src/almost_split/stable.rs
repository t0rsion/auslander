use crate::decompose::add_morphisms;
use crate::ext::{ExtClass, ExtSpace, lift_through};
use crate::field::{Fp, PrimeField};
use crate::hom::{Morphism, hom, zero_morphism};
use crate::homspace::{HomQuotient, HomSpace, HomSubspace, scale_morphism};
use crate::indec::IndecomposableModule;
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::resolution::projective_cover;
use crate::sequence::ShortExactSequence;

use super::errors::AlmostSplitError;

/// The subspace of maps in `space` that factor through a projective module.
///
/// By the factorization lemma, this is the image of
/// `Hom(M, P(N)) -> Hom(M, N)`, `h -> h.then(pi_N)`.
pub fn projectively_trivial(space: &HomSpace) -> Result<HomSubspace, AlmostSplitError> {
    let (cover, pi) = projective_cover(space.target());
    let through = hom(space.source(), &cover)?;
    let composites: Vec<Morphism> = through
        .iter()
        .map(|h| h.then(&pi))
        .collect::<Result<_, _>>()?;
    Ok(space.subspace(&composites)?)
}

/// `Hom(M, N)` modulo the projectively trivial maps, with the deterministic
/// complement representatives of [`HomQuotient`].
///
/// # Errors
/// [`AlmostSplitError::Hom`] when the modules do not share one algebra.
pub fn stable_hom(m: &Module, n: &Module) -> Result<HomQuotient, AlmostSplitError> {
    let space = HomSpace::new(m, n)?;
    let trivial = projectively_trivial(&space)?;
    Ok(space.full_subspace().quotient_by(&trivial)?)
}

/// `stable_hom(m, m)`: the stable endomorphism algebra of `m` as a vector
/// space.
pub fn stable_end(m: &Module) -> Result<HomQuotient, AlmostSplitError> {
    stable_hom(m, m)
}

/// The matrix `A_phi` of `Ext^1(phi, N)` in the fixed Ext basis of
/// `space = Ext^1(M, N)`, for `phi` an endomorphism of `M`. Row `i` holds
/// the coordinates of the image of basis class `i`.
///
/// The functor is contravariant, so `A_{phi.then(psi)} = A_psi A_phi`.
pub(in crate::almost_split) fn action_matrix(
    space: &ExtSpace,
    phi: &Morphism,
) -> Result<DenseMat, AlmostSplitError> {
    let d = space.dim();
    if d == 0 {
        return Ok(DenseMat::zero(0, 0));
    }
    let res = space.resolution();
    let rhs0 = res.augmentation.then(phi)?;
    let phi0 = lift_through(&res.terms[0], &res.augmentation, &rhs0);
    let d1 = &res.maps[0];
    let rhs1 = d1.then(&phi0)?;
    let phi1 = lift_through(&res.terms[1], d1, &rhs1);
    let rows: Vec<Vec<Fp>> = space
        .representatives()
        .iter()
        .map(|rep| {
            let moved = phi1.then(rep)?;
            Ok(space.class_from_cocycle(&moved)?.coordinates().to_vec())
        })
        .collect::<Result<_, AlmostSplitError>>()?;
    Ok(DenseMat::from_rows(&rows))
}

/// One [`action_matrix`] per radical basis element of `End(M)`, in radical
/// basis order, over `space = Ext^1(M, tau M)`.
pub(in crate::almost_split) fn action_matrices(
    m: &IndecomposableModule,
    space: &ExtSpace,
) -> Result<Vec<DenseMat>, AlmostSplitError> {
    let endo = m.endo();
    let radical = endo.radical_basis();
    (0..radical.rows())
        .map(|j| action_matrix(space, &endo.morphism(radical.row(j))))
        .collect()
}

/// Whether the sequence and class have the expected endpoints and recover.
pub(in crate::almost_split) fn ext_sequence_holds(
    m: &IndecomposableModule,
    sequence: &ShortExactSequence,
    class: &ExtClass,
) -> bool {
    let space = class.space();
    space.degree() == 1
        && space.source().ptr_eq(m.module())
        && sequence.quotient().ptr_eq(space.source())
        && sequence.sub().ptr_eq(space.target())
        && space.matches_recomputation()
        && ShortExactSequence::new(sequence.inclusion().clone(), sequence.projection().clone())
            .is_ok()
        && matches!(sequence.ext1_class(space), Ok(recovered) if recovered.equals(class) == Ok(true))
}

/// The RREF basis of `{ e : e . r_j = 0 for every j }`: the left kernel of
/// the horizontally stacked action matrices. With no radical elements the
/// socle is the whole space.
pub(in crate::almost_split) fn socle_kernel(
    action: &[DenseMat],
    dim: usize,
    field: &PrimeField,
) -> DenseMat {
    let mut stacked = DenseMat::zero(dim, dim * action.len());
    for (j, a) in action.iter().enumerate() {
        for r in 0..dim {
            for c in 0..dim {
                stacked.set(r, j * dim + c, a.get(r, c));
            }
        }
    }
    stacked.left_kernel_basis(field).into_row_space_basis(field)
}

/// The morphism with the given coordinates over the RREF basis of `sub`, or
/// `None` on a length mismatch.
pub(in crate::almost_split) fn subspace_combination(
    sub: &HomSubspace,
    coords: &[Fp],
) -> Option<Morphism> {
    if coords.len() != sub.dim() {
        return None;
    }
    let mut acc = zero_morphism(sub.source(), sub.target())
        .expect("a subspace's endpoints share one algebra");
    for (k, &c) in coords.iter().enumerate().filter(|(_, c)| !c.is_zero()) {
        acc = add_morphisms(&acc, &scale_morphism(&sub.basis_morphism(k), c));
    }
    Some(acc)
}
