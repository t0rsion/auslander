use super::helpers::{factor_through_epi, negate};
use super::{SequenceError, ShortExactSequence};
use crate::decompose::add_morphisms;
use crate::ext::{ExtClass, ExtSpace, lift_through};
use crate::hom::{
    Morphism, cokernel, express_in_row_basis, factor_through_monomorphism, image, zero_morphism,
};
use crate::module::{Module, direct_sum};

impl ShortExactSequence {
    /// The extension realizing a class in `Ext^1(M, N)`, built as a pushout.
    ///
    /// Take `K = im d_1` with its inclusion `kappa: K -> P_0` and the
    /// surjection `s: P_1 -> K`, then factor the representative cocycle as
    /// `c = s.then(c_bar)`. The middle term is the cokernel of
    /// `(c_bar, -kappa): K -> N (+) P_0`. The zero class gives the split
    /// sequence. The result passes through [`ShortExactSequence::new`], so it
    /// is exact by construction.
    ///
    /// # Errors
    /// [`SequenceError::WrongDegree`] when the class degree is not 1.
    pub fn from_ext1(class: &ExtClass) -> Result<ShortExactSequence, SequenceError> {
        let space = class.space();
        if space.degree() != 1 {
            return Err(SequenceError::WrongDegree {
                expected: 1,
                got: space.degree(),
            });
        }
        let m = space.source();
        let n = space.target();
        let res = space.resolution();
        let field = m.field();
        let nv = m.algebra().quiver().num_vertices();
        let p0 = &res.terms[0];
        let c = class.representative();
        let (kappa, c_bar) = match res.maps.first() {
            Some(d1) => {
                let (k_mod, kappa) = image(d1);
                let s_maps = (0..nv)
                    .map(|v| express_in_row_basis(kappa.map_at(v), d1.map_at(v), &field))
                    .collect();
                let s = Morphism::new(d1.source(), &k_mod, s_maps)
                    .expect("the corestriction of d_1 to its image is A-linear");
                let c_bar = factor_through_epi(&s, &c);
                (kappa, c_bar)
            }
            None => {
                // A projective quotient has no d_1, so K is the zero module.
                let k_mod = Module::zero(m.algebra());
                let kappa =
                    zero_morphism(&k_mod, p0).expect("the zero module is built over m's algebra");
                let c_bar =
                    zero_morphism(&k_mod, n).expect("the zero module is built over m's algebra");
                (kappa, c_bar)
            }
        };
        let (_sum, inclusions, projections) = direct_sum(&[n, p0]);
        let mu = add_morphisms(
            &c_bar
                .then(&inclusions[0])
                .expect("the sum inclusion starts at N"),
            &negate(&kappa)
                .then(&inclusions[1])
                .expect("the sum inclusion starts at P_0"),
        );
        let (_e, q) = cokernel(&mu);
        let iota = inclusions[0]
            .then(&q)
            .expect("the cokernel projection starts at the sum");
        let w = projections[1]
            .then(&res.augmentation)
            .expect("the augmentation starts at P_0");
        let pi = factor_through_epi(&q, &w);
        ShortExactSequence::new(iota, pi)
    }

    /// The class of this extension in `space = Ext^1(quotient, sub)`.
    ///
    /// The recovery lifts the augmentation through the projection, pulls
    /// `d_1.then(lift)` back through the inclusion, and reduces the resulting
    /// cocycle.
    ///
    /// # Errors
    /// [`SequenceError::WrongDegree`] when the space's degree is not 1, and
    /// [`SequenceError::SpaceSourceMismatch`] or
    /// [`SequenceError::SpaceTargetMismatch`] when the space's endpoints are
    /// not this sequence's quotient and sub (by [`Module::ptr_eq`]).
    pub fn ext1_class(&self, space: &ExtSpace) -> Result<ExtClass, SequenceError> {
        if space.degree() != 1 {
            return Err(SequenceError::WrongDegree {
                expected: 1,
                got: space.degree(),
            });
        }
        if !space.source().ptr_eq(&self.quotient) {
            return Err(SequenceError::SpaceSourceMismatch);
        }
        if !space.target().ptr_eq(&self.sub) {
            return Err(SequenceError::SpaceTargetMismatch);
        }
        let res = space.resolution();
        let Some(d1) = res.maps.first() else {
            return Ok(space
                .class_from_coordinates(&[])
                .expect("a projective quotient has the zero Ext^1 space"));
        };
        let h = lift_through(&res.terms[0], &self.projection, &res.augmentation);
        let d1h = d1.then(&h).expect("d_1 targets P_0");
        let c = factor_through_monomorphism(&self.inclusion, &d1h);
        Ok(space
            .class_from_cocycle(&c)
            .expect("the recovered cochain is a cocycle; failure is a bug in auslander"))
    }
}
