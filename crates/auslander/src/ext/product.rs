//! Ext classes, Yoneda products, and product witnesses.

use crate::field::Fp;
use crate::hom::Morphism;
use crate::homspace::{row_times, rref_coords};
use crate::linalg::DenseMat;
use crate::module::{same_morphism_data, same_representation};

use super::foundation::{
    chain_maps, chain_terms, cochain_from_coordinates, coordinates, layout, lift_through,
};
use super::space::{ExtClassError, ExtSpace, product_degree};

/// An element of an [`ExtSpace`]: coordinates over the complement basis.
///
/// Equality and arithmetic require compatible spaces (see
/// [`ExtSpace::is_compatible`]); incompatible operands are a typed
/// [`ExtClassError`], never `false`.
#[derive(Clone, Debug)]
pub struct ExtClass {
    pub(super) space: ExtSpace,
    pub(super) coords: Vec<Fp>,
}

impl ExtClass {
    accessor_methods! {
        /// The space the class lives in.
        pub space() -> &ExtSpace = |this| &this.space;
        /// The coordinates over the complement basis.
        pub coordinates() -> &[Fp] = |this| &this.coords;
    }

    /// Whether every coordinate is zero.
    pub fn is_zero(&self) -> bool {
        self.coords.iter().all(|c| c.is_zero())
    }

    fn with_coordinates(&self, coords: Vec<Fp>) -> ExtClass {
        ExtClass {
            space: self.space.clone(),
            coords,
        }
    }

    fn require_compatible(&self, other: &ExtClass) -> Result<(), ExtClassError> {
        self.space
            .is_compatible(&other.space)
            .then_some(())
            .ok_or(ExtClassError::IncompatibleSpaces)
    }

    /// The sum of two classes. Errors unless the spaces are compatible.
    pub fn add(&self, other: &ExtClass) -> Result<ExtClass, ExtClassError> {
        self.require_compatible(other)?;
        let field = self.space.0.source.field();
        let coords = self
            .coords
            .iter()
            .zip(&other.coords)
            .map(|(&a, &b)| field.add(a, b))
            .collect();
        Ok(self.with_coordinates(coords))
    }

    /// The additive inverse.
    pub fn neg(&self) -> ExtClass {
        let field = self.space.0.source.field();
        self.with_coordinates(self.coords.iter().map(|&c| field.neg(c)).collect())
    }

    /// The scalar multiple. The scalar must be a canonical element of the
    /// modules' field.
    pub fn scale(&self, c: Fp) -> ExtClass {
        let field = self.space.0.source.field();
        self.with_coordinates(self.coords.iter().map(|&x| field.mul(c, x)).collect())
    }

    /// Whether the classes are equal. Errors unless the spaces are
    /// compatible, so incompatible operands never read as unequal.
    pub fn equals(&self, other: &ExtClass) -> Result<bool, ExtClassError> {
        self.require_compatible(other)?;
        Ok(self.coords == other.coords)
    }

    /// The representative cocycle `P_k -> N`: the complement-row combination
    /// of the coordinates.
    pub fn representative(&self) -> Morphism {
        let inner = &self.space.0;
        let field = inner.source.field();
        let row = row_times(&self.coords, &inner.complement, &field);
        let lay = layout(&inner.term);
        cochain_from_coordinates(&inner.term, &lay, &inner.target, &row)
    }

    /// The Yoneda product `Ext^m(M, N) x Ext^n(N, L) -> Ext^{m+n}(M, L)`,
    /// matching the endpoint order of [`Morphism::then`]. Errors when the
    /// middle modules disagree (by [`crate::module::Module::ptr_eq`]).
    ///
    /// Each call builds the product space. To multiply many classes into one
    /// space, build it once and use [`ExtClass::then_in`].
    pub fn then(&self, other: &ExtClass) -> Result<ExtClass, ExtClassError> {
        self.then_with_witness(other).map(|(class, _)| class)
    }

    /// The Yoneda product together with the chain lifts that computed it.
    /// Errors when the middle modules disagree (by
    /// [`crate::module::Module::ptr_eq`]).
    pub fn then_with_witness(
        &self,
        other: &ExtClass,
    ) -> Result<(ExtClass, ProductWitness), ExtClassError> {
        let product_space = self.product_space(other)?;
        self.then_with_witness_in(other, &product_space)
    }

    /// The Yoneda product reduced in `product_space` instead of a fresh one.
    ///
    /// `product_space` must be `Ext^{m+n}(M, L)` for the endpoints of the two
    /// factors: source pointer-equal to this class's source, target
    /// pointer-equal to `other`'s target, degree the sum. A space that fails
    /// any of those is [`ExtClassError::IncompatibleSpaces`]. Recomputed
    /// compatible spaces carry identical bases, so the coordinates are the
    /// ones [`ExtClass::then`] returns.
    pub fn then_in(
        &self,
        other: &ExtClass,
        product_space: &ExtSpace,
    ) -> Result<ExtClass, ExtClassError> {
        self.then_with_witness_in(other, product_space)
            .map(|(class, _)| class)
    }

    /// [`ExtClass::then_in`] with the chain lifts that computed the product.
    pub fn then_with_witness_in(
        &self,
        other: &ExtClass,
        product_space: &ExtSpace,
    ) -> Result<(ExtClass, ProductWitness), ExtClassError> {
        if !self.space.0.target.ptr_eq(&other.space.0.source) {
            return Err(ExtClassError::MiddleMismatch);
        }
        let n = other.space.0.degree;
        let product_degree = product_degree(self.space.0.degree, n)?;
        if !product_space.0.source.ptr_eq(&self.space.0.source)
            || !product_space.0.target.ptr_eq(&other.space.0.target)
            || product_space.0.degree != product_degree
        {
            return Err(ExtClassError::IncompatibleSpaces);
        }
        let lifts = chain_lifts(self, other, product_space)?;
        let g = other.representative();
        let h = lifts[n]
            .then(&g)
            .expect("the last lift targets the right class's cochain term");
        let class = product_space
            .class_from_cocycle(&h)
            .expect("a Yoneda product of cocycles is a cocycle");
        Ok((class, ProductWitness { lifts }))
    }

    /// `Ext^{m+n}(M, L)` for the two factors. Errors when the middle modules
    /// disagree (by [`crate::module::Module::ptr_eq`]) or the degree sum is
    /// not representable.
    pub fn product_space(&self, other: &ExtClass) -> Result<ExtSpace, ExtClassError> {
        if !self.space.0.target.ptr_eq(&other.space.0.source) {
            return Err(ExtClassError::MiddleMismatch);
        }
        let degree = product_degree(self.space.0.degree, other.space.0.degree)?;
        Ok(
            ExtSpace::new(&self.space.0.source, &other.space.0.target, degree)
                .expect("the middle module fixes one algebra and the degree has a successor"),
        )
    }
}

/// The chain lifts `phi_0, ..., phi_n` with `phi_i: P^M_{m+i} -> P^N_i`,
/// `phi_0.then(aug_N) = f` for `f` the representative of `alpha`, and
/// `d^M_{m+i+1}.then(phi_i) = phi_{i+1}.then(d^N_{i+1})` for `0 <= i < n`.
///
/// Both chains are extended by zero modules and zero maps past the end of a
/// finite resolution. Every lift solves per-generator systems with free
/// variables zeroed, so the family is deterministic.
pub(super) fn chain_lifts(
    alpha: &ExtClass,
    beta: &ExtClass,
    product_space: &ExtSpace,
) -> Result<Vec<Morphism>, ExtClassError> {
    let m = alpha.space.0.degree;
    let n = beta.space.0.degree;
    let deep = &product_space.0.resolution;
    // Both prefixes come from `resolve` on the same module, so they must
    // agree term by term. The lifts below transport the representative onto
    // `deep.terms[m]` and would build a morphism over the wrong actions if
    // they did not, so the disagreement is reported, not asserted away.
    let own = &alpha.space.0.resolution;
    for (degree, (x, y)) in own.terms.iter().zip(&deep.terms).enumerate() {
        if !same_representation(x, y) {
            return Err(ExtClassError::ResolutionDisagreement { degree });
        }
    }
    for (k, (x, y)) in own.maps.iter().zip(&deep.maps).enumerate() {
        if !same_morphism_data(x, y) {
            return Err(ExtClassError::ResolutionDisagreement { degree: k + 1 });
        }
    }
    let algebra = alpha.space.0.source.algebra();
    let chain_m = chain_terms(deep, m, m + n, &product_space.0.term, algebra);
    let chain_dm = chain_maps(deep, m, n, &chain_m);
    let res_n = &beta.space.0.resolution;
    let chain_n = chain_terms(res_n, 0, n, &beta.space.0.term, algebra);
    let chain_dn = chain_maps(res_n, 0, n, &chain_n);
    let rep = alpha.representative();
    let nv = algebra.quiver().num_vertices();
    let rep_maps: Vec<DenseMat> = (0..nv).map(|v| rep.map_at(v).clone()).collect();
    let f = Morphism::new(&chain_m[0], &beta.space.0.source, rep_maps)
        .expect("the compared resolution prefix matches, so the representative transports");
    let mut lifts = vec![lift_through(&chain_m[0], &res_n.augmentation, &f)];
    for i in 1..=n {
        let rhs = chain_dm[i - 1]
            .then(&lifts[i - 1])
            .expect("chain endpoints line up by construction");
        lifts.push(lift_through(&chain_m[i], &chain_dn[i - 1], &rhs));
    }
    Ok(lifts)
}

/// The chain lifts behind one Yoneda product, `phi_i: P^M_{m+i} -> P^N_i` in
/// degree order.
#[derive(Clone, Debug)]
pub struct ProductWitness {
    pub(super) lifts: Vec<Morphism>,
}

impl ProductWitness {
    accessor_methods! {
        /// The lifts in degree order, `phi_0` first.
        pub lifts() -> &[Morphism] = |this| &this.lifts;
    }

    /// Rechecks that the lifts tie `alpha` and `beta` to `product`.
    ///
    /// The product space is recomputed from the live endpoint modules and
    /// compared by [`ExtSpace::matches`]. The two factor spaces are
    /// not rechecked: their bases fix what `alpha.representative()` and
    /// `beta.representative()` mean. [`ExtSpace::matches_recomputation`] is
    /// the check for a factor.
    ///
    /// The remaining checks are the two lift identity families and the
    /// reduction of `phi_n.then(g)` to the product coordinates, by
    /// multiplication and coboundary membership. Membership alone is not
    /// enough: on the fixtures here the raw product cocycle already lies in
    /// the complement span, so a tampered coboundary basis still passes the
    /// membership solve and only the space comparison rejects it.
    pub fn verify(&self, alpha: &ExtClass, beta: &ExtClass, product: &ExtClass) -> bool {
        let inner = &product.space.0;
        let_or_false!(Ok(fresh) = ExtSpace::new(&inner.source, &inner.target, inner.degree));
        self.verify_against(alpha, beta, product, &fresh)
    }

    /// [`ProductWitness::verify`] with the product space's recomputation
    /// supplied by the caller.
    ///
    /// `recomputed` must be a fresh [`ExtSpace::new`] over the product
    /// endpoints. This method compares it against `product.space()` with
    /// [`ExtSpace::matches`]. Pass a space already built when verifying many
    /// products in one space.
    pub fn verify_against(
        &self,
        alpha: &ExtClass,
        beta: &ExtClass,
        product: &ExtClass,
        recomputed: &ExtSpace,
    ) -> bool {
        let m = alpha.space.0.degree;
        let n = beta.space.0.degree;
        verify_guard!(
            product.space.0.degree == m + n
                && beta.space.0.source.ptr_eq(&alpha.space.0.target)
                && product.space.0.source.ptr_eq(&alpha.space.0.source)
                && product.space.0.target.ptr_eq(&beta.space.0.target)
                && self.lifts.len() == n + 1
                && product.coords.len() == product.space.dim()
                && product.space.matches(recomputed)
        );
        let deep = &product.space.0.resolution;
        let res_n = &beta.space.0.resolution;
        let field = alpha.space.0.source.field();
        let algebra = alpha.space.0.source.algebra();
        let nv = algebra.quiver().num_vertices();
        let rep = alpha.representative();
        let rep_maps: Vec<DenseMat> = (0..nv).map(|v| rep.map_at(v).clone()).collect();
        let_or_false!(
            Ok(f) = Morphism::new(self.lifts[0].source(), &beta.space.0.source, rep_maps)
        );
        let_or_false!(Ok(lhs) = self.lifts[0].then(&res_n.augmentation));
        verify_guard!(lhs == f);
        let terms_m = chain_terms(deep, m, m + n, &product.space.0.term, algebra);
        let maps_m = chain_maps(deep, m, n, &terms_m);
        let terms_n = chain_terms(res_n, 0, n, &beta.space.0.term, algebra);
        let maps_n = chain_maps(res_n, 0, n, &terms_n);
        verify_guard!(
            maps_m
                .iter()
                .zip(&self.lifts)
                .zip(self.lifts.iter().skip(1).zip(&maps_n))
                .all(|((left, lift), (next_lift, right))| {
                    matches!(
                        (left.then(lift), next_lift.then(right)),
                        (Ok(left), Ok(right)) if left == right
                    )
                })
        );
        let g = beta.representative();
        let_or_false!(Ok(h) = self.lifts[n].then(&g));
        verify_guard!(h.source().ptr_eq(&product.space.0.term));
        let lay = layout(&product.space.0.term);
        let h_coords = coordinates(&h, &lay, &product.space.0.target);
        let expected = row_times(&product.coords, &product.space.0.complement, &field);
        let diff: Vec<Fp> = h_coords
            .iter()
            .zip(&expected)
            .map(|(&a, &b)| field.sub(a, b))
            .collect();
        // The space matched its recomputation above, so its coboundary basis
        // is RREF and the membership solve reads off its pivots.
        rref_coords(&product.space.0.coboundaries, &diff, &field).is_some()
    }
}
