//! Explicit Ext-space construction and class-coordinate reduction.

use std::sync::Arc;

use crate::field::Fp;
use crate::hom::Morphism;
use crate::homspace::{deterministic_complement, rref_coords_many, stack_rows};
use crate::linalg::DenseMat;
use crate::module::{Module, same_morphism_data, same_representation, same_slice};
use crate::resolution::{ProjectiveResolution, resolve};

use super::foundation::{
    ExtError, check_pair, cochain_from_coordinates, coordinates, delta_matrix, hom_space_dim,
    layout,
};
use super::product::ExtClass;

/// Rejected Ext class input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtClassError {
    /// The operands' spaces are not compatible: compatibility needs
    /// pointer-equal sources, pointer-equal targets, and equal degrees.
    IncompatibleSpaces,
    /// The left class's target module is not the right class's source module
    /// (by [`Module::ptr_eq`]), so the Yoneda product is undefined.
    MiddleMismatch,
    /// The sum of the two class degrees is not representable.
    DegreeOverflow { left: usize, right: usize },
    /// The cochain's source is not the space's cochain term (by
    /// [`Module::ptr_eq`]).
    SourceMismatch,
    /// The cochain's target is not the space's target module (by
    /// [`Module::ptr_eq`]).
    TargetMismatch,
    /// The cochain is not a cocycle: `d_{k+1}.then(f)` is nonzero. The field
    /// holds the composite's coordinates in the degree `k + 1` cochain basis.
    NotCocycle { composite: Vec<Fp> },
    /// The coordinate vector's length is not the space's dimension.
    CoordinateCountMismatch { expected: usize, got: usize },
    /// The coordinate at this index is not a canonical element of the
    /// modules' field.
    NonCanonicalCoordinate { index: usize },
    /// The identity class lives only in `Ext^0(M, M)`: degree 0 with
    /// pointer-equal endpoints.
    NotDegreeZeroEndo,
    /// The left class's resolution prefix and the product space's prefix
    /// disagree at this degree, in the term or in the differential into it.
    /// Both come from [`resolve`] on the same module, so a disagreement is a
    /// crate defect, not bad input.
    ResolutionDisagreement { degree: usize },
}

display_error! { error ExtClassError {
    Self::IncompatibleSpaces => "the classes live in incompatible Ext spaces";
    Self::MiddleMismatch => "the left class's target module is not the right class's source module";
    Self::DegreeOverflow { left, right } => "Ext degree sum {left} + {right} is not representable";
    Self::SourceMismatch => "the cochain's source is not the space's cochain term";
    Self::TargetMismatch => "the cochain's target is not the space's target module";
    Self::NotCocycle { .. } => "the cochain is not a cocycle";
    Self::CoordinateCountMismatch { expected, got } => "coordinate vector has {got} entries, the space has dimension {expected}";
    Self::NonCanonicalCoordinate { index } => "coordinate {index} is not a canonical element of the modules' field";
    Self::NotDegreeZeroEndo => "the identity class lives only in Ext^0(M, M)";
    Self::ResolutionDisagreement { degree } => "two resolutions of one module disagree at degree {degree}; crate defect";
} }

pub(super) fn product_degree(left: usize, right: usize) -> Result<usize, ExtClassError> {
    left.checked_add(right)
        .filter(|&degree| degree != usize::MAX)
        .ok_or(ExtClassError::DegreeOverflow { left, right })
}

pub(super) struct ExtSpaceInner {
    pub(super) source: Module,
    pub(super) target: Module,
    pub(super) degree: usize,
    // resolve(source, degree + 1); minimal, so recomputation gives the same
    // matrices.
    pub(super) resolution: ProjectiveResolution,
    // P_k, or the zero module when the finite resolution ends before k.
    pub(super) term: Module,
    // RREF basis of Z^k = ker delta^k in generator-block coordinates.
    pub(super) cocycles: DenseMat,
    // RREF basis of B^k = im delta^{k-1}; zero rows at degree 0.
    pub(super) coboundaries: DenseMat,
    // Deterministic complement of B^k in Z^k.
    pub(super) complement: DenseMat,
    // One cocycle morphism P_k -> N per complement row.
    pub(super) reps: Vec<Morphism>,
}

/// `Ext^k(M, N)` as an explicit vector space: the resolution prefix, RREF
/// cocycle and coboundary bases in generator-block coordinates, the
/// deterministic complement of the coboundaries inside the cocycles, and one
/// representative cocycle per complement row.
///
/// Two spaces are compatible when their sources are [`Module::ptr_eq`], their
/// targets are [`Module::ptr_eq`], and their degrees are equal. Every stored
/// matrix is deterministic, so recomputed compatible spaces carry identical
/// bases and class coordinates transport verbatim.
///
/// Cloning is cheap (a reference count bump).
#[derive(Clone)]
pub struct ExtSpace(pub(super) Arc<ExtSpaceInner>);

debug_fields!(ExtSpace |this| {
    "source_dim" => this.0.source.dim_vector();
    "target_dim" => this.0.target.dim_vector();
    "degree" => this.0.degree;
    "dim" => this.dim();
});

impl ExtSpace {
    /// Builds `Ext^k(m, n)` from the minimal resolution prefix
    /// `resolve(m, k + 1)`. Zero modules give zero spaces. A finite resolution
    /// that ends before degree `k` gives the zero space with the zero module
    /// as cochain term. Errors when the modules do not share one algebra or
    /// `k + 1` is not representable.
    pub fn new(m: &Module, n: &Module, k: usize) -> Result<ExtSpace, ExtError> {
        check_pair(m, n)?;
        let field = m.field();
        let steps = k
            .checked_add(1)
            .ok_or(ExtError::DegreeOverflow { degree: k })?;
        let resolution = resolve(m, steps);
        let (term, cocycles, coboundaries) = if k < resolution.terms.len() {
            let term = resolution.terms[k].clone();
            let lay = layout(&term);
            let width = hom_space_dim(&lay, n);
            let cocycles = if k + 1 < resolution.terms.len() {
                let next_lay = layout(&resolution.terms[k + 1]);
                let delta = delta_matrix(&resolution.maps[k], &term, &lay, &next_lay, n);
                delta.left_kernel_basis(&field).into_row_space_basis(&field)
            } else {
                DenseMat::identity(width)
            };
            let coboundaries = if k == 0 {
                DenseMat::zero(0, width)
            } else {
                let prev = &resolution.terms[k - 1];
                let prev_lay = layout(prev);
                delta_matrix(&resolution.maps[k - 1], prev, &prev_lay, &lay, n)
                    .into_row_space_basis(&field)
            };
            (term, cocycles, coboundaries)
        } else {
            (
                Module::zero(m.algebra()),
                DenseMat::zero(0, 0),
                DenseMat::zero(0, 0),
            )
        };
        assert!(
            rref_coords_many(&cocycles, &coboundaries, &field).is_some(),
            "im delta^{} is not contained in ker delta^{k}; this is a bug in auslander",
            k.wrapping_sub(1)
        );
        let complement = deterministic_complement(&cocycles, &coboundaries, &field);
        let lay = layout(&term);
        let reps = (0..complement.rows())
            .map(|r| cochain_from_coordinates(&term, &lay, n, complement.row(r)))
            .collect();
        Ok(ExtSpace(Arc::new(ExtSpaceInner {
            source: m.clone(),
            target: n.clone(),
            degree: k,
            resolution,
            term,
            cocycles,
            coboundaries,
            complement,
            reps,
        })))
    }

    accessor_methods! {
        /// `dim_Fp Ext^k(M, N)`: the number of complement rows. Equals
        /// [`crate::ext::ext_dim`](m, n, k).
        pub dim() -> usize = |this| this.0.complement.rows();
        /// The source module `M`.
        pub source() -> &Module = |this| &this.0.source;
        /// The target module `N`.
        pub target() -> &Module = |this| &this.0.target;
        /// The cohomological degree `k`.
        pub degree() -> usize = |this| this.0.degree;
        /// The source of degree-`k` cochains: `P_k` of the minimal resolution, or
        /// the zero module when the finite resolution ends before `k`.
        pub cochain_term() -> &Module = |this| &this.0.term;
        /// One representative cocycle `P_k -> N` per complement row, in row order.
        pub representatives() -> &[Morphism] = |this| &this.0.reps;
        /// The RREF basis of `Z^k = ker delta^k` in generator-block coordinates,
        /// one vector per row.
        pub cocycle_basis() -> &DenseMat = |this| &this.0.cocycles;
        /// The RREF basis of `B^k = im delta^{k-1}` in generator-block
        /// coordinates, one vector per row; no rows at degree 0.
        pub coboundary_basis() -> &DenseMat = |this| &this.0.coboundaries;
        /// The complement of `B^k` in `Z^k`, in scan order. Class coordinates
        /// index these rows.
        pub complement_basis() -> &DenseMat = |this| &this.0.complement;
        /// The stored resolution prefix `resolve(source, degree + 1)`.
        pub(crate) resolution() -> &ProjectiveResolution = |this| &this.0.resolution;
    }

    /// Whether class coordinates transport verbatim between the two spaces:
    /// sources pointer-equal, targets pointer-equal, degrees equal.
    pub fn is_compatible(&self, other: &ExtSpace) -> bool {
        self.0.source.ptr_eq(&other.0.source)
            && self.0.target.ptr_eq(&other.0.target)
            && self.0.degree == other.0.degree
    }

    /// Whether the two compatible spaces carry the same stored data: the
    /// resolution prefix term by term and differential by differential, the
    /// cochain term, the cocycle, coboundary and complement bases, and the
    /// representatives.
    ///
    /// Incompatible spaces are never equal. Terms and representatives are
    /// compared entry by entry, because a recomputed space owns fresh module
    /// values that no pointer test can match.
    pub fn matches(&self, other: &ExtSpace) -> bool {
        let (a, b) = (&*self.0, &*other.0);
        self.is_compatible(other)
            && a.resolution.agrees_with(&b.resolution)
            && same_representation(&a.term, &b.term)
            && a.cocycles == b.cocycles
            && a.coboundaries == b.coboundaries
            && a.complement == b.complement
            && same_slice(&a.reps, &b.reps, same_morphism_data)
    }

    /// Whether every stored matrix equals a fresh [`ExtSpace::new`] over the
    /// live endpoint modules, by [`ExtSpace::matches`].
    ///
    /// Rechecks that read this space (action matrices, socle, cocycle
    /// reduction) use the stored resolution and bases, so a tampered space
    /// would otherwise certify itself.
    pub fn matches_recomputation(&self) -> bool {
        let_or_false!(Ok(fresh) = ExtSpace::new(&self.0.source, &self.0.target, self.0.degree));
        self.matches(&fresh)
    }

    /// The zero class of this space.
    pub fn zero_class(&self) -> ExtClass {
        ExtClass {
            space: self.clone(),
            coords: vec![Fp::ZERO; self.dim()],
        }
    }

    /// The Yoneda unit: the class of the augmentation in `Ext^0(M, M)`.
    /// Errors unless the space has degree 0 and pointer-equal endpoints.
    pub fn identity_class(&self) -> Result<ExtClass, ExtClassError> {
        if self.0.degree != 0 || !self.0.source.ptr_eq(&self.0.target) {
            return Err(ExtClassError::NotDegreeZeroEndo);
        }
        self.class_from_cocycle(&self.0.resolution.augmentation)
    }

    /// The class of the cocycle `f: P_k -> N`: checks both endpoints by
    /// [`Module::ptr_eq`], checks `d_{k+1}.then(f) = 0`, then reduces modulo
    /// `B^k` by solving `f` against the complement rows stacked above the
    /// coboundary basis and keeping the complement part.
    pub fn class_from_cocycle(&self, f: &Morphism) -> Result<ExtClass, ExtClassError> {
        let inner = &self.0;
        if !f.source().ptr_eq(&inner.term) {
            return Err(ExtClassError::SourceMismatch);
        }
        if !f.target().ptr_eq(&inner.target) {
            return Err(ExtClassError::TargetMismatch);
        }
        let field = inner.source.field();
        if inner.degree + 1 < inner.resolution.terms.len() {
            let composite = inner.resolution.maps[inner.degree]
                .then(f)
                .expect("d_{k+1} targets the cochain term");
            if !composite.is_zero() {
                let next_lay = layout(&inner.resolution.terms[inner.degree + 1]);
                return Err(ExtClassError::NotCocycle {
                    composite: coordinates(&composite, &next_lay, &inner.target),
                });
            }
        }
        let lay = layout(&inner.term);
        let f_coords = coordinates(f, &lay, &inner.target);
        let stacked = stack_rows(
            &[&inner.complement, &inner.coboundaries],
            inner.complement.cols(),
        );
        let x = stacked
            .transpose()
            .solve(&f_coords, &field)
            .expect("a cocycle lies in the span of the complement plus the coboundaries; this is a bug in auslander");
        Ok(ExtClass {
            space: self.clone(),
            coords: x[..inner.complement.rows()].to_vec(),
        })
    }

    /// A copy of the space with the three stored bases replaced and the
    /// representatives rebuilt from the new complement.
    ///
    /// Test helper for the mutation corpus: the result is an `ExtSpace` value
    /// that no constructor would produce, so [`ExtSpace::matches_recomputation`]
    /// must reject it.
    #[cfg(test)]
    pub(crate) fn with_bases(
        &self,
        cocycles: DenseMat,
        coboundaries: DenseMat,
        complement: DenseMat,
    ) -> ExtSpace {
        let inner = &self.0;
        let lay = layout(&inner.term);
        let reps = (0..complement.rows())
            .map(|r| cochain_from_coordinates(&inner.term, &lay, &inner.target, complement.row(r)))
            .collect();
        self.with_parts(cocycles, coboundaries, complement, reps)
    }

    /// A copy of the space with the representatives replaced and every basis
    /// kept. Test helper for the mutation corpus, as [`ExtSpace::with_bases`].
    #[cfg(test)]
    pub(crate) fn with_representatives(&self, reps: Vec<Morphism>) -> ExtSpace {
        let inner = &self.0;
        self.with_parts(
            inner.cocycles.clone(),
            inner.coboundaries.clone(),
            inner.complement.clone(),
            reps,
        )
    }

    #[cfg(test)]
    fn with_parts(
        &self,
        cocycles: DenseMat,
        coboundaries: DenseMat,
        complement: DenseMat,
        reps: Vec<Morphism>,
    ) -> ExtSpace {
        let inner = &self.0;
        ExtSpace(Arc::new(ExtSpaceInner {
            source: inner.source.clone(),
            target: inner.target.clone(),
            degree: inner.degree,
            resolution: ProjectiveResolution {
                terms: inner.resolution.terms.clone(),
                maps: inner.resolution.maps.clone(),
                augmentation: inner.resolution.augmentation.clone(),
                end: inner.resolution.end,
            },
            term: inner.term.clone(),
            cocycles,
            coboundaries,
            complement,
            reps,
        }))
    }

    /// The class with the given coordinates over the complement basis.
    /// Errors on a wrong length and on entries that are not canonical
    /// elements of the modules' field.
    pub fn class_from_coordinates(&self, coords: &[Fp]) -> Result<ExtClass, ExtClassError> {
        if coords.len() != self.dim() {
            return Err(ExtClassError::CoordinateCountMismatch {
                expected: self.dim(),
                got: coords.len(),
            });
        }
        let modulus = self.0.source.field().modulus();
        if let Some(index) = coords.iter().position(|c| c.raw() >= modulus) {
            return Err(ExtClassError::NonCanonicalCoordinate { index });
        }
        Ok(ExtClass {
            space: self.clone(),
            coords: coords.to_vec(),
        })
    }
}
