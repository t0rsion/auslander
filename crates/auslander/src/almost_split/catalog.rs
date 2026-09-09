use std::sync::Arc;

use crate::arquiver::{ArQuiverError, IndecomposableCatalog, category_radical};
use crate::ext::ExtClass;
use crate::field::Fp;
use crate::hom::{HomError, Morphism, hom};
use crate::homspace::{HomSpace, HomSubspace};
use crate::indec::IndecomposableModule;
use crate::sequence::ShortExactSequence;

use super::errors::AlmostSplitError;
use super::stable::{ext_sequence_holds, subspace_combination};

/// The stored factorization data of one catalog entry `X`.
///
/// Right side, through `g: E -> M`: coordinates that express each radical
/// basis map of `rad(X, M)` over the image of `Hom(X, E) -> Hom(X, M)`, and
/// coordinates that place each composite `h_i.then(g)` inside `rad(X, M)`.
/// Left side, through `f: tau M -> E`: the same two families for
/// `Hom(E, X) -> Hom(tau M, X)` against `rad(tau M, X)`.
///
/// The left side is provably redundant, not redundant by assumed symmetry.
/// Theorem (Auslander, Reiten, and Smalo V.1.14): for a non-split short exact
/// sequence with indecomposable end terms, right almost split, left almost
/// split, and almost split are equivalent. The right-side equality over an
/// exhaustive catalog already proves `g` right almost split, and both ends are
/// [`crate::indec::IndecomposableModule`] values, so the left side follows. It is computed
/// and stored as an independent check.
#[derive(Clone, Debug)]
pub struct CatalogEntryCheck {
    pub(in crate::almost_split) right_factorizations: Vec<Vec<Fp>>,
    pub(in crate::almost_split) right_memberships: Vec<Vec<Fp>>,
    pub(in crate::almost_split) left_factorizations: Vec<Vec<Fp>>,
    pub(in crate::almost_split) left_memberships: Vec<Vec<Fp>>,
}

impl CatalogEntryCheck {
    accessor_methods! {
        /// Coordinates of each `rad(X, M)` basis map over the RREF basis of
        /// `im(Hom(X, E) -> Hom(X, M))`, in radical basis order.
        pub right_factorizations() -> &[Vec<Fp>] = |this| &this.right_factorizations;
        /// Coordinates of each composite `h_i.then(g)` over the RREF basis of
        /// `rad(X, M)`, in `Hom(X, E)` basis order.
        pub right_memberships() -> &[Vec<Fp>] = |this| &this.right_memberships;
        /// Coordinates of each `rad(tau M, X)` basis map over the RREF basis of
        /// `im(Hom(E, X) -> Hom(tau M, X))`, in radical basis order.
        pub left_factorizations() -> &[Vec<Fp>] = |this| &this.left_factorizations;
        /// Coordinates of each composite `f.then(h_i)` over the RREF basis of
        /// `rad(tau M, X)`, in `Hom(E, X)` basis order.
        pub left_memberships() -> &[Vec<Fp>] = |this| &this.left_memberships;
    }
}

/// The stored data of the exhaustive catalog route: one
/// [`CatalogEntryCheck`] per catalog entry, in catalog order.
///
/// The right-side equality at the entry `X = M` already proves the sequence
/// non-split. `End(M)` is local, so the identity of `M` is not in
/// `rad(M, M)`, and therefore it does not factor through `g`.
#[derive(Clone, Debug)]
pub struct CatalogWitness {
    pub(in crate::almost_split) entries: Vec<CatalogEntryCheck>,
}

/// The per-entry subspaces and composites that the construction and the
/// verification both recompute and compare against.
pub(in crate::almost_split) struct EntryRecompute {
    pub(in crate::almost_split) image: HomSubspace,
    pub(in crate::almost_split) rad: HomSubspace,
    pub(in crate::almost_split) composites: Vec<Morphism>,
    pub(in crate::almost_split) left_image: HomSubspace,
    pub(in crate::almost_split) left_rad: HomSubspace,
    pub(in crate::almost_split) left_composites: Vec<Morphism>,
}

pub(in crate::almost_split) fn radical_maps(radical: &HomSubspace) -> Vec<Morphism> {
    (0..radical.dim())
        .map(|i| radical.basis_morphism(i))
        .collect()
}

pub(in crate::almost_split) fn express(
    over: &HomSubspace,
    maps: &[Morphism],
) -> Result<Vec<Vec<Fp>>, AlmostSplitError> {
    maps.iter()
        .map(|map| {
            Ok(over.witness_contains(map)?.expect(
                "the subspaces were just proved equal, so every map solves; this is a bug in \
                 auslander",
            ))
        })
        .collect()
}

impl EntryRecompute {
    pub(in crate::almost_split) fn verifies(&self, check: &CatalogEntryCheck) -> bool {
        self.image == self.rad
            && self.left_image == self.left_rad
            && family_solves(
                &check.right_factorizations,
                &self.image,
                &radical_maps(&self.rad),
            )
            && family_solves(&check.right_memberships, &self.rad, &self.composites)
            && family_solves(
                &check.left_factorizations,
                &self.left_image,
                &radical_maps(&self.left_rad),
            )
            && family_solves(
                &check.left_memberships,
                &self.left_rad,
                &self.left_composites,
            )
    }

    pub(in crate::almost_split) fn into_check(self) -> Result<CatalogEntryCheck, AlmostSplitError> {
        Ok(CatalogEntryCheck {
            right_factorizations: express(&self.image, &radical_maps(&self.rad))?,
            right_memberships: express(&self.rad, &self.composites)?,
            left_factorizations: express(&self.left_image, &radical_maps(&self.left_rad))?,
            left_memberships: express(&self.left_rad, &self.left_composites)?,
        })
    }
}

pub(in crate::almost_split) fn entry_data(
    maps: &[Morphism],
    compose: impl Fn(&Morphism) -> Result<Morphism, HomError>,
    space: impl FnOnce() -> Result<HomSpace, HomError>,
    radical: impl FnOnce() -> Result<HomSubspace, ArQuiverError>,
) -> Result<(HomSubspace, HomSubspace, Vec<Morphism>), AlmostSplitError> {
    let composites = maps
        .iter()
        .map(compose)
        .collect::<Result<Vec<Morphism>, _>>()
        .map_err(AlmostSplitError::Hom)?;
    let image = space()?.subspace(&composites)?;
    Ok((image, radical()?, composites))
}

pub(in crate::almost_split) fn recompute_entry(
    m: &IndecomposableModule,
    tau_ind: &IndecomposableModule,
    sequence: &ShortExactSequence,
    x: &IndecomposableModule,
) -> Result<EntryRecompute, AlmostSplitError> {
    let (image, rad, composites) = entry_data(
        &hom(x.module(), sequence.middle())?,
        |map| map.then(sequence.projection()),
        || HomSpace::new(x.module(), m.module()),
        || category_radical(x, m),
    )?;
    let (left_image, left_rad, left_composites) = entry_data(
        &hom(sequence.middle(), x.module())?,
        |map| sequence.inclusion().then(map),
        || HomSpace::new(sequence.sub(), x.module()),
        || category_radical(tau_ind, x),
    )?;
    Ok(EntryRecompute {
        image,
        rad,
        composites,
        left_image,
        left_rad,
        left_composites,
    })
}

impl CatalogWitness {
    accessor_methods! {
        /// The per-entry factorization data, in catalog order.
        pub entry_checks() -> &[CatalogEntryCheck] = |this| &this.entries;
    }

    /// Rechecks the witness against the live modules, for every catalog entry
    /// and in both directions.
    ///
    /// The stored coordinates are re-solved, not replayed: the image subspaces
    /// and the category radicals are recomputed, their equality is rechecked,
    /// and every stored factorization and membership vector must rebuild its
    /// morphism over the recomputed RREF basis. The class's [`crate::ext::ExtSpace`] is
    /// rebuilt and compared by [`crate::ext::ExtSpace::matches_recomputation`], because
    /// the class recovery below reduces against its stored bases. The sequence
    /// is also rechecked for exactness through the [`ShortExactSequence`]
    /// constructor, for recovery of the supplied class, and for
    /// indecomposability of the sub module.
    ///
    /// The sequence and class are the caller's, not this witness's own. For
    /// the pair the almost-split value holds, call
    /// [`crate::almost_split::AlmostSplitSequence::verify_with_catalog`].
    pub fn verify(
        &self,
        m: &IndecomposableModule,
        catalog: &IndecomposableCatalog,
        sequence: &ShortExactSequence,
        class: &ExtClass,
    ) -> bool {
        verify_guard!(
            Arc::ptr_eq(m.module().algebra(), catalog.algebra())
                && self.entries.len() == catalog.len()
        );
        verify_guard!(!class.is_zero() && ext_sequence_holds(m, sequence, class));
        let_or_false!(Ok(tau_ind) = IndecomposableModule::new(sequence.sub()));
        for (check, x) in self.entries.iter().zip(catalog.entries()) {
            let_or_false!(Ok(entry) = recompute_entry(m, &tau_ind, sequence, x));
            verify_guard!(entry.verifies(check));
        }
        true
    }
}

/// Whether each stored coordinate vector rebuilds the matching expected
/// morphism over the RREF basis of `over`.
pub(in crate::almost_split) fn family_solves(
    stored: &[Vec<Fp>],
    over: &HomSubspace,
    expected: &[Morphism],
) -> bool {
    stored.len() == expected.len()
        && stored.iter().zip(expected).all(|(coords, target)| {
            matches!(subspace_combination(over, coords), Some(rebuilt) if rebuilt == *target)
        })
}
