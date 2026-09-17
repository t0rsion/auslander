//! Coordinates a module against a complete indecomposable catalog.
//!
//! [`coordinates`] decomposes the module, matches each certified summand to a
//! catalog entry, and records the multiplicity vector. A catalog theorem
//! makes a full scan with no match a defect. An undetermined decomposition or
//! isomorphism comparison stays [`CatalogCoordinateOutcome::Unknown`].

use std::sync::Arc;

use crate::algebra::Algebra;
use crate::arquiver::{CatalogProvenance, IndecomposableCatalog};
use crate::decompose::{Certificate, Decomposition, decompose};
use crate::hom::{HomError, Morphism};
use crate::iso::{IsoOutcome, is_isomorphic};
use crate::module::Module;

/// Limits for matching one module against a catalog.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CatalogCoordinateLimits {
    /// Maximum number of catalog isomorphism checks, excluding decomposition work.
    pub max_work_units: usize,
}

impl Default for CatalogCoordinateLimits {
    fn default() -> Self {
        Self {
            max_work_units: usize::MAX,
        }
    }
}

/// Why coordinate matching stopped at a caller limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CatalogCoordinateCutReason {
    /// The next catalog isomorphism check would exceed the work limit.
    WorkLimit { limit: usize },
}

display_error! { CatalogCoordinateCutReason {
    Self::WorkLimit { limit } => "catalog coordinate work limit {limit} reached";
} }

/// Why coordinate matching could not certify a complete result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CatalogCoordinateUnknown {
    /// A summand decomposition certificate did not decide indecomposability.
    UndeterminedSummand { summand: usize, attempts: u32 },
    /// A generic isomorphism comparison returned no decision.
    Isomorphism {
        summand: usize,
        catalog_entry: usize,
        reason: String,
    },
}

display_error! { CatalogCoordinateUnknown {
    Self::UndeterminedSummand { summand, attempts } => "summand {summand} stayed undetermined after {attempts} split attempts";
    Self::Isomorphism { summand, catalog_entry, reason } => "isomorphism of summand {summand} with catalog entry {catalog_entry} is undetermined: {reason}";
} }

/// A rejected coordinate request or a failed catalog theorem check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CatalogCoordinateError {
    /// The module uses another prime field than the catalog algebra.
    FieldMismatch { catalog: u64, module: u64 },
    /// The module and catalog use distinct algebra values over one field.
    DifferentAlgebra,
    /// A checked isomorphism call failed for one summand and entry.
    Isomorphism {
        summand: usize,
        catalog_entry: usize,
        error: HomError,
    },
    /// Every catalog entry was proved non-isomorphic to a certified summand.
    /// This contradicts the completeness theorem carried by the catalog.
    CatalogInvariantViolation {
        summand: usize,
        dim_vector: Vec<usize>,
    },
    /// A multiplicity counter overflowed while accumulating a checked split.
    MultiplicityOverflow { catalog_entry: usize },
    /// The completed matching check counter overflowed.
    WorkOverflow,
}

display_error! { CatalogCoordinateError {
    Self::FieldMismatch { catalog, module } => "the catalog uses F_{catalog}, the module uses F_{module}";
    Self::DifferentAlgebra => "the module and catalog use different algebra values";
    Self::Isomorphism { summand, catalog_entry, error } => "isomorphism check for summand {summand} and catalog entry {catalog_entry} failed: {error}";
    Self::CatalogInvariantViolation { summand, dim_vector } => "certified summand {summand} with dimension vector {dim_vector:?} matches no catalog entry; catalog theorem invariant failed";
    Self::MultiplicityOverflow { catalog_entry } => "multiplicity for catalog entry {catalog_entry} overflows usize";
    Self::WorkOverflow => "catalog coordinate work counter overflows usize";
} }

error_source! { CatalogCoordinateError {
    Self::Isomorphism { error, .. } => Some(error),
    Self::FieldMismatch { .. }
    | Self::DifferentAlgebra
    | Self::CatalogInvariantViolation { .. }
    | Self::MultiplicityOverflow { .. }
    | Self::WorkOverflow => None,
} }

/// One checked isomorphism from a decomposed summand to a catalog entry.
#[derive(Clone, Debug)]
pub struct CatalogCoordinateMatch {
    summand: usize,
    catalog_entry: usize,
    witness: Morphism,
}

impl CatalogCoordinateMatch {
    accessor_methods! {
        /// The summand position in [`CatalogCoordinateProgress::decomposition`].
        pub summand() -> usize = |this| this.summand;
        /// The catalog entry matched by the summand.
        pub catalog_entry() -> usize = |this| this.catalog_entry;
        /// The checked isomorphism from the summand to the catalog entry.
        pub witness() -> &Morphism = |this| &this.witness;
    }
}

/// Checked prefix data for an exact, unknown, or cut coordinate result.
#[derive(Clone, Debug)]
pub struct CatalogCoordinateProgress {
    decomposition: Decomposition,
    multiplicities: Vec<usize>,
    matches: Vec<CatalogCoordinateMatch>,
    work_units: usize,
}

impl CatalogCoordinateProgress {
    accessor_methods! {
        /// The verified decomposition used by coordinate matching.
        pub decomposition() -> &Decomposition = |this| &this.decomposition;
        /// Multiplicities certified so far, in catalog order.
        pub multiplicities() -> &[usize] = |this| &this.multiplicities;
        /// Checked summand matches certified so far.
        pub matches() -> &[CatalogCoordinateMatch] = |this| &this.matches;
        /// The number of completed catalog isomorphism checks.
        pub work_units() -> usize = |this| this.work_units;
    }

    /// Whether the stored prefix and all stored witnesses are consistent.
    pub fn verify(&self, catalog: &IndecomposableCatalog, module: &Module) -> bool {
        verify_progress(self, catalog, module)
    }
}

/// Complete catalog coordinates with decomposition and isomorphism evidence.
#[derive(Clone, Debug)]
pub struct CatalogCoordinates {
    algebra: Arc<Algebra>,
    provenance: CatalogProvenance,
    progress: CatalogCoordinateProgress,
}

impl CatalogCoordinates {
    accessor_methods! {
        /// The algebra named by the coordinate result.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The completeness theorem carried by the catalog.
        pub provenance() -> CatalogProvenance = |this| this.provenance;
        /// The exact multiplicity vector in catalog order.
        pub multiplicities() -> &[usize] = |this| &this.progress.multiplicities;
        /// The verified decomposition of the input module.
        pub decomposition() -> &Decomposition = |this| &this.progress.decomposition;
        /// One checked isomorphism per decomposed summand, in summand order.
        pub matches() -> &[CatalogCoordinateMatch] = |this| &this.progress.matches;
        /// The completed catalog isomorphism checks.
        pub work_units() -> usize = |this| this.progress.work_units;
    }

    /// Rechecks the decomposition, multiplicities, and every isomorphism witness.
    pub fn verify(&self, catalog: &IndecomposableCatalog, module: &Module) -> bool {
        Arc::ptr_eq(&self.algebra, catalog.algebra())
            && self.provenance == catalog.provenance()
            && verify_progress(&self.progress, catalog, module)
            && self.progress.matches.len() == self.progress.decomposition.summands().len()
            && self.progress.decomposition.certificates().len()
                == self.progress.decomposition.summands().len()
            && self
                .progress
                .decomposition
                .certificates()
                .iter()
                .all(|c| matches!(c, Certificate::Indecomposable))
    }
}

/// The result of a catalog coordinate request.
#[derive(Clone, Debug)]
pub enum CatalogCoordinateOutcome {
    /// Every summand matched one catalog entry.
    Exact(CatalogCoordinates),
    /// Decomposition or isomorphism matching returned no certified decision.
    Unknown {
        /// The checked prefix available before the undecided operation.
        progress: CatalogCoordinateProgress,
        /// The operation that stayed undecided.
        reason: CatalogCoordinateUnknown,
    },
    /// Matching stopped before the next catalog entry could be checked.
    Cut {
        /// The checked prefix available at the limit.
        progress: CatalogCoordinateProgress,
        /// The limit that stopped matching.
        reason: CatalogCoordinateCutReason,
    },
}

impl CatalogCoordinateOutcome {
    optional_accessors! {
        /// The complete coordinates, if matching finished.
        pub exact() -> &CatalogCoordinates = Self::Exact(value) => value;
    }

    /// The checked prefix produced by the request.
    pub fn progress(&self) -> &CatalogCoordinateProgress {
        match self {
            Self::Exact(value) => &value.progress,
            Self::Unknown { progress, .. } | Self::Cut { progress, .. } => progress,
        }
    }

    /// Whether the request produced an exact multiplicity vector.
    pub fn is_exact(&self) -> bool {
        matches!(self, Self::Exact(_))
    }

    /// Rechecks the stored exact result or checked prefix.
    pub fn verify(&self, catalog: &IndecomposableCatalog, module: &Module) -> bool {
        match self {
            Self::Exact(result) => result.verify(catalog, module),
            Self::Unknown { progress, reason } => {
                progress.verify(catalog, module) && verify_unknown(reason, progress, catalog)
            }
            Self::Cut { progress, reason } => {
                progress.verify(catalog, module) && verify_cut(reason, progress)
            }
        }
    }
}

/// Coordinates `module` against the complete catalog.
///
/// The default work limit is [`usize::MAX`]. This limit excludes decomposition
/// work. Decomposition keeps its existing typed `Certificate::Undetermined`
/// outcome, and catalog matching counts completed isomorphism checks only.
pub fn coordinates(
    catalog: &IndecomposableCatalog,
    module: &Module,
) -> Result<CatalogCoordinateOutcome, CatalogCoordinateError> {
    coordinates_with_limits(catalog, module, CatalogCoordinateLimits::default())
}

/// Coordinates `module` against the catalog with a checked matching limit.
/// The limit covers catalog isomorphism checks. Decomposition is outside this
/// budget, and the operation has no cooperative cancellation control.
pub fn coordinates_with_limits(
    catalog: &IndecomposableCatalog,
    module: &Module,
    limits: CatalogCoordinateLimits,
) -> Result<CatalogCoordinateOutcome, CatalogCoordinateError> {
    check_ambient(catalog, module)?;
    let decomposition = decompose(module);
    let mut progress = CatalogCoordinateProgress {
        decomposition,
        multiplicities: vec![0; catalog.len()],
        matches: Vec::new(),
        work_units: 0,
    };
    if let Some((summand, attempts)) = undetermined_summand(&progress.decomposition) {
        return Ok(CatalogCoordinateOutcome::Unknown {
            progress,
            reason: CatalogCoordinateUnknown::UndeterminedSummand { summand, attempts },
        });
    }
    for summand in 0..progress.decomposition.summands().len() {
        let source = progress.decomposition.summands()[summand].clone();
        let found = match find_entry(catalog, &source, summand, &mut progress, limits)? {
            FindEntry::Found(found) => found,
            FindEntry::Unknown(reason) => {
                return Ok(CatalogCoordinateOutcome::Unknown { progress, reason });
            }
            FindEntry::Cut(reason) => {
                return Ok(CatalogCoordinateOutcome::Cut { progress, reason });
            }
        };
        progress.multiplicities[found.catalog_entry] = progress.multiplicities[found.catalog_entry]
            .checked_add(1)
            .ok_or(CatalogCoordinateError::MultiplicityOverflow {
                catalog_entry: found.catalog_entry,
            })?;
        progress.matches.push(found);
    }
    Ok(CatalogCoordinateOutcome::Exact(CatalogCoordinates {
        algebra: catalog.algebra().clone(),
        provenance: catalog.provenance(),
        progress,
    }))
}

fn check_ambient(
    catalog: &IndecomposableCatalog,
    module: &Module,
) -> Result<(), CatalogCoordinateError> {
    let catalog_field = catalog.algebra().field().modulus();
    let module_field = module.field().modulus();
    if catalog_field != module_field {
        return Err(CatalogCoordinateError::FieldMismatch {
            catalog: catalog_field,
            module: module_field,
        });
    }
    if !Arc::ptr_eq(catalog.algebra(), module.algebra()) {
        return Err(CatalogCoordinateError::DifferentAlgebra);
    }
    Ok(())
}

fn undetermined_summand(decomposition: &Decomposition) -> Option<(usize, u32)> {
    decomposition
        .certificates()
        .iter()
        .enumerate()
        .find_map(|(summand, certificate)| match certificate {
            Certificate::Indecomposable => None,
            Certificate::Undetermined { attempts } => Some((summand, *attempts)),
        })
}

enum FindEntry {
    Found(CatalogCoordinateMatch),
    Unknown(CatalogCoordinateUnknown),
    Cut(CatalogCoordinateCutReason),
}

fn find_entry(
    catalog: &IndecomposableCatalog,
    source: &Module,
    summand: usize,
    progress: &mut CatalogCoordinateProgress,
    limits: CatalogCoordinateLimits,
) -> Result<FindEntry, CatalogCoordinateError> {
    let mut unknown = None;
    for catalog_entry in 0..catalog.len() {
        if progress.work_units >= limits.max_work_units {
            return Ok(FindEntry::Cut(CatalogCoordinateCutReason::WorkLimit {
                limit: limits.max_work_units,
            }));
        }
        progress.work_units = progress
            .work_units
            .checked_add(1)
            .ok_or(CatalogCoordinateError::WorkOverflow)?;
        let outcome =
            is_isomorphic(source, catalog.entries()[catalog_entry].module()).map_err(|error| {
                CatalogCoordinateError::Isomorphism {
                    summand,
                    catalog_entry,
                    error,
                }
            })?;
        match outcome {
            IsoOutcome::Isomorphic(witness) => {
                return Ok(FindEntry::Found(CatalogCoordinateMatch {
                    summand,
                    catalog_entry,
                    witness,
                }));
            }
            IsoOutcome::NotIsomorphic(_) => {}
            IsoOutcome::Unknown { reason } => {
                if unknown.is_none() {
                    unknown = Some(CatalogCoordinateUnknown::Isomorphism {
                        summand,
                        catalog_entry,
                        reason,
                    });
                }
            }
        }
    }
    if let Some(reason) = unknown {
        return Ok(FindEntry::Unknown(reason));
    }
    Err(CatalogCoordinateError::CatalogInvariantViolation {
        summand,
        dim_vector: source.dim_vector().to_vec(),
    })
}

fn verify_progress(
    progress: &CatalogCoordinateProgress,
    catalog: &IndecomposableCatalog,
    module: &Module,
) -> bool {
    if !progress_shape_is_valid(progress, catalog, module) {
        return false;
    }
    if progress.work_units < progress.matches.len()
        || !progress
            .matches
            .iter()
            .enumerate()
            .all(|(summand, found)| found.summand == summand)
        || !progress.matches.iter().all(|found| {
            matches!(
                progress.decomposition.certificates().get(found.summand),
                Some(Certificate::Indecomposable)
            )
        })
    {
        return false;
    }
    let mut seen = vec![false; progress.decomposition.summands().len()];
    let mut counts = vec![0usize; catalog.len()];
    progress
        .matches
        .iter()
        .all(|found| verify_match(found, progress, catalog, &mut seen, &mut counts))
        && counts == progress.multiplicities
}

fn progress_shape_is_valid(
    progress: &CatalogCoordinateProgress,
    catalog: &IndecomposableCatalog,
    module: &Module,
) -> bool {
    Arc::ptr_eq(module.algebra(), catalog.algebra())
        && progress.decomposition.split().total().ptr_eq(module)
        && progress.decomposition.split().verify()
        && progress.decomposition.certificates().len() == progress.decomposition.summands().len()
        && progress.decomposition.endos().len() == progress.decomposition.summands().len()
        && progress.multiplicities.len() == catalog.len()
        && progress.matches.len() <= progress.decomposition.summands().len()
}

fn verify_unknown(
    reason: &CatalogCoordinateUnknown,
    progress: &CatalogCoordinateProgress,
    catalog: &IndecomposableCatalog,
) -> bool {
    match reason {
        CatalogCoordinateUnknown::UndeterminedSummand { summand, attempts } => verify_undetermined(
            progress.decomposition.certificates(),
            progress.work_units,
            progress.matches.is_empty(),
            *summand,
            *attempts,
        ),
        CatalogCoordinateUnknown::Isomorphism {
            summand,
            catalog_entry,
            reason,
        } => verify_isomorphism_unknown(progress, catalog, *summand, *catalog_entry, reason),
    }
}

fn verify_undetermined(
    certificates: &[Certificate],
    work_units: usize,
    matches_empty: bool,
    summand: usize,
    attempts: u32,
) -> bool {
    work_units == 0
        && matches_empty
        && certificates.get(..summand).is_some_and(|prefix| {
            prefix
                .iter()
                .all(|certificate| matches!(certificate, Certificate::Indecomposable))
        })
        && matches!(
            certificates.get(summand),
            Some(Certificate::Undetermined { attempts: found }) if *found == attempts
        )
}

fn verify_isomorphism_unknown(
    progress: &CatalogCoordinateProgress,
    catalog: &IndecomposableCatalog,
    summand: usize,
    catalog_entry: usize,
    reason: &str,
) -> bool {
    summand == progress.matches.len()
        && catalog_entry < catalog.len()
        && !reason.is_empty()
        && matches!(
            progress.decomposition.certificates().get(summand),
            Some(Certificate::Indecomposable)
        )
        && progress
            .decomposition
            .certificates()
            .iter()
            .all(|certificate| matches!(certificate, Certificate::Indecomposable))
}

fn verify_cut(reason: &CatalogCoordinateCutReason, progress: &CatalogCoordinateProgress) -> bool {
    match reason {
        CatalogCoordinateCutReason::WorkLimit { limit } => {
            progress.work_units == *limit
                && progress.matches.len() < progress.decomposition.summands().len()
                && progress
                    .decomposition
                    .certificates()
                    .iter()
                    .all(|certificate| matches!(certificate, Certificate::Indecomposable))
        }
    }
}

fn verify_match(
    found: &CatalogCoordinateMatch,
    progress: &CatalogCoordinateProgress,
    catalog: &IndecomposableCatalog,
    seen: &mut [bool],
    counts: &mut [usize],
) -> bool {
    let Some(seen_slot) = seen.get_mut(found.summand) else {
        return false;
    };
    let Some(count) = counts.get_mut(found.catalog_entry) else {
        return false;
    };
    if *seen_slot {
        return false;
    }
    let source = &progress.decomposition.summands()[found.summand];
    let target = catalog.entries()[found.catalog_entry].module();
    if !found.witness.source().ptr_eq(source)
        || !found.witness.target().ptr_eq(target)
        || !found.witness.is_isomorphism()
    {
        return false;
    }
    let Some(next) = count.checked_add(1) else {
        return false;
    };
    *seen_slot = true;
    *count = next;
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{cyclic_nakayama, linear_an};
    use crate::atlas::{CatalogAtlas, CatalogAtlasLimits};
    use crate::field::PrimeField;
    use crate::module::Module;
    use std::sync::Arc;

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn materialize(catalog: Arc<IndecomposableCatalog>, chosen: &[usize]) -> Module {
        let atlas = CatalogAtlas::compute(catalog.clone(), 0, CatalogAtlasLimits::default())
            .expect("degree-zero atlas materializes the catalog");
        let mut multiplicities = vec![0; catalog.len()];
        for &index in chosen {
            multiplicities[index] += 1;
        }
        atlas
            .materialize(&multiplicities)
            .expect("the selected entries fit the materialization limit")
    }

    #[test]
    fn nakayama_materialization_roundtrips_with_multiplicity() {
        let algebra = cyclic_nakayama(&[3, 3, 3], f5()).unwrap();
        let catalog = Arc::new(IndecomposableCatalog::nakayama(&algebra).unwrap());
        let module = materialize(catalog.clone(), &[2, 5, 5, 8]);
        let outcome = coordinates(&catalog, &module).unwrap();
        let result = outcome.exact().expect("the finite Nakayama match is exact");
        assert_eq!(result.multiplicities()[2], 1);
        assert_eq!(result.multiplicities()[5], 2);
        assert_eq!(result.multiplicities()[8], 1);
        assert_eq!(result.matches().len(), 4);
        assert!(result.verify(&catalog, &module));
    }

    #[test]
    fn cyclic_nakayama_equal_dimensions_still_match_by_isomorphism() {
        let algebra = cyclic_nakayama(&[3, 3, 3], f5()).unwrap();
        let catalog = Arc::new(IndecomposableCatalog::nakayama(&algebra).unwrap());
        assert_eq!(catalog.entries()[2].module().dim_vector(), &[1, 1, 1]);
        assert_eq!(catalog.entries()[5].module().dim_vector(), &[1, 1, 1]);
        assert_ne!(
            crate::radical::top(catalog.entries()[2].module())
                .0
                .dim_vector(),
            crate::radical::top(catalog.entries()[5].module())
                .0
                .dim_vector()
        );
        let outcome =
            crate::iso::is_isomorphic(catalog.entries()[2].module(), catalog.entries()[5].module())
                .unwrap();
        assert!(matches!(outcome, IsoOutcome::NotIsomorphic(_)));
    }

    #[test]
    fn dynkin_materialization_roundtrips() {
        let algebra = linear_an(3, f5());
        let catalog = Arc::new(IndecomposableCatalog::dynkin(&algebra).unwrap());
        let module = materialize(catalog.clone(), &[0, 3, 3, 5]);
        let outcome = coordinates(&catalog, &module).unwrap();
        let result = outcome.exact().expect("the finite Dynkin match is exact");
        assert_eq!(result.multiplicities()[0], 1);
        assert_eq!(result.multiplicities()[3], 2);
        assert_eq!(result.multiplicities()[5], 1);
        assert!(result.verify(&catalog, &module));
    }

    #[test]
    fn zero_module_has_the_zero_coordinate_vector() {
        let algebra = linear_an(2, f5());
        let catalog = Arc::new(IndecomposableCatalog::dynkin(&algebra).unwrap());
        let module = materialize(catalog.clone(), &[]);
        let outcome = coordinates(&catalog, &module).unwrap();
        let result = outcome.exact().expect("zero decomposition is exact");
        assert_eq!(result.multiplicities(), vec![0; catalog.len()]);
        assert!(result.decomposition().summands().is_empty());
        assert!(result.verify(&catalog, &module));
    }

    #[test]
    fn field_and_algebra_identity_are_checked() {
        let f5_algebra = linear_an(2, f5());
        let catalog = Arc::new(IndecomposableCatalog::dynkin(&f5_algebra).unwrap());
        let f2_algebra = linear_an(2, PrimeField::new(2).unwrap());
        assert_eq!(
            coordinates(&catalog, &Module::zero(&f2_algebra)).unwrap_err(),
            CatalogCoordinateError::FieldMismatch {
                catalog: 5,
                module: 2
            }
        );
        let same_field = linear_an(2, f5());
        assert_eq!(
            coordinates(&catalog, &Module::zero(&same_field)).unwrap_err(),
            CatalogCoordinateError::DifferentAlgebra
        );
    }

    #[test]
    fn matching_limit_is_a_typed_cut() {
        let algebra = linear_an(2, f5());
        let catalog = Arc::new(IndecomposableCatalog::dynkin(&algebra).unwrap());
        let module = materialize(catalog.clone(), &[0]);
        let outcome = coordinates_with_limits(
            &catalog,
            &module,
            CatalogCoordinateLimits { max_work_units: 0 },
        )
        .unwrap();
        assert!(matches!(
            outcome,
            CatalogCoordinateOutcome::Cut {
                reason: CatalogCoordinateCutReason::WorkLimit { limit: 0 },
                ..
            }
        ));
        assert!(outcome.verify(&catalog, &module));
    }

    #[test]
    fn undetermined_verification_keeps_the_first_unknown_index() {
        let certificates = [
            Certificate::Indecomposable,
            Certificate::Undetermined { attempts: 3 },
        ];
        assert!(verify_undetermined(&certificates, 0, true, 1, 3));
    }

    #[test]
    fn prefix_verification_rejects_a_missing_or_reordered_summand() {
        let algebra = linear_an(2, f5());
        let catalog = Arc::new(IndecomposableCatalog::dynkin(&algebra).unwrap());
        let module = materialize(catalog.clone(), &[0, 1]);
        let exact = coordinates(&catalog, &module).unwrap();
        assert!(exact.verify(&catalog, &module));
        let CatalogCoordinateOutcome::Exact(result) = exact else {
            panic!("the finite match is exact");
        };
        assert_eq!(result.matches().len(), 2);
        let mut missing = result.clone();
        missing.progress.matches.remove(0);
        assert!(!missing.progress.verify(&catalog, &module));

        let mut reordered = result.clone();
        reordered.progress.matches.swap(0, 1);
        assert!(!reordered.progress.verify(&catalog, &module));
    }
}
