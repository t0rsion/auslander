//! Higher Ext-orthogonality over a complete indecomposable catalog.
//!
//! The degree bound is inclusive: `max_degree = d` checks `Ext^i` for
//! `1 <= i <= d`. The catalog is exhaustive, so vanishing against every
//! catalog entry is vanishing against every finite-dimensional module. Ext is
//! additive over finite direct sums. A plain module list never enters this
//! API, so a catalog-relative result cannot be mistaken for a global one.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::arquiver::{CatalogProvenance, IndecomposableCatalog};
use crate::ext::ext_table_from_resolution;
use crate::resolution::{ProjectiveResolution, resolve};

/// Work limits for one higher-orthogonality table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HigherOrthogonalityLimits {
    /// Maximum number of distinct ordered Ext pairs.
    pub max_pairs: usize,
    /// Maximum number of stored positive-degree Ext dimensions.
    pub max_ext_cells: usize,
}

impl Default for HigherOrthogonalityLimits {
    fn default() -> Self {
        Self {
            max_pairs: 1_000_000,
            max_ext_cells: 10_000_000,
        }
    }
}

/// Rejected higher-orthogonality input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HigherOrthogonalityError {
    /// At least one positive Ext degree is required.
    ZeroDegree,
    /// `max_degree + 1` is not representable.
    DegreeOverflow { degree: usize },
    /// A selected index is outside the catalog.
    IndexOutOfRange {
        position: usize,
        index: usize,
        catalog: usize,
    },
    /// One catalog index occurs twice.
    DuplicateIndex {
        index: usize,
        first: usize,
        second: usize,
    },
    /// The distinct pair count exceeds the limit.
    PairLimit { requested: usize, limit: usize },
    /// The Ext table would exceed the cell limit.
    ExtCellLimit { requested: usize, limit: usize },
}

display_error! { error HigherOrthogonalityError {
    Self::ZeroDegree => "higher orthogonality needs at least Ext degree 1";
    Self::DegreeOverflow { degree } => "Ext degree {degree} has no representable successor";
    Self::IndexOutOfRange { position, index, catalog } => "selected position {position} has catalog index {index}, but the catalog has {catalog} entries";
    Self::DuplicateIndex { index, first, second } => "catalog index {index} occurs at selected positions {first} and {second}";
    Self::PairLimit { requested, limit } => "orthogonality needs {requested} Ext pairs, above the limit {limit}";
    Self::ExtCellLimit { requested, limit } => "orthogonality needs {requested} Ext cells, above the limit {limit}";
} }

/// Positive-degree Ext dimensions for one ordered catalog pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HigherExtPair {
    source: usize,
    target: usize,
    dimensions: Vec<usize>,
}

impl HigherExtPair {
    accessor_methods! {
        /// The source catalog index.
        pub source() -> usize = |this| this.source;
        /// The target catalog index.
        pub target() -> usize = |this| this.target;
        /// Dimensions in degrees one through the inclusive bound.
        pub dimensions() -> &[usize] = |this| &this.dimensions;
        /// Whether every stored Ext group vanishes.
        pub vanishes() -> bool = |this| this.dimensions.iter().all(|&dimension| dimension == 0);
    }
}

/// Exact operation counts for a higher-orthogonality table.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HigherOrthogonalityWork {
    /// Distinct source resolutions.
    pub resolutions: usize,
    /// Ext tables computed from those resolutions.
    pub ext_tables: usize,
}

/// A global higher-orthogonality result over an exhaustive catalog.
#[derive(Clone)]
pub struct HigherOrthogonality {
    algebra: Arc<Algebra>,
    provenance: CatalogProvenance,
    catalog_len: usize,
    chosen: Vec<usize>,
    max_degree: usize,
    limits: HigherOrthogonalityLimits,
    pairs: Vec<HigherExtPair>,
    left: Vec<usize>,
    right: Vec<usize>,
    rigid: bool,
    work: HigherOrthogonalityWork,
}

fn validate_chosen(
    chosen: &[usize],
    catalog_len: usize,
) -> Result<Vec<usize>, HigherOrthogonalityError> {
    let mut seen = BTreeMap::new();
    for (position, &index) in chosen.iter().enumerate() {
        if index >= catalog_len {
            return Err(HigherOrthogonalityError::IndexOutOfRange {
                position,
                index,
                catalog: catalog_len,
            });
        }
        if let Some(&first) = seen.get(&index) {
            return Err(HigherOrthogonalityError::DuplicateIndex {
                index,
                first,
                second: position,
            });
        }
        seen.insert(index, position);
    }
    let mut sorted = chosen.to_vec();
    sorted.sort_unstable();
    Ok(sorted)
}

fn selected_pairs(catalog_len: usize, chosen: &[usize]) -> Vec<(usize, usize)> {
    let mut pairs = BTreeSet::new();
    for index in 0..catalog_len {
        for &member in chosen {
            pairs.insert((index, member));
            pairs.insert((member, index));
        }
    }
    pairs.into_iter().collect()
}

fn preflight(
    pair_count: usize,
    max_degree: usize,
    limits: HigherOrthogonalityLimits,
) -> Result<usize, HigherOrthogonalityError> {
    if max_degree == 0 {
        return Err(HigherOrthogonalityError::ZeroDegree);
    }
    let steps = max_degree
        .checked_add(1)
        .ok_or(HigherOrthogonalityError::DegreeOverflow { degree: max_degree })?;
    if pair_count > limits.max_pairs {
        return Err(HigherOrthogonalityError::PairLimit {
            requested: pair_count,
            limit: limits.max_pairs,
        });
    }
    let cells =
        pair_count
            .checked_mul(max_degree)
            .ok_or(HigherOrthogonalityError::ExtCellLimit {
                requested: usize::MAX,
                limit: limits.max_ext_cells,
            })?;
    if cells > limits.max_ext_cells {
        return Err(HigherOrthogonalityError::ExtCellLimit {
            requested: cells,
            limit: limits.max_ext_cells,
        });
    }
    Ok(steps)
}

fn build_resolutions(
    catalog: &IndecomposableCatalog,
    pairs: &[(usize, usize)],
    steps: usize,
) -> BTreeMap<usize, ProjectiveResolution> {
    pairs
        .iter()
        .map(|pair| pair.0)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|source| {
            let module = catalog.entries()[source].module();
            (source, resolve(module, steps))
        })
        .collect()
}

fn compute_pairs(
    catalog: &IndecomposableCatalog,
    selected: &[(usize, usize)],
    resolutions: &BTreeMap<usize, ProjectiveResolution>,
    max_degree: usize,
) -> Vec<HigherExtPair> {
    selected
        .iter()
        .map(|&(source, target)| {
            let target_module = catalog.entries()[target].module();
            let table = ext_table_from_resolution(&resolutions[&source], target_module, max_degree);
            HigherExtPair {
                source,
                target,
                dimensions: table[1..].to_vec(),
            }
        })
        .collect()
}

fn vanishing_map(pairs: &[HigherExtPair]) -> BTreeMap<(usize, usize), bool> {
    pairs
        .iter()
        .map(|pair| ((pair.source, pair.target), pair.vanishes()))
        .collect()
}

fn orthogonals(
    catalog_len: usize,
    chosen: &[usize],
    vanishing: &BTreeMap<(usize, usize), bool>,
) -> (Vec<usize>, Vec<usize>) {
    let left = (0..catalog_len)
        .filter(|&candidate| chosen.iter().all(|&member| vanishing[&(candidate, member)]))
        .collect();
    let right = (0..catalog_len)
        .filter(|&candidate| chosen.iter().all(|&member| vanishing[&(member, candidate)]))
        .collect();
    (left, right)
}

impl HigherOrthogonality {
    /// Computes both Ext-orthogonals of selected indecomposables.
    ///
    /// The returned index lists are global for finite-dimensional modules,
    /// because `catalog` is exhaustive and Ext is additive over finite direct
    /// sums. The selected list may be empty. Its orthogonals are then the whole
    /// catalog.
    pub fn compute(
        catalog: &IndecomposableCatalog,
        chosen: &[usize],
        max_degree: usize,
        limits: HigherOrthogonalityLimits,
    ) -> Result<Self, HigherOrthogonalityError> {
        let chosen = validate_chosen(chosen, catalog.len())?;
        let selected = selected_pairs(catalog.len(), &chosen);
        let steps = preflight(selected.len(), max_degree, limits)?;
        let resolutions = build_resolutions(catalog, &selected, steps);
        let pairs = compute_pairs(catalog, &selected, &resolutions, max_degree);
        let vanishing = vanishing_map(&pairs);
        let (left, right) = orthogonals(catalog.len(), &chosen, &vanishing);
        let rigid = chosen
            .iter()
            .all(|&source| chosen.iter().all(|&target| vanishing[&(source, target)]));
        let work = HigherOrthogonalityWork {
            resolutions: resolutions.len(),
            ext_tables: pairs.len(),
        };
        Ok(Self {
            algebra: catalog.algebra().clone(),
            provenance: catalog.provenance(),
            catalog_len: catalog.len(),
            chosen,
            max_degree,
            limits,
            pairs,
            left,
            right,
            rigid,
            work,
        })
    }

    accessor_methods! {
        /// The theorem that makes the catalog exhaustive.
        pub provenance() -> CatalogProvenance = |this| this.provenance;
        /// The selected catalog indices, sorted in increasing order.
        pub chosen() -> &[usize] = |this| &this.chosen;
        /// The inclusive positive Ext degree bound.
        pub max_degree() -> usize = |this| this.max_degree;
        /// Stored Ext rows in source-major order.
        pub pairs() -> &[HigherExtPair] = |this| &this.pairs;
        /// Indices `X` with `Ext^i(X, C) = 0` for every selected `C` and `1 <= i <= d`.
        pub left() -> &[usize] = |this| &this.left;
        /// Indices `X` with `Ext^i(C, X) = 0` for every selected `C` and `1 <= i <= d`.
        pub right() -> &[usize] = |this| &this.right;
        /// Whether all positive-degree Ext groups between selected entries vanish.
        pub is_rigid() -> bool = |this| this.rigid;
        /// Exact operation counts.
        pub work() -> HigherOrthogonalityWork = |this| this.work;
        /// Whether `add(chosen)` equals both global orthogonals through the bound.
        pub is_two_sided_maximal() -> bool = |this| this.left == this.chosen && this.right == this.chosen;
    }

    /// Recomputes the table over the same catalog value.
    pub fn verify(&self, catalog: &IndecomposableCatalog) -> bool {
        if !Arc::ptr_eq(&self.algebra, catalog.algebra()) || self.catalog_len != catalog.len() {
            return false;
        }
        let Ok(rebuilt) = Self::compute(catalog, &self.chosen, self.max_degree, self.limits) else {
            return false;
        };
        self.provenance == rebuilt.provenance
            && self.pairs == rebuilt.pairs
            && self.left == rebuilt.left
            && self.right == rebuilt.right
            && self.rigid == rebuilt.rigid
            && self.work == rebuilt.work
    }
}

debug_fields! { HigherOrthogonality |this| {
    "provenance" => this.provenance;
    "chosen" => this.chosen;
    "max_degree" => this.max_degree;
    "left" => this.left;
    "right" => this.right;
    "rigid" => this.rigid;
    "work" => this.work;
} }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::linear_an;
    use crate::field::PrimeField;

    fn limits() -> HigherOrthogonalityLimits {
        HigherOrthogonalityLimits {
            max_pairs: 100,
            max_ext_cells: 200,
        }
    }

    #[test]
    fn the_single_a1_entry_is_globally_maximal_in_every_positive_degree() {
        for prime in [2, 5] {
            let algebra = linear_an(1, PrimeField::new(prime).unwrap());
            let catalog = IndecomposableCatalog::dynkin(&algebra).unwrap();
            let result = HigherOrthogonality::compute(&catalog, &[0], 3, limits()).unwrap();
            assert_eq!(result.left(), &[0]);
            assert_eq!(result.right(), &[0]);
            assert!(result.is_rigid());
            assert!(result.is_two_sided_maximal());
            assert!(result.verify(&catalog));
        }
    }

    #[test]
    fn empty_selection_has_the_whole_catalog_as_each_orthogonal() {
        let algebra = linear_an(2, PrimeField::new(5).unwrap());
        let catalog = IndecomposableCatalog::dynkin(&algebra).unwrap();
        let result = HigherOrthogonality::compute(&catalog, &[], 2, limits()).unwrap();
        assert_eq!(result.left(), &[0, 1, 2]);
        assert_eq!(result.right(), &[0, 1, 2]);
        assert!(result.is_rigid());
        assert!(!result.is_two_sided_maximal());
        assert_eq!(result.work(), HigherOrthogonalityWork::default());
    }

    #[test]
    fn pair_rows_are_source_major_and_match_the_stored_bound() {
        let algebra = linear_an(2, PrimeField::new(5).unwrap());
        let catalog = IndecomposableCatalog::dynkin(&algebra).unwrap();
        let result = HigherOrthogonality::compute(&catalog, &[1], 2, limits()).unwrap();
        let indices: Vec<(usize, usize)> = result
            .pairs()
            .iter()
            .map(|pair| (pair.source(), pair.target()))
            .collect();
        let mut sorted = indices.clone();
        sorted.sort_unstable();
        assert_eq!(indices, sorted);
        assert!(
            result
                .pairs()
                .iter()
                .all(|pair| pair.dimensions().len() == 2)
        );
        assert!(result.verify(&catalog));
    }

    #[test]
    fn bad_indices_degrees_and_limits_are_rejected_before_resolution() {
        let algebra = linear_an(1, PrimeField::new(5).unwrap());
        let catalog = IndecomposableCatalog::dynkin(&algebra).unwrap();
        assert!(matches!(
            HigherOrthogonality::compute(&catalog, &[1], 1, limits()),
            Err(HigherOrthogonalityError::IndexOutOfRange { .. })
        ));
        assert!(matches!(
            HigherOrthogonality::compute(&catalog, &[0, 0], 1, limits()),
            Err(HigherOrthogonalityError::DuplicateIndex { .. })
        ));
        assert!(matches!(
            HigherOrthogonality::compute(&catalog, &[0], 0, limits()),
            Err(HigherOrthogonalityError::ZeroDegree)
        ));
        assert!(matches!(
            HigherOrthogonality::compute(
                &catalog,
                &[0],
                2,
                HigherOrthogonalityLimits {
                    max_pairs: 1,
                    max_ext_cells: 1,
                },
            ),
            Err(HigherOrthogonalityError::ExtCellLimit { .. })
        ));
    }
}
