//! Shared work for selected Hom, stable-Hom, and Ext dimension tables.
//!
//! A batch resolves each distinct source once and builds each distinct target's
//! projective cover once. Pair selection is explicit, so a self-pair census does
//! not allocate an all-pairs table. Limits reject the request before computation.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::almost_split::{AlmostSplitError, stable_hom};
use crate::ext::ext_table_from_resolution;
use crate::hom::{HomError, Morphism, hom};
use crate::homspace::{HomQuotient, HomSpace};
use crate::module::Module;
use crate::resolution::{ProjectiveResolution, projective_cover, resolve};

/// Preflight limits for a homological batch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HomologicalBatchLimits {
    /// Maximum number of selected ordered pairs.
    pub max_pairs: usize,
    /// Maximum number of stored Ext dimension cells.
    pub max_ext_cells: usize,
}

impl Default for HomologicalBatchLimits {
    fn default() -> Self {
        Self {
            max_pairs: 1_000_000,
            max_ext_cells: 10_000_000,
        }
    }
}

/// Rejected homological batch input or a failed primitive computation.
#[derive(Clone, Debug)]
pub enum HomologicalBatchError {
    /// One module does not share the first module's algebra object.
    DifferentAlgebra { module: usize },
    /// One selected endpoint is not a module index.
    PairIndex {
        pair: usize,
        endpoint: &'static str,
        index: usize,
        modules: usize,
    },
    /// A selected-pair result index is out of range.
    ResultIndex { index: usize, pairs: usize },
    /// One ordered pair occurs twice.
    DuplicatePair {
        pair: (usize, usize),
        first: usize,
        second: usize,
    },
    /// `max_degree + 1` is not representable.
    DegreeOverflow { degree: usize },
    /// The selected pair count exceeds the preflight limit.
    PairLimit { requested: usize, limit: usize },
    /// The stored Ext table would exceed the preflight limit.
    ExtCellLimit { requested: usize, limit: usize },
    /// An ordinary Hom space failed.
    Hom {
        pair: (usize, usize),
        error: HomError,
    },
    /// A stable-Hom quotient failed.
    StableHom {
        pair: (usize, usize),
        error: AlmostSplitError,
    },
}

display_error! { error HomologicalBatchError {
    Self::DifferentAlgebra { module } => "module {module} does not share the batch algebra";
    Self::PairIndex { pair, endpoint, index, modules } => "pair {pair} has {endpoint} index {index}, but the batch has {modules} modules";
    Self::ResultIndex { index, pairs } => "result index {index} is out of range for {pairs} selected pairs";
    Self::DuplicatePair { pair, first, second } => "pair {:?} occurs at positions {first} and {second}", pair;
    Self::DegreeOverflow { degree } => "Ext degree {degree} has no representable successor";
    Self::PairLimit { requested, limit } => "batch requests {requested} pairs, above the limit {limit}";
    Self::ExtCellLimit { requested, limit } => "batch requests {requested} Ext cells, above the limit {limit}";
    Self::Hom { pair, error } => "Hom for pair {:?} failed: {error}", pair;
    Self::StableHom { pair, error } => "stable Hom for pair {:?} failed: {error}", pair;
} }

/// Exact dimensions for one selected ordered pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HomologicalPair {
    source: usize,
    target: usize,
    hom_dim: usize,
    stable_hom_dim: usize,
    ext_dimensions: Vec<usize>,
}

impl HomologicalPair {
    accessor_methods! {
        /// The source module index.
        pub source() -> usize = |this| this.source;
        /// The target module index.
        pub target() -> usize = |this| this.target;
        /// `dim_k Hom(source, target)`.
        pub hom_dim() -> usize = |this| this.hom_dim;
        /// `dim_k stable Hom(source, target)`.
        pub stable_hom_dim() -> usize = |this| this.stable_hom_dim;
        /// Ext dimensions in degrees zero through the batch bound.
        pub ext_dimensions() -> &[usize] = |this| &this.ext_dimensions;
    }
}

/// Exact operation counts for a homological batch.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HomologicalBatchWork {
    /// Distinct source resolutions.
    pub resolutions: usize,
    /// Distinct projective covers of targets.
    pub target_covers: usize,
    /// Ordinary Hom spaces for selected pairs.
    pub hom_spaces: usize,
    /// Hom spaces into target covers.
    pub projective_factor_spaces: usize,
    /// Ext tables computed from stored source resolutions.
    pub ext_tables: usize,
}

/// Selected Hom, stable-Hom, and Ext dimensions with shared source work.
#[derive(Clone)]
pub struct HomologicalBatch {
    modules: Vec<Module>,
    max_degree: usize,
    limits: HomologicalBatchLimits,
    selected_pairs: Vec<(usize, usize)>,
    resolutions: BTreeMap<usize, ProjectiveResolution>,
    pairs: Vec<HomologicalPair>,
    work: HomologicalBatchWork,
}

fn stable_hom_with_cover(
    space: &HomSpace,
    cover: &Module,
    projection: &Morphism,
) -> Result<HomQuotient, AlmostSplitError> {
    let through = hom(space.source(), cover).map_err(AlmostSplitError::Hom)?;
    let composites: Vec<Morphism> = through
        .iter()
        .map(|map| map.then(projection))
        .collect::<Result<_, _>>()
        .map_err(AlmostSplitError::Hom)?;
    let trivial = space
        .subspace(&composites)
        .map_err(AlmostSplitError::Space)?;
    space
        .full_subspace()
        .quotient_by(&trivial)
        .map_err(AlmostSplitError::Space)
}

fn validate_modules(modules: &[Module]) -> Result<(), HomologicalBatchError> {
    let Some(first) = modules.first() else {
        return Ok(());
    };
    for (index, module) in modules.iter().enumerate().skip(1) {
        if !Arc::ptr_eq(first.algebra(), module.algebra()) {
            return Err(HomologicalBatchError::DifferentAlgebra { module: index });
        }
    }
    Ok(())
}

fn validate_pairs(pairs: &[(usize, usize)], modules: usize) -> Result<(), HomologicalBatchError> {
    let mut seen = BTreeMap::new();
    for (position, &(source, target)) in pairs.iter().enumerate() {
        for (endpoint, index) in [("source", source), ("target", target)] {
            if index >= modules {
                return Err(HomologicalBatchError::PairIndex {
                    pair: position,
                    endpoint,
                    index,
                    modules,
                });
            }
        }
        if let Some(&first) = seen.get(&(source, target)) {
            return Err(HomologicalBatchError::DuplicatePair {
                pair: (source, target),
                first,
                second: position,
            });
        }
        seen.insert((source, target), position);
    }
    Ok(())
}

fn resolution_steps(
    pair_count: usize,
    max_degree: usize,
    limits: HomologicalBatchLimits,
) -> Result<usize, HomologicalBatchError> {
    let steps = max_degree
        .checked_add(1)
        .ok_or(HomologicalBatchError::DegreeOverflow { degree: max_degree })?;
    if pair_count > limits.max_pairs {
        return Err(HomologicalBatchError::PairLimit {
            requested: pair_count,
            limit: limits.max_pairs,
        });
    }
    let ext_cells = pair_count
        .checked_mul(steps)
        .ok_or(HomologicalBatchError::ExtCellLimit {
            requested: usize::MAX,
            limit: limits.max_ext_cells,
        })?;
    if ext_cells > limits.max_ext_cells {
        return Err(HomologicalBatchError::ExtCellLimit {
            requested: ext_cells,
            limit: limits.max_ext_cells,
        });
    }
    Ok(steps)
}

fn compute_pair(
    modules: &[Module],
    resolutions: &BTreeMap<usize, ProjectiveResolution>,
    target_covers: &BTreeMap<usize, (Module, Morphism)>,
    pair: (usize, usize),
    max_degree: usize,
) -> Result<HomologicalPair, HomologicalBatchError> {
    let (source, target) = pair;
    let space = HomSpace::new(&modules[source], &modules[target])
        .map_err(|error| HomologicalBatchError::Hom { pair, error })?;
    let (cover, projection) = &target_covers[&target];
    let stable = stable_hom_with_cover(&space, cover, projection)
        .map_err(|error| HomologicalBatchError::StableHom { pair, error })?;
    let dimensions = ext_table_from_resolution(&resolutions[&source], &modules[target], max_degree);
    debug_assert_eq!(space.dim(), dimensions[0]);
    Ok(HomologicalPair {
        source,
        target,
        hom_dim: space.dim(),
        stable_hom_dim: stable.dim(),
        ext_dimensions: dimensions,
    })
}

impl HomologicalBatch {
    /// Computes the selected ordered pairs with shared source resolutions.
    pub fn compute(
        modules: Vec<Module>,
        pairs: Vec<(usize, usize)>,
        max_degree: usize,
        limits: HomologicalBatchLimits,
    ) -> Result<Self, HomologicalBatchError> {
        validate_modules(&modules)?;
        validate_pairs(&pairs, modules.len())?;
        let resolution_steps = resolution_steps(pairs.len(), max_degree, limits)?;

        let source_indices: BTreeSet<usize> = pairs.iter().map(|pair| pair.0).collect();
        let target_indices: BTreeSet<usize> = pairs.iter().map(|pair| pair.1).collect();
        let resolutions: BTreeMap<usize, ProjectiveResolution> = source_indices
            .iter()
            .map(|&index| (index, resolve(&modules[index], resolution_steps)))
            .collect();
        let target_covers: BTreeMap<usize, (Module, Morphism)> = target_indices
            .iter()
            .map(|&index| (index, projective_cover(&modules[index])))
            .collect();

        let results = pairs
            .iter()
            .copied()
            .map(|pair| compute_pair(&modules, &resolutions, &target_covers, pair, max_degree))
            .collect::<Result<_, _>>()?;
        let work = HomologicalBatchWork {
            resolutions: source_indices.len(),
            target_covers: target_indices.len(),
            hom_spaces: pairs.len(),
            projective_factor_spaces: pairs.len(),
            ext_tables: pairs.len(),
        };
        Ok(Self {
            modules,
            max_degree,
            limits,
            selected_pairs: pairs,
            resolutions,
            pairs: results,
            work,
        })
    }

    /// Computes self-pairs `(i, i)` for every module.
    pub fn self_pairs(
        modules: Vec<Module>,
        max_degree: usize,
        limits: HomologicalBatchLimits,
    ) -> Result<Self, HomologicalBatchError> {
        let pairs = (0..modules.len()).map(|index| (index, index)).collect();
        Self::compute(modules, pairs, max_degree, limits)
    }

    /// Computes every ordered pair in source-major order.
    pub fn all_pairs(
        modules: Vec<Module>,
        max_degree: usize,
        limits: HomologicalBatchLimits,
    ) -> Result<Self, HomologicalBatchError> {
        let count = modules.len();
        let pair_count = count
            .checked_mul(count)
            .ok_or(HomologicalBatchError::PairLimit {
                requested: usize::MAX,
                limit: limits.max_pairs,
            })?;
        if pair_count > limits.max_pairs {
            return Err(HomologicalBatchError::PairLimit {
                requested: pair_count,
                limit: limits.max_pairs,
            });
        }
        let pairs = (0..count)
            .flat_map(|source| (0..count).map(move |target| (source, target)))
            .collect();
        Self::compute(modules, pairs, max_degree, limits)
    }

    accessor_methods! {
        /// The modules indexed by the selected pairs.
        pub modules() -> &[Module] = |this| &this.modules;
        /// The largest stored Ext degree.
        pub max_degree() -> usize = |this| this.max_degree;
        /// The selected pairs in result order.
        pub selected_pairs() -> &[(usize, usize)] = |this| &this.selected_pairs;
        /// Exact results in selected-pair order.
        pub pairs() -> &[HomologicalPair] = |this| &this.pairs;
        /// Exact shared-work counts.
        pub work() -> HomologicalBatchWork = |this| this.work;
    }

    /// The stored resolution for a selected source index.
    pub fn resolution(&self, source: usize) -> Option<&ProjectiveResolution> {
        self.resolutions.get(&source)
    }

    /// Recomputes a full stable-Hom value for one selected pair.
    pub fn stable_hom(&self, pair: usize) -> Result<HomQuotient, HomologicalBatchError> {
        let &(source, target) =
            self.selected_pairs
                .get(pair)
                .ok_or(HomologicalBatchError::ResultIndex {
                    index: pair,
                    pairs: self.selected_pairs.len(),
                })?;
        stable_hom(&self.modules[source], &self.modules[target]).map_err(|error| {
            HomologicalBatchError::StableHom {
                pair: (source, target),
                error,
            }
        })
    }

    /// Recomputes every shared result and exact work count.
    pub fn verify(&self) -> bool {
        let Ok(rebuilt) = Self::compute(
            self.modules.clone(),
            self.selected_pairs.clone(),
            self.max_degree,
            self.limits,
        ) else {
            return false;
        };
        self.pairs == rebuilt.pairs
            && self.work == rebuilt.work
            && self.resolutions.len() == rebuilt.resolutions.len()
            && self.resolutions.iter().all(|(source, resolution)| {
                rebuilt
                    .resolutions
                    .get(source)
                    .is_some_and(|other| resolution.agrees_with(other))
            })
    }
}

debug_fields! { HomologicalBatch |this| {
    "modules" => this.modules.len();
    "pairs" => this.pairs.len();
    "max_degree" => this.max_degree;
    "work" => this.work;
} }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{dual_numbers, linear_an};
    use crate::ext::ext_table;
    use crate::field::PrimeField;

    fn limits() -> HomologicalBatchLimits {
        HomologicalBatchLimits {
            max_pairs: 100,
            max_ext_cells: 500,
        }
    }

    #[test]
    fn self_pair_batch_matches_scalar_calls_over_two_fields() {
        for prime in [2, 5] {
            let algebra = dual_numbers(PrimeField::new(prime).unwrap());
            let modules = vec![Module::simple(&algebra, 0), Module::projective(&algebra, 0)];
            let batch = HomologicalBatch::self_pairs(modules.clone(), 3, limits()).unwrap();
            assert!(batch.verify());
            for (index, result) in batch.pairs().iter().enumerate() {
                assert_eq!(result.source(), index);
                assert_eq!(result.target(), index);
                assert_eq!(
                    result.ext_dimensions(),
                    ext_table(&modules[index], &modules[index], 3).unwrap()
                );
                assert_eq!(
                    result.stable_hom_dim(),
                    stable_hom(&modules[index], &modules[index]).unwrap().dim()
                );
            }
            assert_eq!(batch.work().resolutions, 2);
            assert_eq!(batch.work().target_covers, 2);
        }
    }

    #[test]
    fn selected_pairs_reuse_distinct_sources_and_targets() {
        let algebra = linear_an(3, PrimeField::new(5).unwrap());
        let modules: Vec<Module> = (0..3)
            .map(|vertex| Module::simple(&algebra, vertex))
            .collect();
        let selected = vec![(0, 0), (0, 1), (2, 1)];
        let batch = HomologicalBatch::compute(modules, selected.clone(), 2, limits()).unwrap();
        assert_eq!(batch.selected_pairs(), selected);
        assert_eq!(batch.work().resolutions, 2);
        assert_eq!(batch.work().target_covers, 2);
        assert_eq!(batch.work().hom_spaces, 3);
        assert_eq!(batch.work().projective_factor_spaces, 3);
        assert_eq!(batch.work().ext_tables, 3);
        assert!(batch.resolution(0).is_some());
        assert!(batch.resolution(1).is_none());
        assert_eq!(
            batch.stable_hom(1).unwrap().dim(),
            batch.pairs()[1].stable_hom_dim()
        );
    }

    #[test]
    fn all_pairs_use_source_major_order() {
        let algebra = linear_an(2, PrimeField::new(5).unwrap());
        let modules: Vec<Module> = (0..2)
            .map(|vertex| Module::simple(&algebra, vertex))
            .collect();
        let batch = HomologicalBatch::all_pairs(modules, 1, limits()).unwrap();
        assert_eq!(batch.selected_pairs(), &[(0, 0), (0, 1), (1, 0), (1, 1)]);
    }

    #[test]
    fn preflight_rejects_bad_pairs_and_limits() {
        let algebra = linear_an(2, PrimeField::new(5).unwrap());
        let modules = vec![Module::simple(&algebra, 0)];
        assert!(matches!(
            HomologicalBatch::compute(modules.clone(), vec![(0, 1)], 1, limits()),
            Err(HomologicalBatchError::PairIndex { .. })
        ));
        assert!(matches!(
            HomologicalBatch::compute(modules.clone(), vec![(0, 0), (0, 0)], 1, limits()),
            Err(HomologicalBatchError::DuplicatePair { .. })
        ));
        assert!(matches!(
            HomologicalBatch::self_pairs(
                modules,
                2,
                HomologicalBatchLimits {
                    max_pairs: 1,
                    max_ext_cells: 2,
                },
            ),
            Err(HomologicalBatchError::ExtCellLimit { .. })
        ));
    }

    #[test]
    fn modules_from_distinct_algebra_objects_are_rejected() {
        let field = PrimeField::new(5).unwrap();
        let left = linear_an(2, field);
        let right = linear_an(2, field);
        let modules = vec![Module::simple(&left, 0), Module::simple(&right, 0)];
        assert!(matches!(
            HomologicalBatch::self_pairs(modules, 1, limits()),
            Err(HomologicalBatchError::DifferentAlgebra { module: 1 })
        ));
    }
}
