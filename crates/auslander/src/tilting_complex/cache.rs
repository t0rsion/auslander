use super::classification::quotient;
use super::{Interrupt, TiltingComplexCandidate};
use crate::control::WorkMeter;
use crate::homotopy::{HomSpaceMemo, HomotopyHomQuotient};

/// Exact homotopy-block work for one tilting construction.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TiltingComplexWork {
    hom_spaces_built: usize,
    hom_spaces_reused: usize,
}

impl TiltingComplexWork {
    accessor_methods! {
        /// The number of homotopy quotients built from linear algebra.
        pub hom_spaces_built() -> usize = |this| this.hom_spaces_built;
        /// The number of homotopy quotients reused from exact cached data.
        pub hom_spaces_reused() -> usize = |this| this.hom_spaces_reused;
    }
}

#[derive(Clone, Debug)]
struct CachedHomotopyBlock {
    source: usize,
    target: usize,
    degree: i32,
    quotient: HomotopyHomQuotient,
}

#[derive(Clone, Debug, Default)]
pub(super) struct HomotopyBlockCache {
    blocks: Vec<CachedHomotopyBlock>,
}

impl HomotopyBlockCache {
    fn matching(
        &self,
        candidate: &TiltingComplexCandidate,
        source: usize,
        target: usize,
        degree: i32,
    ) -> Option<HomotopyHomQuotient> {
        self.blocks
            .iter()
            .find(|block| {
                block.source == source
                    && block.target == target
                    && block.degree == degree
                    && block
                        .quotient
                        .source()
                        .agrees_with(candidate.summands()[source].complex())
                    && block
                        .quotient
                        .target()
                        .agrees_with(candidate.summands()[target].complex())
            })
            .map(|block| block.quotient.clone())
    }

    fn retain_candidate(&mut self, candidate: &TiltingComplexCandidate) {
        self.blocks.retain(|block| {
            candidate
                .summands()
                .get(block.source)
                .is_some_and(|source| block.quotient.source().agrees_with(source.complex()))
                && candidate
                    .summands()
                    .get(block.target)
                    .is_some_and(|target| block.quotient.target().agrees_with(target.complex()))
        });
    }
}

pub(super) struct HomotopyBlockBuilder<'a> {
    inherited: Option<&'a HomotopyBlockCache>,
    pub(super) meter: &'a mut WorkMeter,
    cache: HomotopyBlockCache,
    pub(super) work: TiltingComplexWork,
    pub(super) budget_built: usize,
    charge_budget: bool,
    changed: Option<usize>,
    homs: HomSpaceMemo,
}

impl<'a> HomotopyBlockBuilder<'a> {
    pub(super) fn cold(meter: &'a mut WorkMeter) -> HomotopyBlockBuilder<'a> {
        HomotopyBlockBuilder::inheriting(None, meter)
    }

    pub(super) fn with_inherited(
        inherited: &'a HomotopyBlockCache,
        meter: &'a mut WorkMeter,
    ) -> HomotopyBlockBuilder<'a> {
        HomotopyBlockBuilder::inheriting(Some(inherited), meter)
    }

    fn inheriting(
        inherited: Option<&'a HomotopyBlockCache>,
        meter: &'a mut WorkMeter,
    ) -> HomotopyBlockBuilder<'a> {
        HomotopyBlockBuilder {
            inherited,
            meter,
            cache: HomotopyBlockCache::default(),
            work: TiltingComplexWork::default(),
            budget_built: 0,
            charge_budget: false,
            changed: None,
            homs: HomSpaceMemo::default(),
        }
    }

    pub(super) fn set_changed(&mut self, changed: usize) {
        self.changed = Some(changed);
        self.cache
            .blocks
            .retain(|block| block.source != changed && block.target != changed);
    }

    pub(super) fn begin_classification(&mut self) {
        self.budget_built = 0;
        self.charge_budget = true;
    }

    pub(super) fn cached(
        &self,
        candidate: &TiltingComplexCandidate,
        source: usize,
        target: usize,
        degree: i32,
    ) -> bool {
        self.cache
            .matching(candidate, source, target, degree)
            .or_else(|| self.inherited_block(candidate, source, target, degree))
            .is_some()
    }

    /// The inherited block, unless the summand at either end changed.
    fn inherited_block(
        &self,
        candidate: &TiltingComplexCandidate,
        source: usize,
        target: usize,
        degree: i32,
    ) -> Option<HomotopyHomQuotient> {
        let changed = self
            .changed
            .is_some_and(|changed| source == changed || target == changed);
        let inherited = self.inherited.filter(|_| !changed)?;
        inherited.matching(candidate, source, target, degree)
    }

    pub(super) fn blocks_needed(
        &self,
        candidate: &TiltingComplexCandidate,
        keys: &[(usize, usize, i32)],
    ) -> usize {
        keys.iter()
            .filter(|&&(source, target, degree)| !self.cached(candidate, source, target, degree))
            .count()
    }

    pub(super) fn get(
        &mut self,
        candidate: &TiltingComplexCandidate,
        source: usize,
        target: usize,
        degree: i32,
    ) -> Result<HomotopyHomQuotient, Interrupt> {
        if let Some(quotient) = self.cache.matching(candidate, source, target, degree) {
            self.work.hom_spaces_reused += 1;
            return Ok(quotient);
        }
        if let Some(quotient) = self.inherited_block(candidate, source, target, degree) {
            self.work.hom_spaces_reused += 1;
            self.cache.blocks.push(CachedHomotopyBlock {
                source,
                target,
                degree,
                quotient: quotient.clone(),
            });
            return Ok(quotient);
        }
        self.meter.charge()?;
        let quotient = quotient(
            &candidate.summands()[source],
            &candidate.summands()[target],
            degree,
            &mut self.homs,
        )?;
        self.work.hom_spaces_built += 1;
        if self.charge_budget {
            self.budget_built += 1;
        }
        self.cache.blocks.push(CachedHomotopyBlock {
            source,
            target,
            degree,
            quotient: quotient.clone(),
        });
        Ok(quotient)
    }

    pub(super) fn finish(
        mut self,
        candidate: &TiltingComplexCandidate,
    ) -> (HomotopyBlockCache, TiltingComplexWork) {
        self.cache.retain_candidate(candidate);
        (self.cache, self.work)
    }
}
