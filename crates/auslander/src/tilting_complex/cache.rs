use super::classification::quotient;
use super::{TiltingComplexCandidate, TiltingComplexError};
use crate::homotopy::HomotopyHomQuotient;

/// Exact Homotopy-block work for one tilting construction.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TiltingComplexWork {
    hom_spaces_built: usize,
    hom_spaces_reused: usize,
}

impl TiltingComplexWork {
    accessor_methods! {
        /// The number of Homotopy quotients built from linear algebra.
        pub hom_spaces_built() -> usize = |this| this.hom_spaces_built;
        /// The number of Homotopy quotients reused from exact cached data.
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
    cache: HomotopyBlockCache,
    pub(super) work: TiltingComplexWork,
    pub(super) budget_built: usize,
    charge_budget: bool,
    changed: Option<usize>,
}

impl<'a> HomotopyBlockBuilder<'a> {
    pub(super) fn cold() -> HomotopyBlockBuilder<'static> {
        HomotopyBlockBuilder {
            inherited: None,
            cache: HomotopyBlockCache::default(),
            work: TiltingComplexWork::default(),
            budget_built: 0,
            charge_budget: false,
            changed: None,
        }
    }

    pub(super) fn with_inherited(inherited: &'a HomotopyBlockCache) -> HomotopyBlockBuilder<'a> {
        HomotopyBlockBuilder {
            inherited: Some(inherited),
            cache: HomotopyBlockCache::default(),
            work: TiltingComplexWork::default(),
            budget_built: 0,
            charge_budget: false,
            changed: None,
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
        if self
            .changed
            .is_some_and(|changed| source == changed || target == changed)
        {
            return self
                .cache
                .matching(candidate, source, target, degree)
                .is_some();
        }
        self.cache
            .matching(candidate, source, target, degree)
            .or_else(|| {
                self.inherited
                    .and_then(|cache| cache.matching(candidate, source, target, degree))
            })
            .is_some()
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
    ) -> Result<HomotopyHomQuotient, TiltingComplexError> {
        if let Some(quotient) = self.cache.matching(candidate, source, target, degree) {
            self.work.hom_spaces_reused += 1;
            return Ok(quotient);
        }
        if let Some(quotient) = self
            .changed
            .filter(|&changed| source == changed || target == changed)
            .is_none()
            .then(|| {
                self.inherited
                    .and_then(|cache| cache.matching(candidate, source, target, degree))
            })
            .flatten()
        {
            self.work.hom_spaces_reused += 1;
            self.cache.blocks.push(CachedHomotopyBlock {
                source,
                target,
                degree,
                quotient: quotient.clone(),
            });
            return Ok(quotient);
        }
        let quotient = quotient(
            &candidate.summands()[source],
            &candidate.summands()[target],
            degree,
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
