/// A deterministic finite-field module census request.
#[derive(Clone, Debug)]
pub struct Census {
    domain: CensusDomain,
}

impl Census {
    /// Builds a census for one fixed dimension vector.
    pub fn new(algebra: &Arc<Algebra>, dimensions: Vec<usize>) -> Result<Self, CensusError> {
        Ok(Self {
            domain: CensusDomain::new(algebra, dimensions)?,
        })
    }

    /// Builds a census from a borrowed dimension vector.
    pub fn from_dimensions(
        algebra: &Arc<Algebra>,
        dimensions: &[usize],
    ) -> Result<Self, CensusError> {
        Self::new(algebra, dimensions.to_vec())
    }

    accessor_methods! {
        /// The checked finite census domain.
        pub domain() -> &CensusDomain = |this| &this.domain;
    }

    /// Runs with [`CensusLimits::default`] and no cancellation control.
    pub fn run(&self) -> CensusOutcome {
        self.run_with(CensusLimits::default(), None)
    }

    /// Runs with explicit limits and optional cooperative cancellation.
    pub fn run_with(
        &self,
        limits: CensusLimits,
        control: Option<&ComputationControl>,
    ) -> CensusOutcome {
        enumerate_state(CensusState::empty(self.domain.clone(), limits), control)
    }

    /// Continues a replay-verified cut with new absolute limits.
    pub fn resume(
        &self,
        checkpoint: &CensusCut,
        limits: CensusLimits,
        control: Option<&ComputationControl>,
    ) -> Result<CensusOutcome, CensusResumeError> {
        if self.domain != checkpoint.state.domain {
            return Err(CensusResumeError::DifferentDomain);
        }
        if checkpoint.state.limits.retention != limits.retention {
            return Err(CensusResumeError::RetentionMismatch {
                checkpoint: checkpoint.state.limits.retention,
                requested: limits.retention,
            });
        }
        if !checkpoint.verify() {
            return Err(CensusResumeError::InvalidCheckpoint);
        }
        let mut state = checkpoint.state.clone();
        state.limits = limits;
        Ok(enumerate_state(state, control))
    }

    /// Replays a complete result against this request.
    pub fn replay(&self, result: &CensusResult) -> bool {
        self.domain.eq(result.domain()) && result.verify()
    }
}

/// Builds and runs a finite-field module census for one dimension vector.
pub fn census(
    algebra: &Arc<Algebra>,
    dimensions: Vec<usize>,
    limits: CensusLimits,
    control: Option<&ComputationControl>,
) -> Result<CensusOutcome, CensusError> {
    Ok(Census::new(algebra, dimensions)?.run_with(limits, control))
}

/// Returns the checked number of raw arrow-matrix tuples.
pub fn checked_search_space_size(
    algebra: &Arc<Algebra>,
    dimensions: &[usize],
) -> Result<u128, CensusError> {
    CensusDomain::new(algebra, dimensions.to_vec()).map(|domain| domain.raw_space_size())
}
