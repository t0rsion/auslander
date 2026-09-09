/// One retained representative and its raw coordinate provenance.
#[derive(Clone, Debug)]
pub struct CensusRepresentative {
    cursor: u128,
    coordinates: Vec<u64>,
    module: Module,
}

impl CensusRepresentative {
    accessor_methods! {
        /// The raw-domain cursor that produced this representative.
        pub cursor() -> u128 = |this| this.cursor;
        /// Canonical matrix entries in the domain coordinate order.
        pub coordinates() -> &[u64] = |this| &this.coordinates;
        /// The checked representative module.
        pub module() -> &Module = |this| &this.module;
    }
}

/// A checked isomorphism from one accepted candidate to a representative.
#[derive(Clone, Debug)]
pub struct CensusAssignment {
    cursor: u128,
    coordinates: Vec<u64>,
    representative: usize,
    witness: Morphism,
}

impl CensusAssignment {
    accessor_methods! {
        /// The raw-domain cursor assigned to a representative.
        pub cursor() -> u128 = |this| this.cursor;
        /// Canonical matrix entries in the domain coordinate order.
        pub coordinates() -> &[u64] = |this| &this.coordinates;
        /// The representative index in the census result.
        pub representative() -> usize = |this| this.representative;
        /// The verified candidate-to-representative isomorphism.
        pub witness() -> &Morphism = |this| &this.witness;
    }
}

#[derive(Clone, Debug)]
struct CensusState {
    domain: CensusDomain,
    limits: CensusLimits,
    cursor: u128,
    candidates: usize,
    accepted_modules: usize,
    rejected_candidates: usize,
    isomorphism_checks: usize,
    work_units: usize,
    representatives: Vec<CensusRepresentative>,
    assignments: Vec<CensusAssignment>,
}

impl CensusState {
    fn empty(domain: CensusDomain, limits: CensusLimits) -> Self {
        Self {
            domain,
            limits,
            cursor: 0,
            candidates: 0,
            accepted_modules: 0,
            rejected_candidates: 0,
            isomorphism_checks: 0,
            work_units: 0,
            representatives: Vec::new(),
            assignments: Vec::new(),
        }
    }

    fn complete(&self) -> bool {
        self.cursor == self.domain.raw_space_size()
    }
}

/// A complete finite census with one representative per decided class.
#[derive(Clone, Debug)]
pub struct CensusResult {
    state: CensusState,
}

impl CensusResult {
    accessor_methods! {
        /// The checked finite census domain.
        pub domain() -> &CensusDomain = |this| &this.state.domain;
        /// The effective resource limits.
        pub limits() -> CensusLimits = |this| this.state.limits;
        /// The first unvisited raw cursor, equal to the raw-space size.
        pub cursor() -> u128 = |this| this.state.cursor;
        /// The number of fully processed raw candidates.
        pub candidates() -> usize = |this| this.state.candidates;
        /// The number of relation-valid candidates classified into a class.
        pub accepted_modules() -> usize = |this| this.state.accepted_modules;
        /// The number of relation-invalid candidates rejected by `Module::new`.
        pub rejected_candidates() -> usize = |this| this.state.rejected_candidates;
        /// The number of completed isomorphism comparisons.
        pub isomorphism_checks() -> usize = |this| this.state.isomorphism_checks;
        /// The candidate and comparison work units used by the result.
        pub work_units() -> usize = |this| this.state.work_units;
        /// The retained representatives, in first-seen order.
        pub representatives() -> &[CensusRepresentative] = |this| &this.state.representatives;
        /// The verified duplicate assignments, in candidate order.
        pub assignments() -> &[CensusAssignment] = |this| &this.state.assignments;
    }

    /// Replays the finite domain and checks the complete result.
    pub fn verify(&self) -> bool {
        self.state.complete() && verify_state_data(&self.state) && replay_complete(&self.state)
    }
}

/// A checked census prefix stopped before its raw domain was exhausted.
#[derive(Clone, Debug)]
pub struct CensusCut {
    state: CensusState,
    reason: CensusCutReason,
}

/// A checked census prefix followed by a runtime failure.
#[derive(Clone, Debug)]
pub struct CensusFailed {
    state: CensusState,
    error: CensusFailure,
}

impl CensusFailed {
    accessor_methods! {
        /// The checked finite census domain.
        pub domain() -> &CensusDomain = |this| &this.state.domain;
        /// The first unvisited raw cursor.
        pub cursor() -> u128 = |this| this.state.cursor;
        /// The number of fully processed raw candidates.
        pub candidates() -> usize = |this| this.state.candidates;
        /// The retained representatives before the failed candidate.
        pub representatives() -> &[CensusRepresentative] = |this| &this.state.representatives;
        /// The retained duplicate assignments before the failed candidate.
        pub assignments() -> &[CensusAssignment] = |this| &this.state.assignments;
        /// The runtime failure at the first unvisited cursor.
        pub error() -> &CensusFailure = |this| &this.error;
    }

    /// Replays and checks the completed prefix before the failure.
    pub fn verify_prefix(&self) -> bool {
        verify_state_data(&self.state) && replay_prefix(&self.state)
    }
}

impl CensusCut {
    accessor_methods! {
        /// The checked finite census domain.
        pub domain() -> &CensusDomain = |this| &this.state.domain;
        /// The effective resource limits.
        pub limits() -> CensusLimits = |this| this.state.limits;
        /// The first unvisited raw cursor.
        pub cursor() -> u128 = |this| this.state.cursor;
        /// The number of fully processed raw candidates.
        pub candidates() -> usize = |this| this.state.candidates;
        /// The number of relation-valid candidates classified into a class.
        pub accepted_modules() -> usize = |this| this.state.accepted_modules;
        /// The number of relation-invalid candidates rejected by `Module::new`.
        pub rejected_candidates() -> usize = |this| this.state.rejected_candidates;
        /// The number of completed isomorphism comparisons.
        pub isomorphism_checks() -> usize = |this| this.state.isomorphism_checks;
        /// The candidate and comparison work units used by the prefix.
        pub work_units() -> usize = |this| this.state.work_units;
        /// The retained representatives, in first-seen order.
        pub representatives() -> &[CensusRepresentative] = |this| &this.state.representatives;
        /// The verified duplicate assignments, in candidate order.
        pub assignments() -> &[CensusAssignment] = |this| &this.state.assignments;
        /// The exact reason the next candidate was not committed.
        pub reason() -> &CensusCutReason = |this| &this.reason;
    }

    /// Replays the completed prefix and checks the stored representatives.
    pub fn verify(&self) -> bool {
        if !verify_state_data(&self.state) {
            return false;
        }
        if matches!(&self.reason, CensusCutReason::Cancelled) {
            return replay_prefix(&self.state);
        }
        replay_cut(&self.state, &self.reason)
    }
}

/// The three typed outcomes of one census request.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum CensusOutcome {
    /// Every raw tuple was processed and every class decision was certified.
    Complete(CensusResult),
    /// A checked prefix stopped at a caller limit, cancellation, or unknown.
    Cut(CensusCut),
    /// A checked domain encountered a runtime failure.
    Failed(CensusFailed),
}

impl CensusOutcome {
    optional_accessors! {
        /// The complete result, if enumeration finished.
        pub complete() -> &CensusResult = Self::Complete(value) => value;
        /// The checked prefix, if enumeration stopped early.
        pub cut() -> &CensusCut = Self::Cut(value) => value;
        /// The runtime failure, if enumeration could not produce a prefix.
        pub failed() -> &CensusFailed = Self::Failed(value) => value;
    }

    /// Replays a complete result or checked prefix.
    pub fn verify(&self) -> bool {
        match self {
            Self::Complete(result) => result.verify(),
            Self::Cut(cut) => cut.verify(),
            Self::Failed(failed) => failed.verify_prefix(),
        }
    }
}

/// A rejected in-memory census checkpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CensusResumeError {
    /// The checkpoint belongs to another algebra object or dimension vector.
    DifferentDomain,
    /// Replaying the checkpoint did not reproduce its exact prefix.
    InvalidCheckpoint,
    /// The resumed request changes the checkpoint retention mode.
    RetentionMismatch {
        checkpoint: CensusRetention,
        requested: CensusRetention,
    },
}

display_error! { error CensusResumeError {
    Self::DifferentDomain => "the census checkpoint belongs to another domain";
    Self::InvalidCheckpoint => "the census checkpoint failed replay verification";
    Self::RetentionMismatch { checkpoint, requested } => "the census checkpoint uses retention {checkpoint:?}, request uses {requested:?}";
} }
