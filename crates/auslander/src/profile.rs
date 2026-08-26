//! Exact call counters for the primitives and the layers above them, behind
//! the `profiling` feature.
//!
//! A counted site adds one to a `u64` every time control enters it. The counts
//! are exact and machine-independent, so two commits are comparable where wall
//! clock is not. The numbers say how often a primitive ran, not how long it
//! took.
//!
//! Without the `profiling` feature [`hit`] has an empty body, [`snapshot`] and
//! [`distinct_snapshot`] return zeros, and [`ENABLED`] is false. The feature is
//! off by default. No released build carries the counters.
//!
//! Counts are process wide, not per thread. Each thread increments its own
//! shard and [`snapshot`] sums every shard that has ever been created, so work
//! moved onto worker threads still lands in the total. A shard outlives its
//! thread, which keeps a finished worker's counts visible. Take the snapshot
//! after joining the threads you are measuring: a shard is read with
//! [`std::sync::atomic::Ordering::Relaxed`], so a join is what orders a
//! worker's last increment before the read.
//!
//! [`hit_module`] additionally records the nominal identity of its module, so
//! [`distinct_snapshot`] says how many different modules a site ran on against
//! how many times it ran. The store owns a clone of each module it counts, so
//! a freed allocation cannot recycle its address into a second entry.

#[cfg(feature = "profiling")]
use std::collections::HashSet;
#[cfg(feature = "profiling")]
use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(feature = "profiling")]
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};

use crate::module::Module;

/// Declares the site enum and its names from one list, so the two cannot drift.
macro_rules! sites {
    ($($variant:ident => $name:literal,)*) => {
        /// A counted call site.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        #[repr(usize)]
        pub enum Site { $($variant,)* }

        /// Site names, indexed by the discriminant of [`Site`].
        pub const NAMES: &[&str] = &[$($name,)*];
    };
}

sites! {
    FieldMul => "field::mul",
    FieldInv => "field::inv",
    FieldAdd => "field::add",
    FieldSub => "field::sub",
    FieldReduceWide => "field::reduce_wide",
    DenseMul => "DenseMat::mul",
    DenseMulVec => "DenseMat::mul_vec",
    DenseAdd => "DenseMat::add",
    DenseTranspose => "DenseMat::transpose",
    DenseRref => "DenseMat::rref",
    DenseEchelon => "DenseMat::echelon_in_place",
    DenseRank => "DenseMat::rank",
    DenseKernelBasis => "DenseMat::kernel_basis",
    DenseRowSpaceBasis => "DenseMat::row_space_basis",
    DenseSolve => "DenseMat::solve",
    DenseSolveMany => "DenseMat::solve_many",
    DenseInverse => "DenseMat::inverse",
    DenseFirstNoncanonical => "DenseMat::first_noncanonical",
    RowReducerPush => "RowReducer::push",
    SparseMul => "SparseMat::mul",
    SparseRref => "SparseMat::rref",
    SparseEchelon => "SparseMat::echelon_in_place",
    SparseKernelBasis => "SparseMat::kernel_basis",
    SparseSolve => "SparseMat::solve",
    Hom => "hom::hom",
    HomDim => "hom::hom_dim",
    MorphismNew => "Morphism::new",
    MorphismSquare => "Morphism::new commuting square",
    MorphismThen => "Morphism::then",
    ExpressInRowBasis => "hom::express_in_row_basis",
    SolveColumns => "hom::solve_columns",
    HomKernel => "hom::kernel",
    HomImage => "hom::image",
    HomCokernel => "hom::cokernel",
    Submodule => "hom::submodule_with_inclusion",
    Quotient => "hom::quotient_with_projection",
    ModuleNew => "Module::new",
    ModuleRelationCheck => "Module::new relation check",
    ModuleProjective => "Module::projective",
    ModuleInjective => "Module::injective",
    WordAction => "Module::word_action",
    ElementAction => "Module::element_action",
    DirectSum => "module::direct_sum",
    AlgebraNew => "Algebra::new",
    AlgebraFromVerified => "Algebra::from_verified_with_limits",
    MulBasis => "Algebra::mul_basis",
    NfWord => "Algebra::nf_word",
    Opposite => "opposite::opposite",
    Dual => "opposite::dual",
    NuOfPresentation => "opposite::nu_of_presentation_map",
    MinimalPresentation => "resolution::minimal_presentation_matrix",
    HomSpaceNew => "HomSpace::new",
    Tau => "ar::tau",
    TauNakayamaRoute => "ar::nakayama_kernel_route",
    TauTransposeDualRoute => "ar::transpose_dual_route",
    TauWithOpposite => "taurigid::tau_with_opposite",
    TauCacheLookup => "TauCache::tau_of",
    IsIsomorphic => "iso::is_isomorphic",
    IndecomposableIso => "iso::indecomposable_iso",
    FingerprintOf => "Fingerprint::of",
    EndoNew => "EndoAlgebra::new",
    EndoFromSummand => "EndoAlgebra::from_summand",
    EndoOver => "EndoAlgebra::over",
    Decompose => "decompose::decompose",
    KrullSchmidt => "decompose::krull_schmidt",
    IndecNew => "IndecomposableModule::new",
    IndecFromEndo => "IndecomposableModule::from_endo",
    BasicDecompositionNew => "BasicDecomposition::new",
    PairIso => "basic::pair_iso",
    PairFingerprintNew => "PairFingerprint::new",
    SupportPairIsoWitnessVerify => "SupportPairIsoWitness::verify",
    AddClosureWitnessVerify => "AddClosureWitness::verify",
    LeftApproximation => "approx::left_approximation",
    LeftApproximationVerify => "MinimalLeftApproximation::verify",
    SupportPairClassify => "SupportTauTiltingPair::classify_with_cache",
    SupportPairVerify => "SupportTauTiltingPair::verify",
    AlmostCompleteClassify => "AlmostCompletePair::classify_with_cache",
    AlmostCompleteVerify => "AlmostCompletePair::verify",
    TauRigidVerify => "TauRigidModule::verify",
    FacWitnessVerify => "FacWitness::verify",
    MutationWitnessVerify => "MutationWitness::verify",
    MutationVerify => "Mutation::verify",
    ClosureWitnessVerify => "ClosureWitness::verify",
}

/// Whether the crate was built with the `profiling` feature.
pub const ENABLED: bool = cfg!(feature = "profiling");

/// One thread's counts. Only the owning thread writes, so the atomics never
/// contend; they are atomics because [`snapshot`] reads them from elsewhere.
#[cfg(feature = "profiling")]
type Shard = Arc<[AtomicU64; NAMES.len()]>;

/// Every shard ever created, including those of threads that have exited.
#[cfg(feature = "profiling")]
fn shards() -> MutexGuard<'static, Vec<Shard>> {
    static SHARDS: OnceLock<Mutex<Vec<Shard>>> = OnceLock::new();
    SHARDS
        .get_or_init(|| Mutex::new(Vec::new()))
        .lock()
        .expect("the shard registry holds no value that can panic while locked")
}

#[cfg(feature = "profiling")]
thread_local! {
    static SHARD: Shard = {
        let shard: Shard = Arc::new([const { AtomicU64::new(0) }; NAMES.len()]);
        shards().push(Arc::clone(&shard));
        shard
    };
}

/// The distinct modules seen at each site, and the clones that keep their
/// addresses reserved.
#[cfg(feature = "profiling")]
struct Distinct {
    seen: Vec<HashSet<usize>>,
    keep: Vec<Module>,
}

#[cfg(feature = "profiling")]
fn distinct() -> MutexGuard<'static, Distinct> {
    static DISTINCT: OnceLock<Mutex<Distinct>> = OnceLock::new();
    DISTINCT
        .get_or_init(|| {
            Mutex::new(Distinct {
                seen: vec![HashSet::new(); NAMES.len()],
                keep: Vec::new(),
            })
        })
        .lock()
        .expect("the distinct store holds no value that can panic while locked")
}

/// Adds one to the count of `site` on the calling thread's shard.
///
/// Without the `profiling` feature the body is empty and the call inlines
/// away.
#[inline]
pub fn hit(site: Site) {
    #[cfg(feature = "profiling")]
    SHARD.with(|shard| {
        shard[site as usize].fetch_add(1, Ordering::Relaxed);
    });
    #[cfg(not(feature = "profiling"))]
    let _ = site;
}

/// Adds one to the count of `site` and records `m` under its nominal identity.
///
/// Use it where the question is how much of a site's work is repeated. The
/// call count over the distinct count is how many times the average module
/// went through the site. Identity is [`Module::ptr_eq`], the same key a cache
/// can use soundly, so two isomorphic modules built separately count twice.
/// The store takes a clone, which is an [`std::sync::Arc`] bump, and holds it
/// for the rest of the interval.
///
/// This one takes a lock, so it belongs at a site whose own cost is far above
/// a lock, not on a primitive.
#[inline]
pub fn hit_module(site: Site, m: &Module) {
    hit(site);
    #[cfg(feature = "profiling")]
    {
        let mut store = distinct();
        if store.seen[site as usize].insert(m.addr()) {
            store.keep.push(m.clone());
        }
    }
    #[cfg(not(feature = "profiling"))]
    let _ = m;
}

/// Sets every count on every shard back to zero and drops the recorded
/// modules.
///
/// Call it while no counted work is running. A reset that overlaps a counting
/// thread loses that thread's increments in flight.
pub fn reset() {
    #[cfg(feature = "profiling")]
    {
        for shard in shards().iter() {
            for cell in shard.iter() {
                cell.store(0, Ordering::Relaxed);
            }
        }
        let mut store = distinct();
        for seen in &mut store.seen {
            seen.clear();
        }
        store.keep.clear();
    }
}

/// The counts summed over every shard, indexed as [`NAMES`].
///
/// Without the `profiling` feature every entry is zero.
pub fn snapshot() -> Vec<u64> {
    #[cfg(feature = "profiling")]
    {
        let mut out = vec![0u64; NAMES.len()];
        for shard in shards().iter() {
            for (total, cell) in out.iter_mut().zip(shard.iter()) {
                *total += cell.load(Ordering::Relaxed);
            }
        }
        out
    }
    #[cfg(not(feature = "profiling"))]
    {
        vec![0; NAMES.len()]
    }
}

/// The number of nominally distinct modules recorded at each site, indexed as
/// [`NAMES`].
///
/// A site reached through [`hit`] rather than [`hit_module`] stays zero here,
/// which is an absence of a record and not a measured zero.
pub fn distinct_snapshot() -> Vec<usize> {
    #[cfg(feature = "profiling")]
    {
        distinct().seen.iter().map(HashSet::len).collect()
    }
    #[cfg(not(feature = "profiling"))]
    {
        vec![0; NAMES.len()]
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    /// Serializes tests that reset the process-wide profiling counters.
    pub(crate) fn reset_lock() -> std::sync::MutexGuard<'static, ()> {
        static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        LOCK.get_or_init(|| std::sync::Mutex::new(()))
            .lock()
            .expect("a profiling test does not panic while it holds the reset lock")
    }

    /// The assertion is on the increase, not on a total: the test binary runs
    /// its cases concurrently and they raise the same process-wide counters.
    /// Nothing outside `benches/perf.rs` calls [`reset`], so a count only
    /// rises during a test run.
    #[test]
    fn a_count_raised_on_a_worker_thread_reaches_the_process_snapshot() {
        if !ENABLED {
            return;
        }
        let raised = 1_000u64;
        let before = snapshot()[Site::FieldMul as usize];
        std::thread::spawn(move || {
            for _ in 0..raised {
                hit(Site::FieldMul);
            }
        })
        .join()
        .expect("the worker only adds to a counter");
        assert!(snapshot()[Site::FieldMul as usize] >= before + raised);
    }
}
