//! Exact call counters for the primitives, behind the `profiling` feature.
//!
//! A counted site adds one to a `u64` every time control enters it. The counts
//! are exact and machine-independent, so two commits are comparable where wall
//! clock is not. Sampling profilers answer a different question and are not a
//! substitute: these numbers say how often a primitive ran, not how long it
//! took.
//!
//! Without the `profiling` feature [`hit`] has an empty body, [`snapshot`]
//! returns zeros, and [`ENABLED`] is false. The feature is off by default and
//! no released build carries the counters.
//!
//! Counts are per calling thread. The harness in `benches/perf.rs` runs on one
//! thread, so its totals are whole.

#[cfg(feature = "profiling")]
use std::cell::Cell;

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
}

/// Whether the counters record anything, that is, whether the crate was built
/// with the `profiling` feature.
pub const ENABLED: bool = cfg!(feature = "profiling");

#[cfg(feature = "profiling")]
thread_local! {
    static COUNTS: [Cell<u64>; NAMES.len()] =
        const { [const { Cell::new(0) }; NAMES.len()] };
}

/// Adds one to the count of `site`.
///
/// Without the `profiling` feature the body is empty and the call inlines
/// away.
#[inline]
pub fn hit(site: Site) {
    #[cfg(feature = "profiling")]
    COUNTS.with(|c| {
        let cell = &c[site as usize];
        cell.set(cell.get() + 1);
    });
    #[cfg(not(feature = "profiling"))]
    let _ = site;
}

/// Sets every count on this thread back to zero.
pub fn reset() {
    #[cfg(feature = "profiling")]
    COUNTS.with(|c| {
        for cell in c {
            cell.set(0);
        }
    });
}

/// The counts on this thread, indexed as [`NAMES`].
///
/// Without the `profiling` feature every entry is zero.
pub fn snapshot() -> Vec<u64> {
    #[cfg(feature = "profiling")]
    {
        COUNTS.with(|c| c.iter().map(Cell::get).collect())
    }
    #[cfg(not(feature = "profiling"))]
    {
        vec![0; NAMES.len()]
    }
}
