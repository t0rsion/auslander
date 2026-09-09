/// The size factor of every rate below: the unknown count of `Hom(M, M)` for a
/// module of dimension vector `dims`, and never less than 1.
///
/// One unit is one unknown of one Hom system. Every rate names a number of Hom
/// systems and multiplies it by this factor, which is an upper bound for the
/// unknown count of each system in the modelled sequence: the arguments are
/// summands of `M` or simple modules, and `sum_v dim U_v dim W_v` is at most
/// `sum_v (dim M_v)^2` when `U` and `W` are summands of `M`.
///
/// The bound does not cover the systems inside `tau`, since the translate is
/// not known before the call. That term keeps the rate the design fixed for it,
/// scaled by the module the walk is standing on.
///
/// Without this factor a rate charged by call alone does not brake a
/// tau-tilting infinite walk. See [`crate::taugraph::ClosedSupportTauTiltingGraph::work_units`]
/// for the measured gap.
pub(super) fn scale_of(dims: &[usize]) -> u64 {
    let entries: u64 = dims.iter().map(|&d| (d as u64) * (d as u64)).sum();
    entries.max(1)
}

/// Units for `systems` Hom systems of at most `scale` unknowns each.
pub(super) const fn hom_units(systems: u64, scale: u64) -> u64 {
    systems * scale
}

/// Units for one Krull-Schmidt decomposition of a module with `summands`
/// summands, which grows as the cube of the summand count.
pub(super) fn decompose_units(summands: usize, scale: u64) -> u64 {
    8 * (summands as u64).pow(3) * scale
}

/// Units for one certified isomorphism test between modules with `summands`
/// summands.
pub(super) fn iso_units(summands: usize, scale: u64) -> u64 {
    decompose_units(summands, scale) + 16 * scale
}

/// Units for one `tau` on a module with `summands` summands. The walk only
/// ever charges the indecomposable case.
pub(super) fn tau_units(summands: usize, scale: u64) -> u64 {
    64 * summands as u64 * scale + decompose_units(summands, scale)
}

/// Units for one certified indecomposability gate.
pub(super) fn indec_units(scale: u64) -> u64 {
    8 * scale
}

/// Units for one slot visit at a vertex with `summands` module summands, at
/// size factor `scale`.
///
/// The model is the call sequence of [`crate::mutation::mutate_at_with_cache`], charged by the
/// rates of `docs/support-tau-tilting.md` section 8. The Fac test builds one Hom
/// system, `Hom(U, X_j)`, and a slot with no left mutation stops there. A left
/// mutation continues with the decomposition of `U`, the almost complete
/// pair's Hom systems, the decomposition of the cokernel and the
/// indecomposability gate on its first summand, the decomposition of the
/// target, the target pair's Hom systems, and the certified comparison of the
/// two endpoints.
///
/// `tau` is not charged here. It is counted exactly, from the miss counter of
/// the shared [`crate::taurigid::TauCache`], because the cache is what decides whether a call
/// runs at all.
pub(super) fn slot_units(summands: usize, left_mutation: bool, scale: u64) -> u64 {
    let mut units = hom_units(1, scale);
    if !left_mutation {
        return units;
    }
    let kept = summands - 1;
    units += decompose_units(kept, scale) + kept as u64 * indec_units(scale);
    units += hom_units((kept * kept) as u64 + 1, scale);
    units += decompose_units(1, scale) + indec_units(scale);
    units += decompose_units(summands, scale) + summands as u64 * indec_units(scale);
    units += hom_units((summands * summands) as u64 + 1, scale);
    units + iso_units(summands, scale)
}

/// Units for classifying one vertex pair with `summands` module summands, at
/// size factor `scale`.
pub(super) fn vertex_units(summands: usize, scale: u64) -> u64 {
    decompose_units(summands, scale)
        + summands as u64 * indec_units(scale)
        + hom_units((summands * summands) as u64 + 1, scale)
}

/// Units for one [`crate::basic::PairFingerprint`], which runs two Hom dimensions per
/// summand against each of the `vertices` simple modules.
pub(super) fn fingerprint_units(summands: usize, vertices: usize, scale: u64) -> u64 {
    hom_units(2 * (summands * vertices) as u64, scale)
}

/// The entries of the Hom system for `(m, n)`, which has `sum_v dim m_v dim
/// n_v` unknowns.
pub(super) fn hom_entries(m: &[usize], n: &[usize]) -> usize {
    m.iter().zip(n).map(|(a, b)| a * b).sum()
}

/// The running work-unit count of one walk.
///
/// Units are charged by call and by module size, never by time, so a count is
/// exact and profile-independent. The ledger is a model of the call sequence
/// the walk runs, at the rates above, with one exception: the `tau` term is
/// counted from the shared [`crate::taurigid::TauCache`] miss counter rather than modelled,
/// since the cache decides which calls run.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct WorkLedger {
    pub(super) units: u64,
}

impl WorkLedger {
    pub(super) fn charge(&mut self, units: u64) {
        self.units += units;
    }

    /// Charges `misses` translates of an indecomposable at size factor
    /// `scale`.
    pub(super) fn charge_tau_misses(&mut self, misses: u64, scale: u64) {
        self.units += misses * tau_units(1, scale);
    }

    /// Whether `extra` further units would exceed `limit`.
    pub(super) fn would_exceed(&self, extra: u64, limit: u64) -> bool {
        self.units + extra > limit
    }
}
