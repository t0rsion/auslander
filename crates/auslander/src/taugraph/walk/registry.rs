use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::basic::PairFingerprint;
use crate::indec::IndecomposableModule;
use crate::iso::indecomposable_iso;
use crate::module::Module;
use crate::taurigid::TauCache;

use super::super::contracts::{GraphLimit, GraphVertex, MutationGraphLimits, VerifiedMutation};
use super::accounting::{WorkLedger, iso_units, scale_of};

/// The indecomposables the walk has discovered, each with a stable index.
///
/// The index labels an isomorphism class for witnesses and for the Python
/// bindings. It does not key the shared [`TauCache`], which keys on nominal
/// module identity.
///
/// Module identity in this crate is nominal, and every decomposition returns
/// fresh module values, so an index is recovered by a certified isomorphism
/// test. Indices are never reused for a second isomorphism class.
#[derive(Default)]
pub(super) struct SummandRegistry {
    entries: Vec<(usize, Module)>,
    next: usize,
}

impl SummandRegistry {
    /// An index no entry holds.
    pub(super) fn fresh(&mut self) -> usize {
        let index = self.next;
        self.next += 1;
        index
    }

    /// The index of the entry isomorphic to `x`, or `None`.
    ///
    /// The dimension vector prefilters the scan, and the certified radical
    /// criterion decides. Charges one isomorphism test per candidate the
    /// prefilter admits.
    pub(super) fn lookup(
        &self,
        x: &IndecomposableModule,
        ledger: &mut WorkLedger,
    ) -> Option<usize> {
        let scale = scale_of(x.module().dim_vector());
        for (index, entry) in &self.entries {
            if entry.dim_vector() != x.module().dim_vector() {
                continue;
            }
            ledger.charge(iso_units(1, scale));
            // The radical criterion takes the endomorphism algebra of its
            // first argument, so the query supplies it and the stored entry
            // needs only its module.
            if indecomposable_iso(x.module(), entry, x.endo()).is_some() {
                return Some(*index);
            }
        }
        None
    }

    pub(super) fn insert(&mut self, index: usize, x: Module) {
        self.entries.push((index, x));
    }
}

/// Why the walk stopped before the frontier emptied.
pub(super) enum Stop {
    Budget(GraphLimit),
    Blocked(String),
}

/// The state of one [`crate::taugraph::support_tau_tilting_graph`] run.
pub(super) struct Walk<'a> {
    pub(super) algebra: Arc<Algebra>,
    pub(super) limits: &'a MutationGraphLimits,
    pub(super) cache: TauCache,
    pub(super) registry: SummandRegistry,
    pub(super) ledger: WorkLedger,
    pub(super) vertices: Vec<GraphVertex>,
    pub(super) indices: Vec<Vec<usize>>,
    pub(super) fingerprints: Vec<PairFingerprint>,
    pub(super) buckets: HashMap<PairFingerprint, Vec<usize>>,
    pub(super) mutations: Vec<VerifiedMutation>,
    pub(super) queue: VecDeque<usize>,
    pub(super) total_slots: usize,
    pub(super) verified_slots: usize,
    pub(super) new_vertices: usize,
    pub(super) repeated_endpoints: usize,
    pub(super) at_vertex: usize,
    pub(super) at_slot: Option<usize>,
}

pub(super) struct SlotPlan {
    pub(super) summands: usize,
    pub(super) scale: u64,
    pub(super) fresh: usize,
    pub(super) indices: Vec<usize>,
}
