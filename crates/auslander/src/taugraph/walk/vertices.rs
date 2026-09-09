use crate::basic::{
    BasicDecomposition, PairFingerprint, ProjectiveSupport, SupportPairIsoOutcome,
    SupportPairIsoWitness, pair_iso,
};
use crate::supporttau::{SupportTauTiltingClassification, SupportTauTiltingPair};

use super::super::contracts::{GraphError, GraphVertex, defect, support_blocker};
use super::accounting::{fingerprint_units, iso_units, scale_of, vertex_units};
use super::registry::{Stop, Walk};

impl Walk<'_> {
    /// The number of vertices of the quiver, which is `n`.
    pub(super) fn quiver_vertices(&self) -> usize {
        self.algebra.quiver().num_vertices() as usize
    }

    /// Charges the translates the shared cache computed since the miss count
    /// was `misses_before`, at the size factor of the module the walk stands
    /// on.
    ///
    /// A hit costs nothing, which is why the walk shares one cache.
    pub(super) fn charge_tau(&mut self, misses_before: u64, scale: u64) {
        let misses = self.cache.misses() - misses_before;
        self.ledger.charge_tau_misses(misses, scale);
    }

    /// The stable index of each summand of `decomposition`, registering the
    /// ones the walk has not seen.
    ///
    /// `preferred` is the index a mutation already spent on its cokernel
    /// summand. Reusing it keeps one index per isomorphism class, so the
    /// registry does not grow a second label for the same class. It does not
    /// preserve the cached translate: the cache is keyed by module identity,
    /// and re-decomposition produces a fresh module value that misses.
    fn resolve_indices(
        &mut self,
        decomposition: &BasicDecomposition,
        preferred: Option<usize>,
    ) -> Vec<usize> {
        let mut preferred = preferred;
        let mut out = Vec::with_capacity(decomposition.len());
        for x in decomposition.summands() {
            if let Some(index) = self.registry.lookup(x, &mut self.ledger) {
                out.push(index);
                continue;
            }
            let index = preferred.take().unwrap_or_else(|| self.registry.fresh());
            self.registry.insert(index, x.module().clone());
            out.push(index);
        }
        out
    }

    /// Classifies `(module, support)` and pushes it as a further vertex.
    pub(super) fn push_vertex(
        &mut self,
        module: BasicDecomposition,
        support: ProjectiveSupport,
        preferred: Option<usize>,
    ) -> Result<Result<usize, Stop>, GraphError> {
        let summands = module.len();
        let n = self.quiver_vertices();
        let scale = scale_of(module.module().dim_vector());
        self.ledger.charge(vertex_units(summands, scale));
        let indices = self.resolve_indices(&module, preferred);
        let misses = self.cache.misses();
        let classification = SupportTauTiltingPair::classify_with_cache(
            module,
            support,
            &indices,
            Some(&mut self.cache),
        );
        self.charge_tau(misses, scale);
        let classification = match classification {
            Ok(classification) => classification,
            Err(error) => {
                if let Some(reason) = support_blocker(&error) {
                    return Ok(Err(Stop::Blocked(reason)));
                }
                return Err(error.into());
            }
        };
        let pair = match classification {
            SupportTauTiltingClassification::Pair(pair) => pair,
            SupportTauTiltingClassification::Rejected(rejection) => {
                return Err(defect(format!(
                    "a mutation target left condition {} unmet: {rejection}",
                    rejection.condition()
                )));
            }
        };
        self.ledger.charge(fingerprint_units(summands, n, scale));
        let fingerprint = PairFingerprint::new(pair.module(), &pair.projective())?;
        let index = self.vertices.len();
        self.buckets
            .entry(fingerprint.clone())
            .or_default()
            .push(index);
        self.fingerprints.push(fingerprint);
        self.indices.push(indices);
        self.total_slots += summands;
        self.vertices.push(GraphVertex {
            pair,
            slots: Vec::with_capacity(summands),
        });
        self.queue.push_back(index);
        Ok(Ok(index))
    }

    /// The vertex isomorphic to `pair`, with the witness, or `None`.
    ///
    /// The fingerprint buckets the candidates and [`pair_iso`] decides. A
    /// fingerprint match is inconclusive, so the certified test always runs.
    pub(super) fn find_vertex(
        &mut self,
        pair: &SupportTauTiltingPair,
    ) -> Result<Option<(usize, SupportPairIsoWitness)>, GraphError> {
        let summands = pair.module().len();
        let scale = scale_of(pair.module().module().dim_vector());
        self.ledger
            .charge(fingerprint_units(summands, self.quiver_vertices(), scale));
        let fingerprint = PairFingerprint::new(pair.module(), &pair.projective())?;
        let Some(bucket) = self.buckets.get(&fingerprint) else {
            return Ok(None);
        };
        let bucket = bucket.clone();
        for candidate in bucket {
            self.ledger.charge(iso_units(summands, scale));
            let vertex = &self.vertices[candidate];
            match pair_iso(
                pair.module(),
                &pair.projective(),
                vertex.pair.module(),
                &vertex.pair.projective(),
            )? {
                SupportPairIsoOutcome::Isomorphic(witness) => {
                    return Ok(Some((candidate, witness)));
                }
                SupportPairIsoOutcome::NotIsomorphic(_) => {}
            }
        }
        Ok(None)
    }
}
