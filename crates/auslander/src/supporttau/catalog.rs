use std::sync::Arc;

use crate::algebra::Algebra;
use crate::arquiver::{CatalogProvenance, IndecomposableCatalog};
use crate::basic::{
    BasicDecomposition, PairFingerprint, ProjectiveSupport, SupportPairIsoOutcome, pair_iso,
    pairwise_distinct_by,
};
use crate::hom::hom_dim;
use crate::taurigid::TauCache;

use super::errors::SupportTauError;
use super::pair::{SupportTauTiltingClassification, SupportTauTiltingPair};

/// The state of one [`enumerate_over_catalog`] run.
struct CatalogWalk<'a> {
    catalog: &'a IndecomposableCatalog,
    algebra: Arc<Algebra>,
    vertices: usize,
    // tau_hom[i][j] = dim Hom(X_i, tau X_j), and 0 when tau X_j is zero.
    tau_hom: Vec<Vec<usize>>,
    cache: TauCache,
    pairs: Vec<SupportTauTiltingPair>,
    nodes: usize,
}

impl CatalogWalk<'_> {
    /// Whether `chosen + [i]` is still tau-rigid, given that `chosen` is.
    ///
    /// Only the pairs involving `i` are new, so the test is incremental.
    fn extends_tau_rigid(&self, chosen: &[usize], i: usize) -> bool {
        self.tau_hom[i][i] == 0
            && chosen
                .iter()
                .all(|&j| self.tau_hom[i][j] == 0 && self.tau_hom[j][i] == 0)
    }

    fn walk(&mut self, chosen: &mut Vec<usize>, start: usize) -> Result<(), SupportTauError> {
        self.emit(chosen)?;
        // |M| + |P| = n with |P| >= 0 bounds |M| by n, so a longer subset can
        // never be the module part of a pair. The bound is checked on the
        // count, before any module is assembled.
        if chosen.len() == self.vertices {
            return Ok(());
        }
        for i in start..self.catalog.len() {
            if self.extends_tau_rigid(chosen, i) {
                chosen.push(i);
                self.nodes += 1;
                self.walk(chosen, i + 1)?;
                chosen.pop();
            }
        }
        Ok(())
    }

    /// Builds the pair whose module part is the subset `chosen`, when there is
    /// one.
    ///
    /// The subset admits a pair exactly when `|M|` equals the number of
    /// vertices where `M` is nonzero, and then the support of `P` is the
    /// complement of that set. So one subset yields at most one pair, and the
    /// test is a count.
    fn emit(&mut self, chosen: &[usize]) -> Result<(), SupportTauError> {
        let support: Vec<u32> = (0..self.vertices as u32)
            .filter(|&v| self.vanishes_at(chosen, v))
            .collect();
        if support.len() + chosen.len() != self.vertices {
            return Ok(());
        }
        // The catalog lists one entry per isomorphism class, so a subset of it
        // is already a certified basic decomposition. Reassembling and running
        // Krull-Schmidt would rediscover exactly what `chosen` names.
        let module = BasicDecomposition::from_catalog(self.catalog, chosen)?;
        let indices = chosen.to_vec();
        let projective = ProjectiveSupport::new(&self.algebra, &support)?;
        let classification = SupportTauTiltingPair::classify_with_cache(
            module,
            projective,
            &indices,
            Some(&mut self.cache),
        )?;
        match classification {
            SupportTauTiltingClassification::Pair(pair) => {
                self.pairs.push(pair);
                Ok(())
            }
            SupportTauTiltingClassification::Rejected(rejection) => Err(SupportTauError::Defect {
                reason: format!(
                    "the tables admitted the subset {chosen:?} with support {support:?} and the \
                     certified route rejected it: {rejection}"
                ),
            }),
        }
    }

    /// Whether every entry of `chosen` has dimension zero at `vertex`, which
    /// is `Hom(P_vertex, M) = 0` by the identification on `support_complement`.
    fn vanishes_at(&self, chosen: &[usize], vertex: u32) -> bool {
        chosen
            .iter()
            .all(|&i| self.catalog.entries()[i].module().dim_vector()[vertex as usize] == 0)
    }
}

/// Every support tau-tilting pair of one algebra, listed from the definition
/// over an exhaustive catalog.
///
/// Completeness comes from the catalog's classification theorem, and from
/// nothing else. An [`IndecomposableCatalog`] holds every indecomposable of
/// its algebra up to isomorphism, by one of the classifications named by
/// [`CatalogProvenance`]. The module part of a basic pair is a direct sum of
/// pairwise non-isomorphic indecomposables, so it is the sum of a subset of
/// the catalog, and walking the subsets reaches every pair.
///
/// The limit is the same theorem. Only algebras with a catalog can be
/// enumerated this way, so [`enumerate_over_catalog`] takes a catalog rather
/// than an algebra, and there is no route from an arbitrary algebra to a
/// value of this type. The Kronecker algebra is tau-tilting infinite and has
/// no exhaustive catalog, so every catalog constructor rejects it and no
/// enumeration is attempted.
///
/// This route is independent of the mutation-graph certificate. It uses no
/// mutation, no approximation, and no theorem about the support tau-tilting
/// quiver: only `Hom`, `tau`, and the four conditions of
/// [`SupportTauTiltingPair`]. When the two routes produce the same list, that
/// is evidence, not a restatement of one route by the other.
pub struct CatalogEnumeration {
    algebra: Arc<Algebra>,
    provenance: CatalogProvenance,
    catalog_len: usize,
    pub(super) pairs: Vec<SupportTauTiltingPair>,
    nodes_visited: usize,
}

debug_fields!(CatalogEnumeration |this| {
    "provenance" => this.provenance;
    "catalog_len" => this.catalog_len;
    "pairs" => this.pairs.len();
    "nodes_visited" => this.nodes_visited;
});

impl CatalogEnumeration {
    accessor_methods! {
        /// The algebra the pairs live over.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The classification theorem the completeness of the list rests on.
        pub provenance() -> CatalogProvenance = |this| this.provenance;
        /// The number of catalog entries the walk ran over.
        pub catalog_len() -> usize = |this| this.catalog_len;
        /// The pairs, in walk order: module subsets in lexicographic order over
        /// catalog positions, one pair per subset that admits one.
        pub pairs() -> &[SupportTauTiltingPair] = |this| &this.pairs;
        /// The number of pairs.
        pub len() -> usize = |this| this.pairs.len();
        /// Whether the list is empty. It never is: `(A, 0)` is a pair over every
        /// algebra.
        pub is_empty() -> bool = |this| this.pairs.is_empty();
        /// The number of subsets the depth-first search visited, counting the
        /// empty subset.
        ///
        /// Tau-rigidity is inherited by subsets, so the walk visits exactly the
        /// tau-rigid subsets of at most `n` entries and tests each remaining entry
        /// once per visit. The count is deterministic and profile-independent, so
        /// a test can assert it.
        pub nodes_visited() -> usize = |this| this.nodes_visited;
    }

    /// Pair counts by `|M|`, indexed from zero to the number of vertices.
    pub fn histogram(&self) -> Vec<usize> {
        let vertices = self.algebra.quiver().num_vertices() as usize;
        let mut out = vec![0; vertices + 1];
        for pair in &self.pairs {
            out[pair.module().len()] += 1;
        }
        out
    }

    /// Rechecks every pair, and that the pairs are pairwise non-isomorphic.
    ///
    /// Each pair goes through [`SupportTauTiltingPair::verify`]. Distinctness
    /// runs [`PairFingerprint`] as a prefilter and [`pair_iso`] inside a
    /// bucket, so a duplicated entry fails even when the two copies were
    /// built separately.
    ///
    /// This rechecks the list. It does not recheck completeness, which is the
    /// catalog's classification theorem and is not a computation.
    pub fn verify(&self) -> bool {
        pairwise_distinct_by(
            &self.pairs,
            |pair| {
                (Arc::ptr_eq(pair.module().module().algebra(), &self.algebra) && pair.verify())
                    .then(|| PairFingerprint::new(pair.module(), &pair.projective()).ok())
                    .flatten()
            },
            |left, right| {
                matches!(
                    pair_iso(
                        left.module(),
                        &left.projective(),
                        right.module(),
                        &right.projective(),
                    ),
                    Ok(SupportPairIsoOutcome::NotIsomorphic(_))
                )
            },
        )
    }
}

/// Lists every support tau-tilting pair of the catalog's algebra, from the
/// definition alone.
///
/// The algorithm is the one `docs/support-tau-tilting.md` section 10 fixes:
///
/// 1. Compute `tau X_i` once per catalog entry, through one [`TauCache`].
/// 2. Build the table `hom_dim(X_i, tau X_j)`.
/// 3. Walk the subsets depth first, extending only sets that stay tau-rigid.
/// 4. Keep the subsets whose support complement has exactly `n - |M|`
///    vertices, which is the whole projective condition.
///
/// The subset walk reads the table and the dimension vectors, so no linear
/// algebra runs inside it. `Hom(P_v, X) = X_v`, so the second table the
/// design calls for is the dimension vectors themselves. The count bound
/// `|M| <= n` cuts a branch before any module is assembled.
///
/// Every kept candidate still goes through
/// [`SupportTauTiltingPair::classify_with_cache`], so each listed pair carries
/// the same witnesses as one built by hand. A candidate the tables admit and
/// the certified route rejects is a [`SupportTauError::Defect`].
///
/// Completeness is the catalog's, and only the catalog's: see
/// [`CatalogEnumeration`].
///
/// # Errors
/// The wrapped errors of the basic, Hom, and tau layers when a check could not
/// be run, and [`SupportTauError::Defect`] when the tables and the certified
/// route disagree.
pub fn enumerate_over_catalog(
    catalog: &IndecomposableCatalog,
) -> Result<CatalogEnumeration, SupportTauError> {
    let algebra = catalog.algebra().clone();
    let vertices = algebra.quiver().num_vertices() as usize;
    let mut cache = TauCache::new();
    let mut translates = Vec::with_capacity(catalog.len());
    for entry in catalog.entries() {
        translates.push(cache.tau_of(entry.module())?.clone());
    }
    let mut tau_hom = vec![vec![0usize; catalog.len()]; catalog.len()];
    for (i, x) in catalog.entries().iter().enumerate() {
        for (j, translate) in translates.iter().enumerate() {
            // Hom(X_i, 0) is zero, so a projective X_j needs no Hom system.
            if !translate.is_zero() {
                tau_hom[i][j] = hom_dim(x.module(), translate)?;
            }
        }
    }
    let mut walk = CatalogWalk {
        catalog,
        algebra: algebra.clone(),
        vertices,
        tau_hom,
        cache,
        pairs: Vec::new(),
        nodes: 1,
    };
    walk.walk(&mut Vec::with_capacity(vertices), 0)?;
    Ok(CatalogEnumeration {
        algebra,
        provenance: catalog.provenance(),
        catalog_len: catalog.len(),
        pairs: walk.pairs,
        nodes_visited: walk.nodes,
    })
}

/// Lists every support tau-tilting pair when one complete catalog applies.
///
/// Catalog selection tries Dynkin, Nakayama, and gentle tree in that order.
/// The selected classification supplies the completeness proof used by
/// [`enumerate_over_catalog`].
pub fn enumerate_over_algebra(
    algebra: &Arc<Algebra>,
) -> Result<CatalogEnumeration, SupportTauError> {
    let catalog = IndecomposableCatalog::complete(algebra)?;
    enumerate_over_catalog(&catalog)
}
