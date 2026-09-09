/// The budget the mutation-graph route runs under when the oracle carries a
/// pair list to compare against.
///
/// A budget is a resource bound and never a claim. A walk that exhausts it
/// returns `Incomplete`, and the harness then claims no completeness either.
/// The ceiling clears the largest fixture that closes here, `inhomogeneous` at
/// 152 vertices, with room to spare.
///
/// This budget does not stop a tau-tilting infinite algebra in reasonable
/// time. The cost of failing grows steeply with the vertex ceiling, because
/// the modules on the preprojective ray grow without bound. The figures that
/// once stood here measured a work-unit rate this code no longer uses and are
/// not restated. So the harness walks the graph only where the oracle's
/// closure marker says GAP enumerated a pair list, and the Kronecker rejection
/// runs under the design's own 16-vertex ceiling in
/// [`kronecker_2_truncates_on_both_sides`].
pub(crate) fn graph_limits() -> MutationGraphLimits {
    MutationGraphLimits {
        max_vertices: 512,
        ..MutationGraphLimits::default()
    }
}

/// One of the `n` labels of a support tau-tilting pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Label {
    /// The isomorphism class of a module summand, as an id local to the
    /// fixture.
    Summand(usize),
    /// A vertex of the projective support.
    Projective(u32),
}

/// One enumerated pair: the schema's weak record, the module summands
/// themselves, and the pair's `n` labels.
pub(crate) struct OurPair {
    pub(crate) record: PairRecord,
    pub(crate) summands: Vec<Module>,
    pub(crate) labels: Vec<Label>,
}

/// Isomorphism-class ids for the module summands across one pair list.
///
/// Dimension vectors are the prefilter and `is_isomorphic` decides inside a
/// class of equal dimension vectors, so the ids are isomorphism classes and
/// not dimension vectors. That is what keeps `cyclic-nakayama-3-3-3` honest:
/// its three pairwise non-isomorphic projectives all have dimension vector
/// `[1, 1, 1]` and get three ids.
#[derive(Default)]
struct SummandIds {
    classes: Vec<Module>,
    by_dimvec: HashMap<Vec<usize>, Vec<usize>>,
}

impl SummandIds {
    fn id_of(&mut self, m: &Module) -> Result<usize, String> {
        let key = m.dim_vector().to_vec();
        for candidate in self.by_dimvec.get(&key).cloned().unwrap_or_default() {
            match is_isomorphic(m, &self.classes[candidate]) {
                Ok(IsoOutcome::Isomorphic(_)) => return Ok(candidate),
                Ok(IsoOutcome::NotIsomorphic(_)) => {}
                Ok(IsoOutcome::Unknown { reason }) => {
                    return Err(format!("summand identity undetermined: {reason}"));
                }
                Err(e) => return Err(format!("summand identity failed: {e}")),
            }
        }
        let id = self.classes.len();
        self.classes.push(m.clone());
        self.by_dimvec.entry(key).or_default().push(id);
        Ok(id)
    }
}

pub(crate) fn our_pairs<'a>(
    pairs: impl Iterator<Item = &'a SupportTauTiltingPair>,
) -> Result<Vec<OurPair>, String> {
    let mut ids = SummandIds::default();
    let mut out = Vec::new();
    for pair in pairs {
        let summands: Vec<Module> = pair
            .module()
            .summands()
            .iter()
            .map(|s| s.module().clone())
            .collect();
        let projective_support = pair.projective().vertices().to_vec();
        let mut labels = Vec::with_capacity(summands.len() + projective_support.len());
        for m in &summands {
            labels.push(Label::Summand(ids.id_of(m)?));
        }
        labels.extend(projective_support.iter().map(|&v| Label::Projective(v)));
        labels.sort_unstable();
        out.push(OurPair {
            record: PairRecord {
                module_dimvecs: pair.module().dim_vectors(),
                projective_support,
            },
            summands,
            labels,
        });
    }
    Ok(out)
}

/// Which route reached the library's pair list, or why none did.
///
/// The two routes are independent. `Catalog` is the definition alone over an
/// exhaustive classification, and `Graph` is the mutation-graph certificate;
/// neither restates the other.
pub(crate) enum OurStt {
    Catalog {
        provenance: CatalogProvenance,
        catalog_len: usize,
        pairs: Vec<OurPair>,
    },
    Graph {
        pairs: Vec<OurPair>,
    },
    /// The mutation graph exhausted its budget, so the list is not complete
    /// and nothing gated on completeness may be compared.
    Truncated {
        reason: String,
    },
    /// The oracle carries no pair list for this fixture, so none was built.
    /// The catalog constructors still ran, because their verdict is compared
    /// against the closure marker.
    NotRequested,
}

impl OurStt {
    pub(crate) fn pairs(&self) -> Option<&[OurPair]> {
        match self {
            OurStt::Catalog { pairs, .. } | OurStt::Graph { pairs } => Some(pairs),
            OurStt::Truncated { .. } | OurStt::NotRequested => None,
        }
    }

    pub(crate) fn route(&self) -> String {
        match self {
            OurStt::Catalog { provenance, .. } => format!("the {provenance} catalog"),
            OurStt::Graph { .. } => "the closed mutation graph".to_string(),
            OurStt::Truncated { reason } => format!("a truncated mutation graph ({reason})"),
            OurStt::NotRequested => "no enumeration".to_string(),
        }
    }
}

/// The library's support tau-tilting pairs, by the catalog route where an
/// exhaustive catalog exists and by the mutation graph otherwise.
///
/// `enumerate` is the oracle's closure marker. Where GAP enumerated no pair
/// list there is nothing to compare, and the mutation graph is not walked: on
/// a tau-tilting infinite algebra its truncation costs more the larger the
/// budget, so that case has its own test with its own ceiling.
pub(crate) fn our_support_tau_tilting(
    algebra: &Arc<Algebra>,
    enumerate: bool,
) -> Result<OurStt, String> {
    let catalog = IndecomposableCatalog::nakayama(algebra)
        .ok()
        .or_else(|| IndecomposableCatalog::dynkin(algebra).ok());
    if let Some(catalog) = catalog {
        let enumeration = enumerate_over_catalog(&catalog)
            .map_err(|e| format!("the catalog enumeration failed: {e}"))?;
        return Ok(OurStt::Catalog {
            provenance: catalog.provenance(),
            catalog_len: catalog.len(),
            pairs: our_pairs(enumeration.pairs().iter())?,
        });
    }
    if !enumerate {
        return Ok(OurStt::NotRequested);
    }
    match support_tau_tilting_graph(algebra, &graph_limits())
        .map_err(|e| format!("the mutation graph rejected the algebra: {e}"))?
    {
        SupportTauTiltingGraphOutcome::Closed(graph) => Ok(OurStt::Graph {
            pairs: our_pairs(graph.pairs())?,
        }),
        SupportTauTiltingGraphOutcome::Incomplete(graph) => Ok(OurStt::Truncated {
            reason: graph.reason().to_string(),
        }),
    }
}

/// The invariants of the minimal left `add(M/X)`-approximation of `X`.
///
/// Invariants only. No mutated pair is built from them: QPA realizes the
/// exchange only when the approximation is injective with a nonzero cokernel,
/// and the other branch gives the wrong partner half the time.
pub(crate) fn approximation_invariants(
    x: &Module,
    rest: &[Module],
) -> Result<ApproxInvariants, String> {
    let approximation = left_approximation(x, rest)
        .map_err(|e| format!("the minimal left approximation failed: {e}"))?;
    let f = approximation.map();
    let (kernel_module, _) = kernel(f);
    let (cokernel_module, _) = cokernel(f);
    let kernel_dimvec = kernel_module.dim_vector().to_vec();
    let source_dimvec = f.source().dim_vector().to_vec();
    Ok(ApproxInvariants {
        rank: source_dimvec.iter().sum::<usize>() - kernel_dimvec.iter().sum::<usize>(),
        target_dimvec: f.target().dim_vector().to_vec(),
        cokernel_dimvec: cokernel_module.dim_vector().to_vec(),
        source_dimvec,
        kernel_dimvec,
    })
}

/// The shape of the graph on the library's pairs, adjacent when they share
/// `n - 1` of their `n` labels.
///
/// This is a self-consistency check of the enumeration against itself, not
/// external truth: both sides compute it from a pair list they already have.
pub(crate) fn our_exchange_shape(pairs: &[OurPair], n: usize) -> ExchangeShape {
    let adjacency: Vec<Vec<usize>> = pairs
        .iter()
        .enumerate()
        .map(|(i, p)| {
            pairs
                .iter()
                .enumerate()
                .filter(|(j, q)| {
                    *j != i && p.labels.iter().filter(|l| q.labels.contains(l)).count() == n - 1
                })
                .map(|(j, _)| j)
                .collect()
        })
        .collect();
    let mut degree_histogram = vec![0; n + 2];
    for row in &adjacency {
        if let Some(slot) = degree_histogram.get_mut(row.len()) {
            *slot += 1;
        }
    }
    let mut seen = vec![false; pairs.len()];
    let mut queue: Vec<usize> = Vec::new();
    if !pairs.is_empty() {
        seen[0] = true;
        queue.push(0);
    }
    while let Some(i) = queue.pop() {
        for &j in &adjacency[i] {
            if !seen[j] {
                seen[j] = true;
                queue.push(j);
            }
        }
    }
    ExchangeShape {
        degree_histogram,
        edges: adjacency.iter().map(Vec::len).sum::<usize>() / 2,
        connected: seen.iter().all(|&s| s),
    }
}

/// A left-convention document stores values for left modules. Left modules
/// over `A` are right modules over `A^op`, so every value is computed over
/// the opposite algebra and compared index for index.
pub(crate) fn build_and_compute(fx: &Fixture, left: bool) -> Result<Computed, String> {
    let algebra = build_algebra(fx)?;
    let algebra = if left {
        opposite(&algebra)
            .map_err(|e| format!("cannot build the opposite algebra: {e}"))?
            .opposite()
            .clone()
    } else {
        algebra
    };
    compute(&algebra, fx.tau_period_bound)
}

type ComputedSlot = Arc<Mutex<Option<Result<Arc<Computed>, String>>>>;
type ComputedCache = Mutex<HashMap<String, ComputedSlot>>;

/// Fixtures repeat across tests and corrupted documents keep their
/// presentations, so results are cached by field, presentation, side, and the
/// tau-orbit search bound. That bound is the one recorded value that changes
/// what the library computes.
///
/// Tests run in parallel, so each key gets its own lock and is computed once.
/// A plain read-then-insert cache would let every thread that starts before
/// the first result lands recompute the same fixture.
pub(crate) fn computed_for(fx: &Fixture, left: bool) -> Result<Arc<Computed>, String> {
    static CACHE: OnceLock<ComputedCache> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let key = format!(
        "{left}|{}|{}|{:?}|{:?}",
        fx.field, fx.tau_period_bound, fx.quiver, fx.relations
    );
    let slot = cache.lock().unwrap().entry(key).or_default().clone();
    let mut entry = slot.lock().unwrap();
    if let Some(hit) = entry.as_ref() {
        return hit.clone();
    }
    let result = build_and_compute(fx, left).map(Arc::new);
    *entry = Some(result.clone());
    result
}

/// The library's whole v8 layer for one fixture.
pub(crate) struct OurSupportTauTilting {
    /// `is_tau_rigid` over the designated modules. An independent route to the
    /// v6 `tau_rigid` list, which the reader already pins to the v8 copy.
    pub(crate) tau_rigid_designated: Vec<bool>,
    pub(crate) enumeration: OurStt,
}

pub(crate) fn build_stt(fx: &Fixture, enumerate: bool) -> Result<OurSupportTauTilting, String> {
    let algebra = build_algebra(fx)?;
    let mut tau_rigid_designated = Vec::new();
    for (r, m) in designated_refs(algebra.quiver().num_vertices() as usize)
        .iter()
        .zip(designated_modules(&algebra))
    {
        match is_tau_rigid(&m) {
            Ok(TauRigidityOutcome::TauRigid(_)) => tau_rigid_designated.push(true),
            Ok(TauRigidityOutcome::NotTauRigid(_)) => tau_rigid_designated.push(false),
            Err(e) => return Err(format!("{}: tau-rigidity failed: {e}", r.label())),
        }
    }
    Ok(OurSupportTauTilting {
        enumeration: our_support_tau_tilting(&algebra, enumerate)?,
        tau_rigid_designated,
    })
}

type SttSlot = Arc<Mutex<Option<Result<Arc<OurSupportTauTilting>, String>>>>;

/// The v8 layer, cached by presentation exactly as [`computed_for`] caches the
/// v6 layer. Corrupted documents keep their presentations, so the enumeration
/// runs once per algebra across the whole binary.
pub(crate) fn stt_for(fx: &Fixture, enumerate: bool) -> Result<Arc<OurSupportTauTilting>, String> {
    static CACHE: OnceLock<Mutex<HashMap<String, SttSlot>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let key = format!(
        "{enumerate}|{}|{:?}|{:?}",
        fx.field, fx.quiver, fx.relations
    );
    let slot = cache.lock().unwrap().entry(key).or_default().clone();
    let mut entry = slot.lock().unwrap();
    if let Some(hit) = entry.as_ref() {
        return hit.clone();
    }
    let result = build_stt(fx, enumerate).map(Arc::new);
    *entry = Some(result.clone());
    result
}

/// How much of the v8 block one pass compares.
///
/// `Shape` is the closure marker, tau-rigidity, the pair list, the histogram
/// and the exchange graph shape, all of which read a pair list the fixture's
/// cache already holds. `Slots` adds the per-slot layer, one minimal left
/// approximation per sampled slot. That layer is recomputed on every call, so
/// the two oracle tests run at `Slots` and the corruption tests, which run the
/// comparison dozens of times, run at `Shape`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum SttDepth {
    Shape,
    Slots,
}

/// The first index where two lists differ, for a readable message on a long
/// list.
pub(crate) fn first_difference<T: PartialEq>(theirs: &[T], ours: &[T]) -> Option<usize> {
    (0..theirs.len().max(ours.len())).find(|&i| theirs.get(i) != ours.get(i))
}
