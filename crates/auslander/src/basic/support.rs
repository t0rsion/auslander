use std::sync::Arc;

use crate::algebra::Algebra;
use crate::context::VerificationContext;
use crate::decompose::{inverse_morphism, mutually_inverse};
use crate::hom::{HomError, Morphism, hom_dim};
use crate::indec::IndecomposableModule;
use crate::iso::indecomposable_iso;
use crate::module::{Module, summand_sum};
use crate::profile::{Site, hit};
use crate::radical::{loewy_length, socle, top};

use super::decomposition::{BasicDecomposition, BasicError, defect_non_invertible};

/// The vertex set of a basic projective module, sorted and deduplicated.
///
/// Over a basic algebra `P = P_{v_1} + ... + P_{v_k}` with distinct vertices,
/// so the vertex set determines `P` up to isomorphism. Identity of the
/// projective half is therefore exact set equality of the vertex lists, which
/// is what [`PartialEq`] compares. The algebra is not part of that
/// comparison; [`ProjectiveSupport::is_compatible`] checks it separately.
pub struct ProjectiveSupport {
    algebra: Arc<Algebra>,
    vertices: Vec<u32>,
}

debug_fields!(ProjectiveSupport |this| {
    "vertices" => this.vertices;
});

/// Equality is exact set equality of the vertex lists, which are sorted and
/// deduplicated at construction. It ignores the algebra.
impl PartialEq for ProjectiveSupport {
    fn eq(&self, other: &ProjectiveSupport) -> bool {
        self.vertices == other.vertices
    }
}

impl Eq for ProjectiveSupport {}

impl ProjectiveSupport {
    /// Builds the support from a vertex list, sorting it and removing
    /// duplicates.
    ///
    /// A vertex outside `0..algebra.quiver().num_vertices()` is
    /// [`BasicError::VertexOutOfRange`]. An empty list is the zero projective.
    pub fn new(algebra: &Arc<Algebra>, vertices: &[u32]) -> Result<ProjectiveSupport, BasicError> {
        let num_vertices = algebra.quiver().num_vertices();
        for &vertex in vertices {
            if vertex >= num_vertices {
                return Err(BasicError::VertexOutOfRange {
                    vertex,
                    num_vertices,
                });
            }
        }
        let mut sorted = vertices.to_vec();
        sorted.sort_unstable();
        sorted.dedup();
        Ok(ProjectiveSupport {
            algebra: algebra.clone(),
            vertices: sorted,
        })
    }

    accessor_methods! {
        /// The algebra the projectives come from.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The support vertices, sorted and deduplicated.
        pub vertices() -> &[u32] = |this| &this.vertices;
        /// The number of support vertices, which is the number of indecomposable
        /// summands of the projective.
        pub len() -> usize = |this| this.vertices.len();
        /// Whether the support is empty, which means the projective is zero.
        pub is_empty() -> bool = |this| this.vertices.is_empty();
        /// Whether `v` lies in the support.
        pub contains(v: u32) -> bool = |this| this.vertices.binary_search(&v).is_ok();
        /// Whether both supports come from one algebra value (the same [`Arc`]).
        pub is_compatible(other: &ProjectiveSupport) -> bool = |this|
            Arc::ptr_eq(&this.algebra, &other.algebra);
        /// Rebuilds the canonical module `P_{v_1} + ... + P_{v_k}` in sorted
        /// vertex order; the zero module when the support is empty.
        ///
        /// Each call builds a fresh [`Module`] value, so results of two calls are
        /// isomorphic but never [`Module::ptr_eq`].
        pub module() -> Module = |this|
            summand_sum(&this.algebra, &this.vertices, Module::projective);
    }
}

/// A proof that two basic pairs are not isomorphic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SupportPairObstruction {
    /// The projective supports differ as sets, so the projective halves are
    /// not isomorphic.
    ProjectiveSupport {
        /// Support of the first pair.
        first: Vec<u32>,
        /// Support of the second pair.
        second: Vec<u32>,
    },
    /// The module halves have different summand counts, so by Krull-Schmidt
    /// they are not isomorphic.
    SummandCount {
        /// Summand count of the first module.
        first: usize,
        /// Summand count of the second module.
        second: usize,
    },
    /// Summand `index` of the first module is isomorphic to no summand of the
    /// second; by Krull-Schmidt the modules differ.
    UnmatchedSummand {
        /// Position of the unmatched summand in the first decomposition.
        index: usize,
        /// Dimension vector of the unmatched summand.
        dim_vector: Vec<usize>,
    },
}

/// A verified isomorphism of two basic pairs.
///
/// Construction goes through [`pair_iso`]. The witness holds the summand
/// bijection and, for every summand of the first module, the isomorphism to
/// its partner and the isomorphism back.
#[derive(Clone)]
pub struct SupportPairIsoWitness {
    pub(super) bijection: Vec<usize>,
    pub(super) forward: Vec<Morphism>,
    pub(super) backward: Vec<Morphism>,
}

debug_fields!(SupportPairIsoWitness |this| {
    "bijection" => this.bijection;
});

impl SupportPairIsoWitness {
    accessor_methods! {
        /// `bijection()[i]` is the summand of the second module matched to
        /// summand `i` of the first.
        pub bijection() -> &[usize] = |this| &this.bijection;
        /// `forward()[i]` runs from summand `i` of the first module to summand
        /// `bijection()[i]` of the second.
        pub forward() -> &[Morphism] = |this| &this.forward;
        /// `backward()[i]` is the inverse of `forward()[i]`.
        pub backward() -> &[Morphism] = |this| &this.backward;
    }

    /// Rechecks the witness: the bijection is a permutation, and each pair of
    /// stored maps multiplies to the identity in both orders.
    pub fn verify(&self) -> bool {
        hit(Site::SupportPairIsoWitnessVerify);
        verify_guard!(
            self.forward.len() == self.bijection.len()
                && self.backward.len() == self.bijection.len()
        );
        let mut seen = vec![false; self.bijection.len()];
        for &j in &self.bijection {
            verify_guard!(j < seen.len() && !seen[j]);
            seen[j] = true;
        }
        for (f, g) in self.forward.iter().zip(&self.backward) {
            verify_guard!(mutually_inverse(f, g));
        }
        true
    }
}

/// The outcome of [`pair_iso`].
///
/// There is no undecided variant. Both inputs are certified basic pairs, and
/// the radical criterion between certified indecomposables is total.
#[derive(Clone, Debug)]
pub enum SupportPairIsoOutcome {
    /// The pairs are isomorphic, with a verified witness.
    Isomorphic(SupportPairIsoWitness),
    /// A proof that the pairs are not isomorphic.
    NotIsomorphic(SupportPairObstruction),
}

/// Whether the basic pairs `(a_mod, a_proj)` and `(b_mod, b_proj)` are
/// isomorphic.
///
/// The projective halves are compared as vertex sets. The module halves are
/// compared summand by summand with the radical criterion, which is exact
/// between certified indecomposables. Both modules are basic, so each summand
/// of the first is isomorphic to at most one summand of the second and the
/// greedy scan is exact.
///
/// Errors when the four inputs do not share one algebra value, and with
/// [`BasicError::Defect`] when the radical criterion returns a map that is
/// not invertible.
pub fn pair_iso(
    a_mod: &BasicDecomposition,
    a_proj: &ProjectiveSupport,
    b_mod: &BasicDecomposition,
    b_proj: &ProjectiveSupport,
) -> Result<SupportPairIsoOutcome, BasicError> {
    hit(Site::PairIso);
    if !a_proj.is_compatible(b_proj)
        || !Arc::ptr_eq(a_mod.module().algebra(), a_proj.algebra())
        || !Arc::ptr_eq(b_mod.module().algebra(), b_proj.algebra())
    {
        return Err(BasicError::DifferentAlgebras);
    }
    if a_proj.vertices() != b_proj.vertices() {
        return Ok(SupportPairIsoOutcome::NotIsomorphic(
            SupportPairObstruction::ProjectiveSupport {
                first: a_proj.vertices().to_vec(),
                second: b_proj.vertices().to_vec(),
            },
        ));
    }
    if a_mod.len() != b_mod.len() {
        return Ok(SupportPairIsoOutcome::NotIsomorphic(
            SupportPairObstruction::SummandCount {
                first: a_mod.len(),
                second: b_mod.len(),
            },
        ));
    }
    let mut bijection = Vec::with_capacity(a_mod.len());
    let mut forward = Vec::with_capacity(a_mod.len());
    let mut backward = Vec::with_capacity(a_mod.len());
    let mut used = vec![false; b_mod.len()];
    for (i, x) in a_mod.summands().iter().enumerate() {
        let Some(matched) = certified_match(
            x,
            b_mod
                .summands()
                .iter()
                .enumerate()
                .filter(|(j, _)| !used[*j]),
        )?
        else {
            return Ok(SupportPairIsoOutcome::NotIsomorphic(
                SupportPairObstruction::UnmatchedSummand {
                    index: i,
                    dim_vector: x.module().dim_vector().to_vec(),
                },
            ));
        };
        used[matched.target_index] = true;
        bijection.push(matched.target_index);
        forward.push(matched.forward);
        backward.push(matched.backward);
    }
    Ok(SupportPairIsoOutcome::Isomorphic(SupportPairIsoWitness {
        bijection,
        forward,
        backward,
    }))
}

/// Isomorphism invariants of one indecomposable summand, used as part of a
/// [`PairFingerprint`].
///
/// Every field is an isomorphism invariant, so isomorphic summands agree in
/// all of them. The converse fails: see [`PairFingerprint`].
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SummandFingerprint {
    dim_vector: Vec<usize>,
    loewy_length: usize,
    top_dim_vector: Vec<usize>,
    socle_dim_vector: Vec<usize>,
    end_dim: usize,
    residue_degree: usize,
    hom_from_simples: Vec<usize>,
    hom_to_simples: Vec<usize>,
}

impl SummandFingerprint {
    accessor_methods! {
        /// The dimension vector.
        pub dim_vector() -> &[usize] = |this| &this.dim_vector;
        /// The Loewy length, from [`loewy_length`].
        pub loewy_length() -> usize = |this| this.loewy_length;
        /// The dimension vector of `top X`.
        pub top_dim_vector() -> &[usize] = |this| &this.top_dim_vector;
        /// The dimension vector of `soc X`.
        pub socle_dim_vector() -> &[usize] = |this| &this.socle_dim_vector;
        /// `dim_Fp End(X)`.
        pub end_dim() -> usize = |this| this.end_dim;
        /// The residue degree of `End(X)`, from
        /// [`IndecomposableModule::residue_degree`].
        pub residue_degree() -> usize = |this| this.residue_degree;
        /// `hom_dim(S_v, X)` for every vertex `v`, in vertex order.
        pub hom_from_simples() -> &[usize] = |this| &this.hom_from_simples;
        /// `hom_dim(X, S_v)` for every vertex `v`, in vertex order.
        pub hom_to_simples() -> &[usize] = |this| &this.hom_to_simples;
    }
}

/// A cheap sound prefilter for pair identity.
///
/// The fingerprint holds the projective support and, per module summand, a
/// [`SummandFingerprint`]; the summand list is sorted, so it does not depend
/// on decomposition order. Isomorphic pairs have equal fingerprints, so
/// unequal fingerprints prove the pairs different.
///
/// A fingerprint match is inconclusive and the certified test [`pair_iso`] is
/// mandatory. Dimension vectors are isomorphism invariants but not complete
/// identifiers: over `kronecker(2)` the three modules of dimension vector
/// `[1, 1]` given by the arrow pairs `(1, 0)`, `(0, 1)`, and `(1, 1)` are
/// pairwise non-isomorphic and share every field of this fingerprint.
///
/// The Hom-dimension profile runs against a fixed anchor family, the simple
/// modules in vertex order. Nothing here profiles against previously found
/// pairs, so a fingerprint depends on the pair alone and never on the order
/// in which pairs were discovered.
///
/// [`PartialEq`], [`Eq`], and [`Hash`] let a caller bucket pairs by
/// fingerprint before running [`pair_iso`] inside a bucket.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PairFingerprint {
    projective_support: Vec<u32>,
    summands: Vec<SummandFingerprint>,
}

impl PairFingerprint {
    /// Computes the fingerprint of the pair `(module, projective)`.
    ///
    /// Errors when the two parts do not share one algebra value.
    pub fn new(
        module: &BasicDecomposition,
        projective: &ProjectiveSupport,
    ) -> Result<PairFingerprint, BasicError> {
        Self::new_with_hom(module, projective, hom_dim)
    }

    pub(crate) fn new_with_context(
        module: &BasicDecomposition,
        projective: &ProjectiveSupport,
        context: &VerificationContext,
    ) -> Result<PairFingerprint, BasicError> {
        Self::new_with_hom(module, projective, |source, target| {
            context.hom_dim_for(source, target)
        })
    }

    fn new_with_hom(
        module: &BasicDecomposition,
        projective: &ProjectiveSupport,
        hom: impl Fn(&Module, &Module) -> Result<usize, HomError>,
    ) -> Result<PairFingerprint, BasicError> {
        hit(Site::PairFingerprintNew);
        let algebra = module.module().algebra();
        if !Arc::ptr_eq(algebra, projective.algebra()) {
            return Err(BasicError::DifferentAlgebras);
        }
        let simples: Vec<Module> = (0..algebra.quiver().num_vertices())
            .map(|v| Module::simple(algebra, v))
            .collect();
        let mut summands = Vec::with_capacity(module.len());
        for x in module.summands() {
            let m = x.module();
            let (top_module, _) = top(m);
            let (socle_module, _) = socle(m);
            let mut hom_from_simples = Vec::with_capacity(simples.len());
            let mut hom_to_simples = Vec::with_capacity(simples.len());
            for simple in &simples {
                hom_from_simples.push(hom(simple, m)?);
                hom_to_simples.push(hom(m, simple)?);
            }
            summands.push(SummandFingerprint {
                dim_vector: m.dim_vector().to_vec(),
                loewy_length: loewy_length(m),
                top_dim_vector: top_module.dim_vector().to_vec(),
                socle_dim_vector: socle_module.dim_vector().to_vec(),
                end_dim: x.endo().dim(),
                residue_degree: x.residue_degree(),
                hom_from_simples,
                hom_to_simples,
            });
        }
        summands.sort();
        Ok(PairFingerprint {
            projective_support: projective.vertices().to_vec(),
            summands,
        })
    }

    accessor_methods! {
        /// The projective support the fingerprint was keyed on.
        pub projective_support() -> &[u32] = |this| &this.projective_support;
        /// The per-summand records, sorted.
        pub summands() -> &[SummandFingerprint] = |this| &this.summands;
    }
}

/// Fingerprints items, then certifies every fingerprint collision.
pub(crate) fn pairwise_distinct_by<T, F>(
    items: &[T],
    mut fingerprint: impl FnMut(&T) -> Option<F>,
    mut distinct: impl FnMut(&T, &T) -> bool,
) -> bool
where
    F: PartialEq,
{
    let_or_false!(
        Some(fingerprints) = items
            .iter()
            .map(&mut fingerprint)
            .collect::<Option<Vec<F>>>()
    );
    (0..items.len()).all(|i| {
        (i + 1..items.len())
            .all(|j| fingerprints[i] != fingerprints[j] || distinct(&items[i], &items[j]))
    })
}

/// One summand of a module together with the summand of `T` it matches.
#[derive(Clone)]
pub struct AddMatch {
    pub(super) target_index: usize,
    pub(super) forward: Morphism,
    pub(super) backward: Morphism,
}

debug_fields!(AddMatch |this| {
    "target_index" => this.target_index;
});

impl AddMatch {
    accessor_methods! {
        /// Index of the matched summand of `T`.
        pub target_index() -> usize = |this| this.target_index;
        /// The isomorphism from the module summand to the summand of `T`.
        pub forward() -> &Morphism = |this| &this.forward;
        /// The inverse of [`AddMatch::forward`].
        pub backward() -> &Morphism = |this| &this.backward;
    }
}

/// The first certified match for `x`, with its checked inverse.
pub(super) fn certified_match<'a>(
    x: &IndecomposableModule,
    candidates: impl IntoIterator<Item = (usize, &'a IndecomposableModule)>,
) -> Result<Option<AddMatch>, BasicError> {
    for (target_index, y) in candidates {
        if let Some(forward) = indecomposable_iso(x.module(), y.module(), x.endo()) {
            let backward = inverse_morphism(&forward).ok_or_else(defect_non_invertible)?;
            return Ok(Some(AddMatch {
                target_index,
                forward,
                backward,
            }));
        }
    }
    Ok(None)
}
