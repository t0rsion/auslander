//! Basic decompositions, projective support, and exact identity for basic
//! pairs.
//!
//! A pair is `(M, P)` with `P` projective. Both parts are basic: their
//! indecomposable summands are pairwise non-isomorphic.
//!
//! The module part is a [`BasicDecomposition`]. [`BasicDecomposition::new`]
//! runs [`krull_schmidt`], certifies every summand through
//! [`IndecomposableModule`], and rejects a repeated summand with
//! [`BasicError::NotBasic`]. An undetermined summand is
//! [`BasicError::CertificationBlocked`], never a silent distinct value.
//!
//! Three constructors skip that work where a theorem already gives the
//! answer: [`BasicDecomposition::without`] drops a summand,
//! [`BasicDecomposition::with_new_summand`] appends a certified one, and
//! [`BasicDecomposition::from_catalog`] takes distinct catalog entries. Each
//! keeps the summand values it was given, which is what a
//! [`crate::taurigid::TauCache`] keyed by module identity needs.
//!
//! The projective part is a [`ProjectiveSupport`]. Over a basic algebra a
//! basic projective is determined by a vertex subset, so the type stores
//! sorted deduplicated vertices and rebuilds the canonical sum of `P_v` on
//! demand. Identity of the projective half is exact set equality.
//!
//! [`pair_iso`] decides identity of two pairs. It has no undecided outcome:
//! both inputs are certified basic pairs, and between certified
//! indecomposables the radical criterion either produces an isomorphism or
//! proves every composite lies in the radical. An undecided comparison is a
//! crate defect, reported as [`BasicError::Defect`].
//!
//! [`PairFingerprint`] is a cheap sound prefilter. Equal pairs have equal
//! fingerprints; equal fingerprints prove nothing, so the certified test
//! stays mandatory.

use std::fmt;
use std::sync::Arc;

use crate::algebra::Algebra;
use crate::arquiver::IndecomposableCatalog;
use crate::decompose::{
    Certificate, KrullSchmidtOutcome, decompose, krull_schmidt, matrix_inverse,
};
use crate::endo::EndoAlgebra;
use crate::hom::{HomError, Morphism, hom_dim, identity};
use crate::indec::{IndecError, IndecomposableModule};
use crate::iso::indecomposable_iso;
use crate::module::{Module, direct_sum};
use crate::radical::{loewy_length, socle, top};

/// Rejected input, a blocked certification, or a failed internal cross-check
/// of the basic layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BasicError {
    /// A summand could not be certified indecomposable, so nothing is claimed
    /// about the decomposition. The sources are
    /// [`KrullSchmidtOutcome::Unknown`], [`IndecError::Undetermined`], and an
    /// undecided isomorphism test. This is not budget exhaustion.
    CertificationBlocked {
        /// Why certification failed.
        reason: String,
    },
    /// Summands `first` and `second` are isomorphic, so the module is not
    /// basic. The indices count summands in [`BasicDecomposition`] order.
    NotBasic {
        /// Index of the first summand of the isomorphic pair.
        first: usize,
        /// Index of the second summand of the isomorphic pair.
        second: usize,
    },
    /// A support vertex is not a vertex of the algebra's quiver.
    VertexOutOfRange {
        /// The rejected vertex.
        vertex: u32,
        /// The quiver's vertex count.
        num_vertices: u32,
    },
    /// Two inputs do not share one algebra value (the same [`Arc`]).
    DifferentAlgebras,
    /// A morphism operation rejected its input.
    Hom(HomError),
    /// A failed internal cross-check: a theorem's hypotheses hold and the
    /// consequence the code checked did not.
    Defect {
        /// What contradicted the theorem.
        reason: String,
    },
}

impl fmt::Display for BasicError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CertificationBlocked { reason } => {
                write!(f, "certification blocked: {reason}")
            }
            Self::NotBasic { first, second } => write!(
                f,
                "summands {first} and {second} are isomorphic, so the module is not basic"
            ),
            Self::VertexOutOfRange {
                vertex,
                num_vertices,
            } => write!(
                f,
                "vertex {vertex} is out of range, the quiver has {num_vertices} vertices"
            ),
            Self::DifferentAlgebras => f.write_str("the inputs do not share one algebra"),
            Self::Hom(error) => write!(f, "morphism rejected: {error}"),
            Self::Defect { reason } => write!(f, "internal cross-check failed: {reason}"),
        }
    }
}

impl std::error::Error for BasicError {}

impl From<HomError> for BasicError {
    fn from(error: HomError) -> BasicError {
        BasicError::Hom(error)
    }
}

/// Certifies one summand of a decomposition that already carries an
/// indecomposability certificate. Anything but [`IndecError::Undetermined`]
/// contradicts that certificate, so it is a defect.
///
/// `endo` is the `End` the decomposition already built for that summand, so
/// the gate costs no second radical computation.
fn certified(endo: EndoAlgebra) -> Result<IndecomposableModule, BasicError> {
    IndecomposableModule::from_endo(endo).map_err(|error| match error {
        IndecError::Undetermined { attempts } => BasicError::CertificationBlocked {
            reason: format!("a summand stayed undetermined after {attempts} split attempts"),
        },
        other => BasicError::Defect {
            reason: format!("a certified summand failed the indecomposability gate: {other}"),
        },
    })
}

/// The inverse of an isomorphism, or `None` when a vertex matrix is singular.
fn inverse_of(f: &Morphism) -> Option<Morphism> {
    let field = f.source().field();
    let mut maps = Vec::new();
    for v in 0..f.source().algebra().quiver().num_vertices() {
        maps.push(matrix_inverse(f.map_at(v), &field)?);
    }
    Morphism::new(f.target(), f.source(), maps).ok()
}

fn defect_non_invertible() -> BasicError {
    BasicError::Defect {
        reason: "the radical criterion returned a non-invertible map between certified \
                 indecomposables"
            .to_string(),
    }
}

/// A module with its certified indecomposable summands, pairwise
/// non-isomorphic.
///
/// Fields are private and construction goes through
/// [`BasicDecomposition::new`], so a value of this type proves the module
/// basic. The zero module is a legitimate value with zero summands: it is the
/// module part of the pair `(0, A)`.
#[derive(Clone)]
pub struct BasicDecomposition {
    module: Module,
    summands: Vec<IndecomposableModule>,
}

/// The direct sum of certified summands, in the order given, and the zero
/// module for an empty list.
fn assemble(algebra: &Arc<Algebra>, summands: &[IndecomposableModule]) -> Module {
    let parts: Vec<&Module> = summands.iter().map(|s| s.module()).collect();
    if parts.is_empty() {
        Module::zero(algebra)
    } else {
        direct_sum(&parts).0
    }
}

impl fmt::Debug for BasicDecomposition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BasicDecomposition")
            .field("dim_vector", &self.module.dim_vector())
            .field("summand_dim_vectors", &self.dim_vectors())
            .finish()
    }
}

impl BasicDecomposition {
    /// Decomposes `m` and requires the summands pairwise non-isomorphic.
    ///
    /// [`krull_schmidt`] groups the summands into isomorphism classes, each
    /// class representative goes through [`IndecomposableModule::new`], and a
    /// class of multiplicity two or more is [`BasicError::NotBasic`]. A
    /// [`KrullSchmidtOutcome::Unknown`] or an [`IndecError::Undetermined`] is
    /// [`BasicError::CertificationBlocked`]. The zero module gives zero
    /// summands.
    pub fn new(m: &Module) -> Result<BasicDecomposition, BasicError> {
        let classes = match krull_schmidt(m) {
            KrullSchmidtOutcome::Classes(classes) => classes,
            KrullSchmidtOutcome::Unknown { reason } => {
                return Err(BasicError::CertificationBlocked { reason });
            }
        };
        let mut summands = Vec::with_capacity(classes.len());
        for class in &classes {
            if class.multiplicity > 1 {
                // Classes carry multiplicities, not positions. Listing a class
                // once per copy in class order puts the first repeat directly
                // after the entry counted so far.
                return Err(BasicError::NotBasic {
                    first: summands.len(),
                    second: summands.len() + 1,
                });
            }
            summands.push(certified(class.endo.clone())?);
        }
        Ok(BasicDecomposition {
            module: m.clone(),
            summands,
        })
    }

    /// This decomposition with the summand at `slot` dropped, or `None` when
    /// `slot` is not a summand position.
    ///
    /// Basicness is inherited, which is why no [`krull_schmidt`] runs: the
    /// kept summands are a sublist of a pairwise non-isomorphic list, so they
    /// stay pairwise non-isomorphic, and each keeps the certificate it was
    /// built with. The module is reassembled as their direct sum in the same
    /// order. The summand values are the stored ones, so a
    /// [`crate::taurigid::TauCache`] keyed by module identity still hits on
    /// them.
    pub fn without(&self, slot: usize) -> Option<BasicDecomposition> {
        if slot >= self.summands.len() {
            return None;
        }
        let summands: Vec<IndecomposableModule> = self
            .summands
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != slot)
            .map(|(_, x)| x.clone())
            .collect();
        Some(BasicDecomposition {
            module: assemble(self.module.algebra(), &summands),
            summands,
        })
    }

    /// This decomposition with `summand` appended.
    ///
    /// Basicness needs exactly one check here. The stored summands are
    /// pairwise non-isomorphic by the invariant and `summand` carries its own
    /// indecomposability certificate, so the only way to lose basicness is
    /// for `summand` to repeat a stored summand. That is one radical
    /// criterion test per stored summand, not a [`krull_schmidt`] of the sum.
    ///
    /// # Errors
    /// [`BasicError::NotBasic`] when `summand` is isomorphic to the stored
    /// summand `first`, with `second` the position it would have taken.
    /// [`BasicError::DifferentAlgebras`] when `summand` lives over another
    /// algebra value.
    pub fn with_new_summand(
        &self,
        summand: &IndecomposableModule,
    ) -> Result<BasicDecomposition, BasicError> {
        if !Arc::ptr_eq(self.module.algebra(), summand.module().algebra()) {
            return Err(BasicError::DifferentAlgebras);
        }
        for (first, x) in self.summands.iter().enumerate() {
            if indecomposable_iso(summand.module(), x.module(), summand.endo()).is_some() {
                return Err(BasicError::NotBasic {
                    first,
                    second: self.summands.len(),
                });
            }
        }
        let mut summands = self.summands.clone();
        summands.push(summand.clone());
        Ok(BasicDecomposition {
            module: assemble(self.module.algebra(), &summands),
            summands,
        })
    }

    /// The decomposition of the sum of the catalog entries listed in
    /// `chosen`, in the order of `chosen`.
    ///
    /// Both catalog enumerators emit one certified entry per isomorphism
    /// class, so distinct entries are pairwise non-isomorphic, distinct
    /// entries are already a basic decomposition, and [`krull_schmidt`] has
    /// nothing to decide. The summands are the catalog's own module values,
    /// so a [`crate::taurigid::TauCache`] keyed by module identity holds one
    /// translate per catalog entry across every subset.
    ///
    /// # Errors
    /// [`BasicError::NotBasic`] when `chosen` lists one entry twice.
    ///
    /// # Panics
    /// Panics when an entry of `chosen` is not a catalog position.
    pub fn from_catalog(
        catalog: &IndecomposableCatalog,
        chosen: &[usize],
    ) -> Result<BasicDecomposition, BasicError> {
        for (second, &i) in chosen.iter().enumerate() {
            assert!(
                i < catalog.len(),
                "from_catalog: entry {i} is not one of the {} catalog positions",
                catalog.len()
            );
            if let Some(first) = chosen[..second].iter().position(|&j| j == i) {
                return Err(BasicError::NotBasic { first, second });
            }
        }
        let summands: Vec<IndecomposableModule> = chosen
            .iter()
            .map(|&i| (*catalog.entries()[i]).clone())
            .collect();
        Ok(BasicDecomposition {
            module: assemble(catalog.algebra(), &summands),
            summands,
        })
    }

    /// The decomposed module.
    #[inline]
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// The certified summands, in decomposition order.
    #[inline]
    pub fn summands(&self) -> &[IndecomposableModule] {
        &self.summands
    }

    /// The number of indecomposable summands.
    #[inline]
    pub fn len(&self) -> usize {
        self.summands.len()
    }

    /// Whether the module is zero, which is the only case with no summands.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.summands.is_empty()
    }

    /// The summand dimension vectors, sorted lexicographically with
    /// repetitions preserved.
    ///
    /// The summands of a basic module are pairwise non-isomorphic, so no
    /// repetition can come from a repeated summand. Two distinct summands can
    /// still share a dimension vector, so the list is not a set: over
    /// `kronecker(2)` three pairwise non-isomorphic indecomposables have the
    /// dimension vector `[1, 1]`.
    pub fn dim_vectors(&self) -> Vec<Vec<usize>> {
        let mut out: Vec<Vec<usize>> = self
            .summands
            .iter()
            .map(|s| s.module().dim_vector().to_vec())
            .collect();
        out.sort();
        out
    }
}

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

impl fmt::Debug for ProjectiveSupport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProjectiveSupport")
            .field("vertices", &self.vertices)
            .finish()
    }
}

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

    /// The algebra the projectives come from.
    #[inline]
    pub fn algebra(&self) -> &Arc<Algebra> {
        &self.algebra
    }

    /// The support vertices, sorted and deduplicated.
    #[inline]
    pub fn vertices(&self) -> &[u32] {
        &self.vertices
    }

    /// The number of support vertices, which is the number of indecomposable
    /// summands of the projective.
    #[inline]
    pub fn len(&self) -> usize {
        self.vertices.len()
    }

    /// Whether the support is empty, which means the projective is zero.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.vertices.is_empty()
    }

    /// Whether `v` lies in the support.
    pub fn contains(&self, v: u32) -> bool {
        self.vertices.binary_search(&v).is_ok()
    }

    /// Whether both supports come from one algebra value (the same [`Arc`]).
    pub fn is_compatible(&self, other: &ProjectiveSupport) -> bool {
        Arc::ptr_eq(&self.algebra, &other.algebra)
    }

    /// Rebuilds the canonical module `P_{v_1} + ... + P_{v_k}` in sorted
    /// vertex order; the zero module when the support is empty.
    ///
    /// Each call builds a fresh [`Module`] value, so results of two calls are
    /// isomorphic but never [`Module::ptr_eq`].
    pub fn module(&self) -> Module {
        if self.vertices.is_empty() {
            return Module::zero(&self.algebra);
        }
        let parts: Vec<Module> = self
            .vertices
            .iter()
            .map(|&v| Module::projective(&self.algebra, v))
            .collect();
        let refs: Vec<&Module> = parts.iter().collect();
        let (sum, _, _) = direct_sum(&refs);
        sum
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
    bijection: Vec<usize>,
    forward: Vec<Morphism>,
    backward: Vec<Morphism>,
}

impl fmt::Debug for SupportPairIsoWitness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SupportPairIsoWitness")
            .field("bijection", &self.bijection)
            .finish()
    }
}

impl SupportPairIsoWitness {
    /// `bijection()[i]` is the summand of the second module matched to
    /// summand `i` of the first.
    #[inline]
    pub fn bijection(&self) -> &[usize] {
        &self.bijection
    }

    /// `forward()[i]` runs from summand `i` of the first module to summand
    /// `bijection()[i]` of the second.
    #[inline]
    pub fn forward(&self) -> &[Morphism] {
        &self.forward
    }

    /// `backward()[i]` is the inverse of `forward()[i]`.
    #[inline]
    pub fn backward(&self) -> &[Morphism] {
        &self.backward
    }

    /// Rechecks the witness: the bijection is a permutation, and each pair of
    /// stored maps multiplies to the identity in both orders.
    pub fn verify(&self) -> bool {
        if self.forward.len() != self.bijection.len() || self.backward.len() != self.bijection.len()
        {
            return false;
        }
        let mut seen = vec![false; self.bijection.len()];
        for &j in &self.bijection {
            if j >= seen.len() || seen[j] {
                return false;
            }
            seen[j] = true;
        }
        for (f, g) in self.forward.iter().zip(&self.backward) {
            let (Ok(round), Ok(round_back)) = (f.then(g), g.then(f)) else {
                return false;
            };
            if round != identity(f.source()) || round_back != identity(g.source()) {
                return false;
            }
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
        let mut matched = None;
        for (j, y) in b_mod.summands().iter().enumerate() {
            if used[j] {
                continue;
            }
            if let Some(f) = indecomposable_iso(x.module(), y.module(), x.endo()) {
                matched = Some((j, f));
                break;
            }
        }
        let Some((j, f)) = matched else {
            return Ok(SupportPairIsoOutcome::NotIsomorphic(
                SupportPairObstruction::UnmatchedSummand {
                    index: i,
                    dim_vector: x.module().dim_vector().to_vec(),
                },
            ));
        };
        let Some(g) = inverse_of(&f) else {
            return Err(defect_non_invertible());
        };
        used[j] = true;
        bijection.push(j);
        forward.push(f);
        backward.push(g);
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
    /// The dimension vector.
    #[inline]
    pub fn dim_vector(&self) -> &[usize] {
        &self.dim_vector
    }

    /// The Loewy length, from [`loewy_length`].
    #[inline]
    pub fn loewy_length(&self) -> usize {
        self.loewy_length
    }

    /// The dimension vector of `top X`.
    #[inline]
    pub fn top_dim_vector(&self) -> &[usize] {
        &self.top_dim_vector
    }

    /// The dimension vector of `soc X`.
    #[inline]
    pub fn socle_dim_vector(&self) -> &[usize] {
        &self.socle_dim_vector
    }

    /// `dim_Fp End(X)`.
    #[inline]
    pub fn end_dim(&self) -> usize {
        self.end_dim
    }

    /// The residue degree of `End(X)`, from
    /// [`IndecomposableModule::residue_degree`].
    #[inline]
    pub fn residue_degree(&self) -> usize {
        self.residue_degree
    }

    /// `hom_dim(S_v, X)` for every vertex `v`, in vertex order.
    #[inline]
    pub fn hom_from_simples(&self) -> &[usize] {
        &self.hom_from_simples
    }

    /// `hom_dim(X, S_v)` for every vertex `v`, in vertex order.
    #[inline]
    pub fn hom_to_simples(&self) -> &[usize] {
        &self.hom_to_simples
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
                hom_from_simples.push(hom_dim(simple, m)?);
                hom_to_simples.push(hom_dim(m, simple)?);
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

    /// The projective support the fingerprint was keyed on.
    #[inline]
    pub fn projective_support(&self) -> &[u32] {
        &self.projective_support
    }

    /// The per-summand records, sorted.
    #[inline]
    pub fn summands(&self) -> &[SummandFingerprint] {
        &self.summands
    }
}

/// One summand of a module together with the summand of `T` it matches.
#[derive(Clone)]
pub struct AddMatch {
    target_index: usize,
    forward: Morphism,
    backward: Morphism,
}

impl fmt::Debug for AddMatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AddMatch")
            .field("target_index", &self.target_index)
            .finish()
    }
}

impl AddMatch {
    /// Index of the matched summand of `T`.
    #[inline]
    pub fn target_index(&self) -> usize {
        self.target_index
    }

    /// The isomorphism from the module summand to the summand of `T`.
    #[inline]
    pub fn forward(&self) -> &Morphism {
        &self.forward
    }

    /// The inverse of [`AddMatch::forward`].
    #[inline]
    pub fn backward(&self) -> &Morphism {
        &self.backward
    }
}

/// A proof that a module lies in `add(T)`.
///
/// The witness holds the module, its indecomposable summands, `T` with its
/// summands, and for every summand one [`AddMatch`]. Every summand of the
/// module is isomorphic to a summand of `T`, so the module is a direct sum of
/// copies of summands of `T`.
///
/// The summands are stored as [`Module`] values rather than as
/// [`IndecomposableModule`] values, because [`IndecomposableModule`] is not
/// [`Clone`]. The indecomposability certificates stay with the
/// [`BasicDecomposition`] inputs the caller holds.
#[derive(Clone)]
pub struct AddClosureWitness {
    module: Module,
    summands: Vec<Module>,
    target: Module,
    target_summands: Vec<Module>,
    matches: Vec<AddMatch>,
}

impl fmt::Debug for AddClosureWitness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AddClosureWitness")
            .field("dim_vector", &self.module.dim_vector())
            .field("target_dim_vector", &self.target.dim_vector())
            .field("matches", &self.matches.len())
            .finish()
    }
}

// Matches each certified summand against a summand of `t`. `Ok(None)` means
// one summand matched nothing, so the module is outside add(T). Summands of
// `t` are reusable: a module in add(T) may repeat a summand.
fn match_summands(
    summands: &[IndecomposableModule],
    t: &BasicDecomposition,
) -> Result<Option<Vec<AddMatch>>, BasicError> {
    let mut matches = Vec::with_capacity(summands.len());
    for x in summands {
        let mut matched = None;
        for (j, y) in t.summands().iter().enumerate() {
            if let Some(f) = indecomposable_iso(x.module(), y.module(), x.endo()) {
                matched = Some((j, f));
                break;
            }
        }
        let Some((target_index, forward)) = matched else {
            return Ok(None);
        };
        let Some(backward) = inverse_of(&forward) else {
            return Err(defect_non_invertible());
        };
        matches.push(AddMatch {
            target_index,
            forward,
            backward,
        });
    }
    Ok(Some(matches))
}

fn target_summand_modules(t: &BasicDecomposition) -> Vec<Module> {
    t.summands().iter().map(|y| y.module().clone()).collect()
}

impl AddClosureWitness {
    /// Places a basic module in `add(T)`, or reports that it is outside.
    ///
    /// Returns `Ok(None)` when some summand of `m` is isomorphic to no
    /// summand of `t`. Both inputs are basic, so every summand of `m` matches
    /// a different summand of `t`. Use [`AddClosureWitness::from_module`] for
    /// a module that is in `add(T)` without being basic.
    ///
    /// Errors when the inputs do not share one algebra value.
    pub fn new(
        m: &BasicDecomposition,
        t: &BasicDecomposition,
    ) -> Result<Option<AddClosureWitness>, BasicError> {
        if !Arc::ptr_eq(m.module().algebra(), t.module().algebra()) {
            return Err(BasicError::DifferentAlgebras);
        }
        let Some(matches) = match_summands(m.summands(), t)? else {
            return Ok(None);
        };
        Ok(Some(AddClosureWitness {
            module: m.module().clone(),
            summands: m
                .summands()
                .iter()
                .map(|x| x.module().clone())
                .collect::<Vec<Module>>(),
            target: t.module().clone(),
            target_summands: target_summand_modules(t),
            matches,
        }))
    }

    /// Places any module in `add(T)`, with multiplicities.
    ///
    /// A module in `add(T)` need not be basic: `T + T` lies in `add(T)`. This
    /// constructor decomposes `m` without the pairwise-distinct requirement of
    /// [`BasicDecomposition`] and matches each summand separately, so one
    /// summand of `t` can be matched more than once.
    ///
    /// Returns `Ok(None)` when some summand of `m` is isomorphic to no
    /// summand of `t`. An undetermined summand is
    /// [`BasicError::CertificationBlocked`]. Errors when the inputs do not
    /// share one algebra value.
    pub fn from_module(
        m: &Module,
        t: &BasicDecomposition,
    ) -> Result<Option<AddClosureWitness>, BasicError> {
        if !Arc::ptr_eq(m.algebra(), t.module().algebra()) {
            return Err(BasicError::DifferentAlgebras);
        }
        let decomposition = decompose(m);
        for certificate in decomposition.certificates() {
            if let Certificate::Undetermined { attempts } = certificate {
                return Err(BasicError::CertificationBlocked {
                    reason: format!(
                        "a summand stayed undetermined after {attempts} split attempts"
                    ),
                });
            }
        }
        let mut summands = Vec::with_capacity(decomposition.summands().len());
        for endo in decomposition.endos() {
            summands.push(certified(endo.clone())?);
        }
        let Some(matches) = match_summands(&summands, t)? else {
            return Ok(None);
        };
        Ok(Some(AddClosureWitness {
            module: m.clone(),
            summands: summands
                .iter()
                .map(|x| x.module().clone())
                .collect::<Vec<Module>>(),
            target: t.module().clone(),
            target_summands: target_summand_modules(t),
            matches,
        }))
    }

    /// The module placed in `add(T)`.
    #[inline]
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// The indecomposable summands of the module, in decomposition order.
    #[inline]
    pub fn summands(&self) -> &[Module] {
        &self.summands
    }

    /// `T` itself.
    #[inline]
    pub fn target(&self) -> &Module {
        &self.target
    }

    /// The indecomposable summands of `T`, in decomposition order.
    #[inline]
    pub fn target_summands(&self) -> &[Module] {
        &self.target_summands
    }

    /// One match per summand of the module, in summand order.
    #[inline]
    pub fn matches(&self) -> &[AddMatch] {
        &self.matches
    }

    /// Rechecks the witness: one match per summand, endpoints as recorded,
    /// and each pair of stored maps multiplies to the identity in both
    /// orders.
    pub fn verify(&self) -> bool {
        if self.matches.len() != self.summands.len() {
            return false;
        }
        for (x, entry) in self.summands.iter().zip(&self.matches) {
            let Some(y) = self.target_summands.get(entry.target_index) else {
                return false;
            };
            if !entry.forward.source().ptr_eq(x)
                || !entry.forward.target().ptr_eq(y)
                || !entry.backward.source().ptr_eq(y)
                || !entry.backward.target().ptr_eq(x)
            {
                return false;
            }
            let (Ok(round), Ok(round_back)) = (
                entry.forward.then(&entry.backward),
                entry.backward.then(&entry.forward),
            ) else {
                return false;
            };
            if round != identity(x) || round_back != identity(y) {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{commutative_square, kronecker, linear_an, truncated_poly};
    use crate::arquiver::IndecomposableCatalog;
    use crate::dynkin::{DynkinType, dynkin_quiver};
    use crate::field::PrimeField;
    use crate::linalg::DenseMat;
    use crate::quiver::{ArrowId, Quiver};
    use crate::supporttau::enumerate_over_catalog;

    fn f2() -> PrimeField {
        PrimeField::new(2).unwrap()
    }

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn fields() -> [PrimeField; 2] {
        [f2(), f5()]
    }

    fn path_algebra(quiver: Quiver, field: PrimeField) -> Arc<Algebra> {
        crate::algebra::path_algebra(quiver, field)
            .expect("the zero ideal over an acyclic quiver completes")
    }

    // D_4 as dynkin_quiver builds it: vertex 0 is the center, arrows 0 -> 1,
    // 0 -> 2, 0 -> 3.
    fn d4(field: PrimeField) -> Arc<Algebra> {
        path_algebra(
            dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver"),
            field,
        )
    }

    fn basic(m: &Module) -> BasicDecomposition {
        BasicDecomposition::new(m).expect("the fixture module is basic")
    }

    fn support(algebra: &Arc<Algebra>, vertices: &[u32]) -> ProjectiveSupport {
        ProjectiveSupport::new(algebra, vertices).expect("the fixture vertices are in range")
    }

    fn sum(parts: &[&Module]) -> Module {
        let (total, _, _) = direct_sum(parts);
        total
    }

    fn expect_witness(outcome: SupportPairIsoOutcome) -> SupportPairIsoWitness {
        match outcome {
            SupportPairIsoOutcome::Isomorphic(witness) => witness,
            SupportPairIsoOutcome::NotIsomorphic(obstruction) => {
                panic!("expected an isomorphism, got {obstruction:?}")
            }
        }
    }

    fn expect_obstruction(outcome: SupportPairIsoOutcome) -> SupportPairObstruction {
        match outcome {
            SupportPairIsoOutcome::NotIsomorphic(obstruction) => obstruction,
            SupportPairIsoOutcome::Isomorphic(witness) => {
                panic!("expected an obstruction, got {witness:?}")
            }
        }
    }

    // Dropping a summand keeps the certified values: the kept summands are the
    // same module values, not rebuilt ones, which is what a TauCache keyed by
    // module identity needs.
    #[test]
    fn without_keeps_the_stored_summand_values() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let parts: Vec<Module> = (0..3).map(|v| Module::projective(&algebra, v)).collect();
            let refs: Vec<&Module> = parts.iter().collect();
            let whole = basic(&sum(&refs));
            assert!(whole.without(3).is_none(), "there is no slot 3");
            for slot in 0..3 {
                let kept = whole.without(slot).expect("the slot is a summand");
                assert_eq!(kept.len(), 2);
                let mut expected: Vec<&IndecomposableModule> = Vec::new();
                for (i, x) in whole.summands().iter().enumerate() {
                    if i != slot {
                        expected.push(x);
                    }
                }
                for (a, b) in kept.summands().iter().zip(expected) {
                    assert!(a.module().ptr_eq(b.module()));
                }
                assert_eq!(
                    kept.module().dim_vector(),
                    BasicDecomposition::new(kept.module())
                        .expect("a sum of two projectives is basic")
                        .module()
                        .dim_vector()
                );
            }
        }
    }

    #[test]
    fn with_new_summand_appends_and_rejects_a_repeat() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p1 = Module::projective(&algebra, 1);
            let one = basic(&p0);
            let other = IndecomposableModule::new(&p1).expect("P_1 is indecomposable");
            let two = one
                .with_new_summand(&other)
                .expect("P_0 and P_1 are not isomorphic");
            assert_eq!(two.len(), 2);
            assert!(two.summands()[0].module().ptr_eq(&p0));
            assert!(two.summands()[1].module().ptr_eq(&p1));
            assert_eq!(two.module().dim_vector(), sum(&[&p0, &p1]).dim_vector());
            let repeat = IndecomposableModule::new(&Module::projective(&algebra, 0))
                .expect("P_0 is indecomposable");
            assert_eq!(
                two.with_new_summand(&repeat).err(),
                Some(BasicError::NotBasic {
                    first: 0,
                    second: 2
                })
            );
            let elsewhere = linear_an(3, field);
            let outside = IndecomposableModule::new(&Module::simple(&elsewhere, 0))
                .expect("a simple is indecomposable");
            assert_eq!(
                two.with_new_summand(&outside).err(),
                Some(BasicError::DifferentAlgebras)
            );
        }
    }

    // The catalog constructor skips Krull-Schmidt, so its answer has to agree
    // with the general one on the same subset, summand for summand.
    #[test]
    fn from_catalog_agrees_with_the_general_constructor() {
        for field in fields() {
            let algebra = d4(field);
            let catalog = IndecomposableCatalog::dynkin(&algebra).expect("D_4 is Dynkin");
            for chosen in [vec![], vec![0], vec![2, 5], vec![1, 3, 7]] {
                let from_catalog = BasicDecomposition::from_catalog(&catalog, &chosen)
                    .expect("distinct catalog entries are pairwise non-isomorphic");
                assert_eq!(from_catalog.len(), chosen.len());
                for (x, &i) in from_catalog.summands().iter().zip(&chosen) {
                    assert!(x.module().ptr_eq(catalog.entries()[i].module()));
                }
                let parts: Vec<&Module> = chosen
                    .iter()
                    .map(|&i| catalog.entries()[i].module())
                    .collect();
                let assembled = if parts.is_empty() {
                    Module::zero(&algebra)
                } else {
                    sum(&parts)
                };
                let general = basic(&assembled);
                assert_eq!(general.dim_vectors(), from_catalog.dim_vectors());
                assert_eq!(
                    general.module().dim_vector(),
                    from_catalog.module().dim_vector()
                );
            }
            assert_eq!(
                BasicDecomposition::from_catalog(&catalog, &[4, 4]).err(),
                Some(BasicError::NotBasic {
                    first: 0,
                    second: 1
                })
            );
        }
    }

    // The three Kronecker representations of dimension vector [1, 1] over
    // F_2: the arrow pair (a, b) takes the values (1, 0), (0, 1), and (1, 1),
    // which are the three points of P^1(F_2). All three are indecomposable
    // and pairwise non-isomorphic.
    fn kronecker_line(algebra: &Arc<Algebra>, field: PrimeField, a: i64, b: i64) -> Module {
        Module::new(
            algebra.clone(),
            vec![1, 1],
            vec![
                DenseMat::from_rows(&[vec![field.elem(a)]]),
                DenseMat::from_rows(&[vec![field.elem(b)]]),
            ],
        )
        .expect("a Kronecker representation is a module")
    }

    // P_v is indecomposable, so its basic decomposition has one summand whose
    // dimension vector is the row v of the Cartan matrix.
    #[test]
    fn each_projective_gives_one_summand() {
        for field in fields() {
            for algebra in [
                linear_an(3, field),
                d4(field),
                truncated_poly(3, field).unwrap(),
                commutative_square(field),
                kronecker(2, field),
            ] {
                for v in 0..algebra.quiver().num_vertices() {
                    let p = Module::projective(&algebra, v);
                    let decomposition = basic(&p);
                    assert_eq!(decomposition.len(), 1, "P_{v} over F_{}", field.modulus());
                    assert!(!decomposition.is_empty());
                    assert!(decomposition.module().ptr_eq(&p));
                    assert_eq!(decomposition.dim_vectors(), vec![p.dim_vector().to_vec()]);
                }
            }
        }
    }

    // Linearly oriented A_3: P_0 = [1, 1, 1], P_1 = [0, 1, 1], P_2 = [0, 0, 1].
    // The three are pairwise non-isomorphic, so the sum is basic and the
    // sorted dimension vectors are [0, 0, 1] < [0, 1, 1] < [1, 1, 1].
    #[test]
    fn the_sum_of_the_a3_projectives_is_basic() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let parts: Vec<Module> = (0..3).map(|v| Module::projective(&algebra, v)).collect();
            let total = sum(&[&parts[0], &parts[1], &parts[2]]);
            let decomposition = basic(&total);
            assert_eq!(decomposition.len(), 3);
            assert_eq!(
                decomposition.dim_vectors(),
                vec![vec![0, 0, 1], vec![0, 1, 1], vec![1, 1, 1]],
                "over F_{}",
                field.modulus()
            );
        }
    }

    // D_4 with every arrow leaving the center: P_0 = [1, 1, 1, 1] and
    // P_1 = P_2 = P_3 are the simples at the three leaves.
    #[test]
    fn the_sum_of_the_d4_projectives_is_basic() {
        for field in fields() {
            let algebra = d4(field);
            let parts: Vec<Module> = (0..4).map(|v| Module::projective(&algebra, v)).collect();
            let total = sum(&[&parts[0], &parts[1], &parts[2], &parts[3]]);
            let decomposition = basic(&total);
            assert_eq!(decomposition.len(), 4);
            assert_eq!(
                decomposition.dim_vectors(),
                vec![
                    vec![0, 0, 0, 1],
                    vec![0, 0, 1, 0],
                    vec![0, 1, 0, 0],
                    vec![1, 1, 1, 1],
                ],
                "over F_{}",
                field.modulus()
            );
        }
    }

    // k[x]/(x^3) has one vertex and three indecomposables, of dimension 1, 2,
    // and 3. The regular module is the one of dimension 3.
    #[test]
    fn truncated_poly_three_gives_summands_of_dimension_one_and_three() {
        for field in fields() {
            let algebra = truncated_poly(3, field).unwrap();
            let regular = Module::projective(&algebra, 0);
            let simple = Module::simple(&algebra, 0);
            let decomposition = basic(&sum(&[&regular, &simple]));
            assert_eq!(decomposition.len(), 2);
            assert_eq!(
                decomposition.dim_vectors(),
                vec![vec![1], vec![3]],
                "over F_{}",
                field.modulus()
            );
        }
    }

    // The commutative square: P_0 = [1, 1, 1, 1] (e_0, a, c, ab = cd),
    // P_1 = [0, 1, 0, 1], P_2 = [0, 0, 1, 1], P_3 = [0, 0, 0, 1].
    #[test]
    fn the_commutative_square_projectives_have_the_expected_dim_vectors() {
        for field in fields() {
            let algebra = commutative_square(field);
            let expected = [
                vec![1, 1, 1, 1],
                vec![0, 1, 0, 1],
                vec![0, 0, 1, 1],
                vec![0, 0, 0, 1],
            ];
            for (v, want) in expected.iter().enumerate() {
                let p = Module::projective(&algebra, v as u32);
                assert_eq!(basic(&p).dim_vectors(), vec![want.clone()]);
            }
        }
    }

    #[test]
    fn the_zero_module_has_no_summands() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let zero = Module::zero(&algebra);
            let decomposition = basic(&zero);
            assert_eq!(decomposition.len(), 0);
            assert!(decomposition.is_empty());
            assert!(decomposition.dim_vectors().is_empty());
            assert!(decomposition.module().ptr_eq(&zero));
        }
    }

    // P_0 + P_0 has one isomorphism class of multiplicity 2, so the repeat
    // sits at index 1 of the summand list.
    #[test]
    fn a_repeated_summand_is_rejected() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let doubled = sum(&[&p0, &p0]);
            assert_eq!(
                BasicDecomposition::new(&doubled).unwrap_err(),
                BasicError::NotBasic {
                    first: 0,
                    second: 1
                },
                "P_0 + P_0 over F_{}",
                field.modulus()
            );
        }
    }

    // A repeat of a separately built copy is still a repeat: identity is
    // isomorphism, not module identity.
    #[test]
    fn a_repeated_summand_from_a_fresh_copy_is_rejected() {
        let algebra = linear_an(3, f5());
        let first = Module::projective(&algebra, 1);
        let second = Module::projective(&algebra, 1);
        assert!(matches!(
            BasicDecomposition::new(&sum(&[&first, &second])).unwrap_err(),
            BasicError::NotBasic { .. }
        ));
    }

    #[test]
    fn projective_support_sorts_and_deduplicates() {
        let algebra = linear_an(3, f5());
        let s = support(&algebra, &[2, 0, 2, 1, 0]);
        assert_eq!(s.vertices(), &[0, 1, 2]);
        assert_eq!(s.len(), 3);
        assert!(!s.is_empty());
        assert!(s.contains(0) && s.contains(1) && s.contains(2));
        assert!(!s.contains(3));
        assert_eq!(support(&algebra, &[]).len(), 0);
        assert!(support(&algebra, &[]).is_empty());
    }

    #[test]
    fn an_out_of_range_support_vertex_is_rejected() {
        let algebra = linear_an(3, f5());
        assert_eq!(
            ProjectiveSupport::new(&algebra, &[0, 3]).unwrap_err(),
            BasicError::VertexOutOfRange {
                vertex: 3,
                num_vertices: 3
            }
        );
    }

    // Over A_3, P_0 = [1, 1, 1] and P_2 = [0, 0, 1], so the support {0, 2}
    // rebuilds a module of dimension vector [1, 1, 2] with two summands.
    #[test]
    fn the_support_module_is_the_sum_of_its_projectives() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let s = support(&algebra, &[2, 0]);
            let module = s.module();
            assert_eq!(module.dim_vector(), &[1, 1, 2]);
            let decomposition = basic(&module);
            assert_eq!(
                decomposition.dim_vectors(),
                vec![vec![0, 0, 1], vec![1, 1, 1]]
            );
            assert!(support(&algebra, &[]).module().is_zero());
        }
    }

    #[test]
    fn support_equality_is_set_equality_and_compatibility_is_separate() {
        let algebra = linear_an(3, f5());
        let other = linear_an(3, f5());
        assert_eq!(support(&algebra, &[1, 0]), support(&algebra, &[0, 1, 0]));
        assert_ne!(support(&algebra, &[1]), support(&algebra, &[2]));
        // Equality ignores the algebra; is_compatible is what separates two
        // algebra values built from the same presentation.
        assert_eq!(support(&algebra, &[1]), support(&other, &[1]));
        assert!(support(&algebra, &[1]).is_compatible(&support(&algebra, &[2])));
        assert!(!support(&algebra, &[1]).is_compatible(&support(&other, &[1])));
    }

    // Two separately built copies of (P_0 + P_2, P_1) over A_3. Both sides
    // decompose in the order `the_decomposition_order_is_pinned` fixes, so
    // the greedy scan of pair_iso matches summand i to summand i and the
    // bijection is the identity.
    #[test]
    fn a_pair_is_isomorphic_to_a_fresh_copy_of_itself() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p2 = Module::projective(&algebra, 2);
            let first = basic(&sum(&[&p0, &p2]));
            let second = basic(&sum(&[&p0, &p2]));
            let s = support(&algebra, &[1]);
            let witness = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
            assert!(witness.verify());
            assert_eq!(witness.bijection(), &[0, 1], "over F_{}", field.modulus());
            assert_eq!(witness.forward().len(), 2);
            assert_eq!(witness.backward().len(), 2);
        }
    }

    // `docs/v0.5-design.md` section 14 requires every stored witness to be
    // deterministic across processes and platforms, so the order the summands
    // come out in is part of the contract. The order is not hand-derivable:
    // `decompose` splits with a Fitting-lemma recursion seeded per call
    // (`DECOMPOSE_SEED`), and `krull_schmidt` lists classes in the order that
    // recursion first produced them. It is exact linear algebra over F_p with
    // no wall-clock and no thread input, so the order is reproducible. This
    // test is the snapshot that catches a change in it.
    //
    // On these fixtures the recursion returns the summands in the reverse of
    // the assembly order: P_0 + P_2 comes out as [0, 0, 1] then [1, 1, 1],
    // P_2 + P_0 comes out the other way, and the regular module
    // P_0 + P_1 + P_2 comes out as [0, 0, 1], [0, 1, 1], [1, 1, 1]. That
    // reversal is what the current recursion does on these inputs, not a rule
    // the type promises.
    #[test]
    fn the_decomposition_order_is_pinned() {
        fn order(d: &BasicDecomposition) -> Vec<Vec<usize>> {
            d.summands()
                .iter()
                .map(|x| x.module().dim_vector().to_vec())
                .collect()
        }
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p1 = Module::projective(&algebra, 1);
            let p2 = Module::projective(&algebra, 2);
            let context = format!("over F_{}", field.modulus());
            assert_eq!(
                order(&basic(&sum(&[&p0, &p2]))),
                vec![vec![0, 0, 1], vec![1, 1, 1]],
                "P_0 + P_2 {context}"
            );
            assert_eq!(
                order(&basic(&sum(&[&p2, &p0]))),
                vec![vec![1, 1, 1], vec![0, 0, 1]],
                "P_2 + P_0 {context}"
            );
            assert_eq!(
                order(&basic(&sum(&[&p0, &p1, &p2]))),
                vec![vec![0, 0, 1], vec![0, 1, 1], vec![1, 1, 1]],
                "the regular module {context}"
            );
            // A second decomposition of the same module repeats the order, so
            // nothing carries over from one call to the next.
            assert_eq!(
                order(&basic(&sum(&[&p0, &p2]))),
                order(&basic(&sum(&[&p0, &p2]))),
                "two calls {context}"
            );
        }
    }

    // The bijection of a SupportPairIsoWitness is deterministic for the same
    // reason: both decomposition orders are pinned, and pair_iso scans the
    // summands of the second module in order and takes the first match.
    //
    // P_0 + P_2 against a fresh P_0 + P_2: both decompose as [0, 0, 1] then
    // [1, 1, 1], and no summand of A_3 matches two of them, so the bijection
    // is [0, 1]. P_0 + P_2 against P_2 + P_0: the second decomposes as
    // [1, 1, 1] then [0, 0, 1], so summand 0 of the first, [0, 0, 1], matches
    // summand 1 of the second and the bijection is [1, 0].
    #[test]
    fn the_pair_iso_bijection_is_pinned() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p2 = Module::projective(&algebra, 2);
            let s = support(&algebra, &[1]);
            let first = basic(&sum(&[&p0, &p2]));
            let same = basic(&sum(&[&p0, &p2]));
            let reversed = basic(&sum(&[&p2, &p0]));
            assert_eq!(first.summands()[0].module().dim_vector(), &[0, 0, 1]);
            assert_eq!(reversed.summands()[0].module().dim_vector(), &[1, 1, 1]);
            let witness = expect_witness(pair_iso(&first, &s, &same, &s).unwrap());
            assert!(witness.verify());
            assert_eq!(witness.bijection(), &[0, 1], "over F_{}", field.modulus());
            let swapped = expect_witness(pair_iso(&first, &s, &reversed, &s).unwrap());
            assert!(swapped.verify());
            assert_eq!(swapped.bijection(), &[1, 0], "over F_{}", field.modulus());
        }
    }

    // Reversing the summand order changes nothing: identity is isomorphism.
    #[test]
    fn a_pair_is_isomorphic_to_its_summands_in_the_other_order() {
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
        let p1 = Module::projective(&algebra, 1);
        let first = basic(&sum(&[&p0, &p1]));
        let second = basic(&sum(&[&p1, &p0]));
        let s = support(&algebra, &[2]);
        let witness = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
        assert!(witness.verify());
    }

    #[test]
    fn a_different_projective_support_is_an_obstruction() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let module = basic(&Module::projective(&algebra, 0));
            let other = basic(&Module::projective(&algebra, 0));
            let left = support(&algebra, &[1]);
            let right = support(&algebra, &[2]);
            assert_eq!(
                expect_obstruction(pair_iso(&module, &left, &other, &right).unwrap()),
                SupportPairObstruction::ProjectiveSupport {
                    first: vec![1],
                    second: vec![2]
                }
            );
        }
    }

    #[test]
    fn a_different_summand_count_is_an_obstruction() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p2 = Module::projective(&algebra, 2);
            let two = basic(&sum(&[&p0, &p2]));
            let one = basic(&p0);
            let s = support(&algebra, &[1]);
            assert_eq!(
                expect_obstruction(pair_iso(&two, &s, &one, &s).unwrap()),
                SupportPairObstruction::SummandCount {
                    first: 2,
                    second: 1
                }
            );
        }
    }

    // P_0 + P_2 against P_0 + P_1: both have two summands and the same
    // support, and P_2 = [0, 0, 1] matches neither P_0 nor P_1.
    #[test]
    fn an_unmatched_summand_is_an_obstruction() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p1 = Module::projective(&algebra, 1);
            let p2 = Module::projective(&algebra, 2);
            let left = basic(&sum(&[&p0, &p2]));
            let right = basic(&sum(&[&p0, &p1]));
            let s = support(&algebra, &[1]);
            let obstruction = expect_obstruction(pair_iso(&left, &s, &right, &s).unwrap());
            match obstruction {
                SupportPairObstruction::UnmatchedSummand { index, dim_vector } => {
                    assert_eq!(left.summands()[index].module().dim_vector(), &[0, 0, 1]);
                    assert_eq!(dim_vector, vec![0, 0, 1]);
                }
                other => panic!("expected an unmatched summand, got {other:?}"),
            }
        }
    }

    #[test]
    fn a_tampered_bijection_fails_verification() {
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let first = basic(&sum(&[&p0, &p2]));
        let second = basic(&sum(&[&p0, &p2]));
        let s = support(&algebra, &[1]);
        let mut witness = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
        assert!(witness.verify());
        // Two summands sent to one target is not a permutation.
        witness.bijection = vec![0, 0];
        assert!(!witness.verify());
        // A dropped map leaves fewer isomorphisms than bijection entries.
        let mut short = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
        short.forward.pop();
        assert!(!short.verify());
    }

    #[test]
    fn a_tampered_isomorphism_fails_verification() {
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
        let first = basic(&p0);
        let second = basic(&Module::projective(&algebra, 0));
        let s = support(&algebra, &[1]);
        let mut witness = expect_witness(pair_iso(&first, &s, &second, &s).unwrap());
        // Replacing the inverse by the forward map breaks the composite,
        // since the two run in opposite directions.
        witness.backward = witness.forward.clone();
        assert!(!witness.verify());
    }

    #[test]
    fn mismatched_algebras_are_rejected() {
        let algebra = linear_an(3, f5());
        let other = linear_an(3, f5());
        let first = basic(&Module::projective(&algebra, 0));
        let second = basic(&Module::projective(&other, 0));
        let left = support(&algebra, &[1]);
        let right = support(&other, &[1]);
        assert_eq!(
            pair_iso(&first, &left, &second, &right).unwrap_err(),
            BasicError::DifferentAlgebras
        );
        assert_eq!(
            PairFingerprint::new(&first, &right).unwrap_err(),
            BasicError::DifferentAlgebras
        );
        assert_eq!(
            AddClosureWitness::new(&first, &second).unwrap_err(),
            BasicError::DifferentAlgebras
        );
    }

    #[test]
    fn isomorphic_pairs_have_equal_fingerprints() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p2 = Module::projective(&algebra, 2);
            let first = basic(&sum(&[&p0, &p2]));
            let second = basic(&sum(&[&p2, &p0]));
            let s = support(&algebra, &[1]);
            assert_eq!(
                PairFingerprint::new(&first, &s).unwrap(),
                PairFingerprint::new(&second, &s).unwrap(),
                "over F_{}",
                field.modulus()
            );
        }
    }

    // The fingerprint separates on the projective support, on the summand
    // count, and on the summand dimension vectors.
    #[test]
    fn fingerprints_separate_obviously_different_pairs() {
        let algebra = linear_an(3, f5());
        let p0 = basic(&Module::projective(&algebra, 0));
        let p1 = basic(&Module::projective(&algebra, 1));
        let both = basic(&sum(&[
            &Module::projective(&algebra, 0),
            &Module::projective(&algebra, 2),
        ]));
        let left = support(&algebra, &[1]);
        let right = support(&algebra, &[2]);
        let base = PairFingerprint::new(&p0, &left).unwrap();
        assert_ne!(base, PairFingerprint::new(&p0, &right).unwrap());
        assert_ne!(base, PairFingerprint::new(&p1, &left).unwrap());
        assert_ne!(base, PairFingerprint::new(&both, &left).unwrap());
        assert_eq!(base.projective_support(), &[1]);
        assert_eq!(base.summands().len(), 1);
    }

    // P_0 over A_3 is uniserial with top S_0 and socle S_2, Loewy length 3,
    // and End(P_0) = k. Hom(S_v, P_0) is 1 at v = 2 and 0 elsewhere, because
    // the only simple submodule is the socle; Hom(P_0, S_v) is 1 at v = 0 and
    // 0 elsewhere, because a map out of a projective is fixed by the top.
    #[test]
    fn the_a3_regular_projective_fingerprint_is_hand_checkable() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = basic(&Module::projective(&algebra, 0));
            let s = support(&algebra, &[]);
            let fingerprint = PairFingerprint::new(&p0, &s).unwrap();
            let record = &fingerprint.summands()[0];
            assert_eq!(record.dim_vector(), &[1, 1, 1]);
            assert_eq!(record.loewy_length(), 3);
            assert_eq!(record.top_dim_vector(), &[1, 0, 0]);
            assert_eq!(record.socle_dim_vector(), &[0, 0, 1]);
            assert_eq!(record.end_dim(), 1);
            assert_eq!(record.residue_degree(), 1);
            assert_eq!(record.hom_from_simples(), &[0, 0, 1]);
            assert_eq!(
                record.hom_to_simples(),
                &[1, 0, 0],
                "over F_{}",
                field.modulus()
            );
            assert!(fingerprint.projective_support().is_empty());
        }
    }

    // The three [1, 1] Kronecker modules over F_2 share every fingerprint
    // field. Each has Loewy length 2 with top [1, 0] and socle [0, 1], End is
    // F_2, and the Hom profile against the simples is
    // hom(S_0, X) = 0, hom(S_1, X) = 1, hom(X, S_0) = 1, hom(X, S_1) = 0,
    // because each module has a nonzero arrow map. Only pair_iso separates
    // them.
    #[test]
    fn the_kronecker_line_modules_collide_in_the_fingerprint() {
        let field = f2();
        let algebra = kronecker(2, field);
        let modules = [
            kronecker_line(&algebra, field, 1, 0),
            kronecker_line(&algebra, field, 0, 1),
            kronecker_line(&algebra, field, 1, 1),
        ];
        let empty = support(&algebra, &[]);
        let decompositions: Vec<BasicDecomposition> = modules.iter().map(basic).collect();
        for decomposition in &decompositions {
            assert_eq!(decomposition.len(), 1);
            assert_eq!(decomposition.dim_vectors(), vec![vec![1, 1]]);
        }
        let fingerprints: Vec<PairFingerprint> = decompositions
            .iter()
            .map(|d| PairFingerprint::new(d, &empty).unwrap())
            .collect();
        assert_eq!(fingerprints[0], fingerprints[1]);
        assert_eq!(fingerprints[0], fingerprints[2]);
        let record = &fingerprints[0].summands()[0];
        assert_eq!(record.loewy_length(), 2);
        assert_eq!(record.top_dim_vector(), &[1, 0]);
        assert_eq!(record.socle_dim_vector(), &[0, 1]);
        assert_eq!(record.end_dim(), 1);
        assert_eq!(record.hom_from_simples(), &[0, 1]);
        assert_eq!(record.hom_to_simples(), &[1, 0]);
        for i in 0..3 {
            for j in 0..3 {
                let outcome =
                    pair_iso(&decompositions[i], &empty, &decompositions[j], &empty).unwrap();
                if i == j {
                    assert!(expect_witness(outcome).verify());
                } else {
                    assert_eq!(
                        expect_obstruction(outcome),
                        SupportPairObstruction::UnmatchedSummand {
                            index: 0,
                            dim_vector: vec![1, 1]
                        },
                        "the [1, 1] modules {i} and {j} are not isomorphic"
                    );
                }
            }
        }
    }

    // T = P_0 + P_2 over A_3. P_2 is a summand of T, so it lies in add(T).
    #[test]
    fn a_summand_of_t_lies_in_add_t() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p2 = Module::projective(&algebra, 2);
            let t = basic(&sum(&[&p0, &p2]));
            let m = basic(&Module::projective(&algebra, 2));
            let witness = AddClosureWitness::new(&m, &t)
                .unwrap()
                .expect("P_2 is a summand of T");
            assert!(witness.verify());
            assert_eq!(witness.matches().len(), 1);
            let target = witness.matches()[0].target_index();
            assert_eq!(
                witness.target_summands()[target].dim_vector(),
                &[0, 0, 1],
                "over F_{}",
                field.modulus()
            );
            assert_eq!(witness.summands().len(), 1);
            assert!(witness.target().ptr_eq(t.module()));
        }
    }

    // S_1 = [0, 1, 0] over A_3 is not isomorphic to P_0 = [1, 1, 1] or to
    // P_2 = [0, 0, 1], so it lies outside add(P_0 + P_2).
    #[test]
    fn a_non_summand_is_outside_add_t() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p2 = Module::projective(&algebra, 2);
            let t = basic(&sum(&[&p0, &p2]));
            let m = basic(&Module::simple(&algebra, 1));
            assert!(AddClosureWitness::new(&m, &t).unwrap().is_none());
        }
    }

    // T + T is in add(T) and is not basic, so only from_module accepts it.
    // Its four summands match the two summands of T twice each.
    #[test]
    fn t_plus_t_lies_in_add_t_through_from_module() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let p0 = Module::projective(&algebra, 0);
            let p2 = Module::projective(&algebra, 2);
            let t_module = sum(&[&p0, &p2]);
            let t = basic(&t_module);
            let doubled = sum(&[&t_module, &t_module]);
            assert!(matches!(
                BasicDecomposition::new(&doubled).unwrap_err(),
                BasicError::NotBasic { .. }
            ));
            let witness = AddClosureWitness::from_module(&doubled, &t)
                .unwrap()
                .expect("T + T lies in add(T)");
            assert!(witness.verify());
            assert_eq!(witness.matches().len(), 4);
            let mut hits = [0usize; 2];
            for entry in witness.matches() {
                hits[entry.target_index()] += 1;
            }
            assert_eq!(hits, [2, 2], "over F_{}", field.modulus());
            assert!(witness.module().ptr_eq(&doubled));
        }
    }

    #[test]
    fn the_zero_module_lies_in_add_t() {
        let algebra = linear_an(3, f5());
        let t = basic(&Module::projective(&algebra, 0));
        let zero = Module::zero(&algebra);
        let witness = AddClosureWitness::from_module(&zero, &t)
            .unwrap()
            .expect("the zero module lies in add(T)");
        assert!(witness.verify());
        assert!(witness.matches().is_empty());
        let basic_zero = basic(&zero);
        let from_basic = AddClosureWitness::new(&basic_zero, &t)
            .unwrap()
            .expect("the zero module lies in add(T)");
        assert!(from_basic.verify());
    }

    #[test]
    fn a_tampered_add_closure_match_fails_verification() {
        let algebra = linear_an(3, f5());
        let p0 = Module::projective(&algebra, 0);
        let p2 = Module::projective(&algebra, 2);
        let t = basic(&sum(&[&p0, &p2]));
        let m = basic(&Module::projective(&algebra, 2));
        let mut witness = AddClosureWitness::new(&m, &t)
            .unwrap()
            .expect("P_2 is a summand of T");
        assert!(witness.verify());
        // Pointing the match at the other summand of T leaves the stored
        // isomorphism with the wrong endpoints.
        witness.matches[0].target_index = 1 - witness.matches[0].target_index;
        assert!(!witness.verify());
    }

    // Over the commutative square, add(P_0 + P_3) contains P_3 but not P_1.
    #[test]
    fn add_closure_holds_over_the_commutative_square() {
        for field in fields() {
            let algebra = commutative_square(field);
            let p0 = Module::projective(&algebra, 0);
            let p3 = Module::projective(&algebra, 3);
            let t = basic(&sum(&[&p0, &p3]));
            let inside = basic(&Module::projective(&algebra, 3));
            let outside = basic(&Module::projective(&algebra, 1));
            assert!(AddClosureWitness::new(&inside, &t).unwrap().is_some());
            assert!(AddClosureWitness::new(&outside, &t).unwrap().is_none());
        }
    }

    // Over k[x]/(x^3), add(k[x]/(x^3)) contains the regular module twice over
    // but not the simple k[x]/(x).
    #[test]
    fn add_closure_holds_over_truncated_poly_three() {
        for field in fields() {
            let algebra = truncated_poly(3, field).unwrap();
            let regular = Module::projective(&algebra, 0);
            let t = basic(&regular);
            let doubled = sum(&[&regular, &regular]);
            let witness = AddClosureWitness::from_module(&doubled, &t)
                .unwrap()
                .expect("the regular module doubled lies in add(T)");
            assert!(witness.verify());
            assert_eq!(witness.matches().len(), 2);
            let simple = basic(&Module::simple(&algebra, 0));
            assert!(AddClosureWitness::new(&simple, &t).unwrap().is_none());
        }
    }

    // D_4 pairs: the module halves agree and the projective halves differ,
    // then both halves agree.
    #[test]
    fn pair_identity_works_over_d4() {
        for field in fields() {
            let algebra = d4(field);
            let p0 = Module::projective(&algebra, 0);
            let s1 = Module::simple(&algebra, 1);
            let first = basic(&sum(&[&p0, &s1]));
            let second = basic(&sum(&[&s1, &p0]));
            let left = support(&algebra, &[2, 3]);
            let right = support(&algebra, &[3]);
            assert_eq!(
                expect_obstruction(pair_iso(&first, &left, &second, &right).unwrap()),
                SupportPairObstruction::ProjectiveSupport {
                    first: vec![2, 3],
                    second: vec![3]
                }
            );
            let witness = expect_witness(pair_iso(&first, &left, &second, &left).unwrap());
            assert!(witness.verify());
            assert_eq!(
                PairFingerprint::new(&first, &left).unwrap(),
                PairFingerprint::new(&second, &left).unwrap()
            );
        }
    }

    /// A xorshift64 generator, seeded by the caller so every basis change
    /// below is the same draw on every run and every platform.
    struct XorShift64(u64);

    impl XorShift64 {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn below(&mut self, n: u64) -> u64 {
            if n == 0 { 0 } else { self.next() % n }
        }
    }

    /// A `d` by `d` invertible matrix, built by elementary row operations on
    /// the identity, so it is invertible whatever the draws are.
    fn invertible(rng: &mut XorShift64, field: &PrimeField, d: usize) -> DenseMat {
        let mut g = DenseMat::identity(d);
        if d == 0 {
            return g;
        }
        for _ in 0..2 * d + 2 {
            let i = rng.below(d as u64) as usize;
            if d == 1 || rng.below(3) == 0 {
                let c = field.elem(1 + rng.below(field.modulus() - 1) as i64);
                for k in 0..d {
                    g.set(i, k, field.mul(g.get(i, k), c));
                }
                continue;
            }
            let j = (i + 1 + rng.below(d as u64 - 1) as usize) % d;
            if rng.below(2) == 0 {
                for k in 0..d {
                    let (a, b) = (g.get(i, k), g.get(j, k));
                    g.set(i, k, b);
                    g.set(j, k, a);
                }
            } else {
                let c = field.elem(rng.below(field.modulus()) as i64);
                for k in 0..d {
                    g.set(i, k, field.add(g.get(i, k), field.mul(c, g.get(j, k))));
                }
            }
        }
        g
    }

    /// `M'(a) = G_{s(a)} M(a) G_{t(a)}^{-1}` for one invertible `G_v` per
    /// vertex, so `M'` is isomorphic to `m` and carries other arrow matrices.
    fn basis_change(rng: &mut XorShift64, m: &Module) -> Module {
        let field = m.field();
        let quiver = m.algebra().quiver();
        let g: Vec<DenseMat> = m
            .dim_vector()
            .iter()
            .map(|&d| invertible(rng, &field, d))
            .collect();
        let g_inv: Vec<DenseMat> = g
            .iter()
            .map(|x| {
                x.inverse(&field)
                    .expect("elementary operations stay invertible")
            })
            .collect();
        let maps: Vec<DenseMat> = (0..quiver.num_arrows())
            .map(|i| {
                let a = ArrowId(i as u32);
                let (s, t) = (quiver.source(a) as usize, quiver.target(a) as usize);
                g[s].mul(m.map(a), &field).mul(&g_inv[t], &field)
            })
            .collect();
        Module::new(m.algebra().clone(), m.dim_vector().to_vec(), maps)
            .expect("a vertexwise basis change preserves the relations")
    }

    // Soundness of the prefilter, which the completeness certificate rests on.
    // `CatalogEnumeration::verify` skips the certified pair_iso test whenever
    // two fingerprints differ, so a fingerprint that separated two isomorphic
    // pairs would let a duplicate vertex through unseen.
    //
    // `isomorphic_pairs_have_equal_fingerprints` cannot catch that: it builds
    // both sides from the same two Module values, and PairFingerprint::new
    // sorts its summand records, so that test passes even when every invariant
    // is computed wrongly. This one rebuilds each module part in another basis.
    // `M'(a) = G_{s(a)} M(a) G_{t(a)}^{-1}` is isomorphic to `M` and carries
    // other arrow matrices, so an invariant computed from the matrices rather
    // than from the isomorphism class moves and the fingerprints separate.
    //
    // The 50 D_4 pairs are the fixture the design's selectivity claim is
    // stated on (section 4: 50 of 2500 comparisons admitted on D_4).
    #[test]
    fn the_fingerprint_is_constant_on_isomorphism_classes() {
        let field = f5();
        let algebra = d4(field);
        let catalog = IndecomposableCatalog::dynkin(&algebra).expect("D_4 is Dynkin");
        let enumeration = enumerate_over_catalog(&catalog).expect("D_4 enumerates");
        assert_eq!(enumeration.len(), 50);

        let mut rng = XorShift64(0x5eed_0005_0005_0001);
        let mut fingerprints = Vec::with_capacity(enumeration.len());
        let mut moved = 0;
        for pair in enumeration.pairs() {
            let before = PairFingerprint::new(pair.module(), &pair.projective()).unwrap();
            let module = pair.module().module();
            let rebuilt = basis_change(&mut rng, module);
            let decomposition =
                BasicDecomposition::new(&rebuilt).expect("a basis change keeps the module basic");
            let after = PairFingerprint::new(&decomposition, &pair.projective()).unwrap();
            assert_eq!(
                before,
                after,
                "the fingerprint moved under a basis change of {:?}",
                pair.module().dim_vectors()
            );
            let arrows = 0..algebra.quiver().num_arrows();
            let same: Vec<bool> = arrows
                .map(|i| {
                    let a = ArrowId(i as u32);
                    rebuilt.map(a) == module.map(a)
                })
                .collect();
            if same.iter().all(|&s| s) {
                // Nothing moved, so this pair carries no evidence. Every arrow
                // of D_4 runs from the center to a leaf, so a module part with
                // a zero dimension at the center or at every leaf has only
                // empty arrow matrices and no basis change can act on it.
                for i in 0..algebra.quiver().num_arrows() {
                    let matrix = module.map(ArrowId(i as u32));
                    assert!(
                        matrix.rows() == 0 || matrix.cols() == 0,
                        "a nonempty arrow matrix survived the basis change in {:?}",
                        pair.module().dim_vectors()
                    );
                }
            } else {
                moved += 1;
            }
            fingerprints.push(before);
        }
        // The 9 unmoved module parts are the 8 sums of the leaf simples S_1,
        // S_2, S_3 (the empty sum included) and S_0 on its own. The seed fixes
        // which basis change each of the other 41 got.
        assert_eq!(moved, 41);

        // The design's selectivity claim, section 4: on D_4 the prefilter
        // admits only self-matches, 50 of the 50 * 50 ordered comparisons.
        let mut admitted = 0;
        for (i, left) in fingerprints.iter().enumerate() {
            for (j, right) in fingerprints.iter().enumerate() {
                if left == right {
                    admitted += 1;
                    assert_eq!(i, j, "pairs {i} and {j} share a fingerprint");
                }
            }
        }
        assert_eq!(admitted, 50);
    }

    // Residue degree is the one fingerprint field that needs a division ring
    // larger than the prime field to say anything, and `docs/v0.5-design.md`
    // section 8 rests field generality on exactly that. Both modules here are
    // Kronecker representations `(I_3, B)` over F_2 with dimension vector
    // [3, 3]:
    //
    // - W takes B the companion matrix of x^3 + x + 1, irreducible over F_2,
    //   so End(W) = F_2[B] is the field F_8 and the residue degree is 3. Same
    //   module as `arquiver::tests::f8_module`, `indec.rs`, and `approx.rs`.
    // - J takes B the nilpotent Jordan block of size 3, so End(J) = F_2[B] is
    //   F_2[x]/(x^3), local with residue field F_2 and residue degree 1.
    //
    // Both have End of F_2 dimension 3, and the first arrow acts invertibly in
    // both, so both have Loewy length 2, top [3, 0], and socle [0, 3]. The Hom
    // profiles against the simples agree too. Residue degree is the only field
    // that separates them.
    #[test]
    fn the_fingerprint_separates_on_residue_degree() {
        let field = f2();
        let algebra = kronecker(2, field);
        let mut companion = DenseMat::zero(3, 3);
        companion.set(0, 1, field.one());
        companion.set(1, 2, field.one());
        companion.set(2, 0, field.one());
        companion.set(2, 1, field.one());
        let w = Module::new(
            algebra.clone(),
            vec![3, 3],
            vec![DenseMat::identity(3), companion],
        )
        .expect("a Kronecker representation is a module");
        let mut jordan = DenseMat::zero(3, 3);
        jordan.set(0, 1, field.one());
        jordan.set(1, 2, field.one());
        let j = Module::new(
            algebra.clone(),
            vec![3, 3],
            vec![DenseMat::identity(3), jordan],
        )
        .expect("a Kronecker representation is a module");

        let empty = support(&algebra, &[]);
        let f8 = PairFingerprint::new(&basic(&w), &empty).unwrap();
        let f2_residue = PairFingerprint::new(&basic(&j), &empty).unwrap();
        let (left, right) = (&f8.summands()[0], &f2_residue.summands()[0]);
        assert_eq!(left.residue_degree(), 3);
        assert_eq!(right.residue_degree(), 1);
        assert_ne!(f8, f2_residue, "residue degree is the separating field");

        // Every other field agrees, so nothing else could have separated them.
        assert_eq!(left.dim_vector(), right.dim_vector());
        assert_eq!(left.dim_vector(), &[3, 3]);
        assert_eq!(left.loewy_length(), right.loewy_length());
        assert_eq!(left.loewy_length(), 2);
        assert_eq!(left.top_dim_vector(), right.top_dim_vector());
        assert_eq!(left.top_dim_vector(), &[3, 0]);
        assert_eq!(left.socle_dim_vector(), right.socle_dim_vector());
        assert_eq!(left.socle_dim_vector(), &[0, 3]);
        assert_eq!(left.end_dim(), right.end_dim());
        assert_eq!(left.end_dim(), 3);
        assert_eq!(left.hom_from_simples(), right.hom_from_simples());
        assert_eq!(left.hom_from_simples(), &[0, 3]);
        assert_eq!(left.hom_to_simples(), right.hom_to_simples());
        assert_eq!(left.hom_to_simples(), &[3, 0]);
    }
}
