//! Projectively trivial maps, stable Hom, the AR socle construction, and
//! witnessed almost-split sequences.
//!
//! Factorization lemma: a map `f: M -> N` factors through some projective
//! module exactly when it factors through the projective cover
//! `pi_N: P(N) -> N`. Proof: take `f = a.then(b)` with projective middle `Q`.
//! Then `b: Q -> N` lifts through the epi `pi_N` because `Q` is projective,
//! giving `b = b'.then(pi_N)` and `f = (a.then(b')).then(pi_N)`. So the
//! projectively trivial subspace of `Hom(M, N)` is the image of
//! `Hom(M, P(N)) -> Hom(M, N)`, `h -> h.then(pi_N)`, and [`stable_hom`] is the
//! quotient of `Hom(M, N)` by that image.
//!
//! `End(M)` acts on `Ext^1(M, tau M)` on the left, equivalently as a right
//! `End(M)^op` action. For `phi` in `End(M)`, lift `phi` over the minimal
//! resolution of `M`: `phi_0: P_0 -> P_0` with `phi_0.then(aug) = aug.then(phi)`,
//! then `phi_1: P_1 -> P_1` with `phi_1.then(d_1) = d_1.then(phi_0)`. The
//! action on the class of a representative cocycle `c: P_1 -> tau M` is the
//! class of `phi_1.then(c)`. Writing `A_phi` for the matrix of that map in the
//! fixed Ext basis, `Ext^1(-, tau M)` is contravariant, so
//! `A_{phi.then(psi)} = A_psi A_phi`: the assignment reverses the crate's
//! diagrammatic product and is an anti-representation, not a representation.
//!
//! The socle is unaffected, which is why the crate keeps the left action.
//! `rad End(M)` is a two-sided ideal, so its left and right annihilators in
//! `Ext^1(M, tau M)` are the same set, and the kernel of the stacked action
//! matrices is that set either way. No computed value depends on the side.
//!
//! A projectively trivial endomorphism acts as zero, because `Ext^1(P, -) = 0`,
//! so the action factors through [`stable_end`]. Every lift solves its systems
//! with free variables zeroed, so the action matrices are deterministic in the
//! fixed Ext basis.
//!
//! Socle criterion (Auslander, Reiten, and Smalo, "Representation Theory of
//! Artin Algebras", IV.2 with V.2). Let `M` be indecomposable and
//! non-projective over an Artin algebra. Then `Ext^1(M, tau M)` is dual to the
//! stable endomorphism algebra of `M`, which here means [`stable_end`]:
//! `End(M)` modulo the maps that factor through a projective. The duality is
//! natural in both arguments, and the nonzero elements of the socle of
//! `Ext^1(M, tau M)` as an `End(M)`-module are exactly the almost-split
//! classes. The socle is the annihilator of `rad End(M)`, one set on either
//! side, as the paragraph above records. Naturality is what turns annihilation
//! by `rad End(M)` into the right-almost-split lifting property; the argument
//! is cited, not re-proved in code. The code checks the hypotheses, namely the
//! [`IndecomposableModule`] gate, the projectivity cross-check, and the two
//! dimension gates of the duality. The theorem supplies the almost-split
//! property itself.
//!
//! The chosen class is the first RREF row of the socle: deterministic, not
//! canonical. When the residue degree `d` of `M` exceeds 1, the socle has
//! dimension `d` over `F_p` and no basis-independent preferred element exists.
//! With the end terms fixed, distinct nonzero socle classes are inequivalent
//! as extensions. Their sequences are isomorphic after suitable automorphisms
//! of the end terms, so the almost-split sequence is unique up to isomorphism
//! of sequences. Nothing in the crate calls the chosen class canonical.

use std::fmt;
use std::sync::Arc;

use crate::ar::{TauError, tau};
use crate::arquiver::{ArQuiverError, IndecomposableCatalog, category_radical};
use crate::decompose::add_morphisms;
use crate::ext::{ExtClass, ExtClassError, ExtSpace, lift_through};
use crate::field::{Fp, PrimeField};
use crate::hom::{HomError, Morphism, hom, zero_morphism};
use crate::homspace::{
    HomQuotient, HomSpace, HomSpaceError, HomSubspace, row_times, scale_morphism,
};
use crate::indec::{IndecError, IndecomposableModule};
use crate::iso::{IsoOutcome, is_isomorphic};
use crate::linalg::DenseMat;
use crate::module::Module;
use crate::resolution::projective_cover;
use crate::sequence::{NonSplitWitness, SequenceError, ShortExactSequence, SplitStatus};

/// A failed internal cross-check of the almost-split layer. Every variant
/// signals a crate defect: the construction checked a consequence of a
/// theorem whose hypotheses hold, and the check failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefectKind {
    /// `dim Ext^1(M, tau M)` differs from `dim stable End(M)`.
    DualityDimensionMismatch {
        /// `dim_Fp Ext^1(M, tau M)`.
        ext_dim: usize,
        /// `dim_Fp stable End(M)`.
        stable_end_dim: usize,
    },
    /// The dimension of the Ext socle differs from the residue degree of
    /// `M`.
    SocleDimensionMismatch {
        /// `dim_Fp` of the socle kernel.
        socle_dim: usize,
        /// The residue degree of `End(M)`.
        residue_degree: usize,
    },
    /// The minimal-resolution projectivity test and the AR translate
    /// disagree on whether `M` is projective.
    ProjectivityDisagreement {
        /// What the minimal resolution says.
        resolution_projective: bool,
        /// Whether `tau` returned zero.
        tau_zero: bool,
    },
    /// The sequence built from a nonzero chosen class came out split.
    NonzeroClassSplit,
    /// `im(Hom(X, E) -> Hom(X, M))` differs from `rad(X, M)` at this
    /// catalog entry.
    RightFactorizationMismatch {
        /// The catalog index of `X`.
        entry: usize,
    },
    /// `im(Hom(E, X) -> Hom(tau M, X))` differs from `rad(tau M, X)` at
    /// this catalog entry.
    LeftFactorizationMismatch {
        /// The catalog index of `X`.
        entry: usize,
    },
}

impl fmt::Display for DefectKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DualityDimensionMismatch {
                ext_dim,
                stable_end_dim,
            } => write!(
                f,
                "Ext^1(M, tau M) has dimension {ext_dim}, stable End(M) has dimension \
                 {stable_end_dim}; crate defect"
            ),
            Self::SocleDimensionMismatch {
                socle_dim,
                residue_degree,
            } => write!(
                f,
                "the Ext socle has dimension {socle_dim}, the residue degree is \
                 {residue_degree}; crate defect"
            ),
            Self::ProjectivityDisagreement {
                resolution_projective,
                tau_zero,
            } => write!(
                f,
                "the resolution route reports projective = {resolution_projective}, tau \
                 reports zero = {tau_zero}; crate defect"
            ),
            Self::NonzeroClassSplit => {
                f.write_str("the sequence of a nonzero chosen class splits; crate defect")
            }
            Self::RightFactorizationMismatch { entry } => write!(
                f,
                "the image of Hom(X, E) in Hom(X, M) differs from rad(X, M) at catalog \
                 entry {entry}; crate defect"
            ),
            Self::LeftFactorizationMismatch { entry } => write!(
                f,
                "the image of Hom(E, X) in Hom(tau M, X) differs from rad(tau M, X) at \
                 catalog entry {entry}; crate defect"
            ),
        }
    }
}

/// Rejected input, a failed dependency, or a failed internal cross-check of
/// the almost-split layer.
#[derive(Clone, Debug)]
pub enum AlmostSplitError {
    /// The AR translate could not be computed or cross-checked.
    Tau(TauError),
    /// The translate failed the indecomposability gate. The theorem makes
    /// this a defect in practice; the variant keeps the gate's own report.
    TauIndecomposability(IndecError),
    /// Two modules do not share one algebra, or a composite was formed from
    /// mismatched endpoints.
    Hom(HomError),
    /// A morphism or subspace did not match the endpoints of its Hom space.
    Space(HomSpaceError),
    /// An Ext class operation rejected its input.
    Ext(ExtClassError),
    /// Building or reading a short exact sequence failed.
    Sequence(SequenceError),
    /// The category radical rejected its input.
    Radical(ArQuiverError),
    /// A failed internal cross-check; see [`DefectKind`].
    Defect(DefectKind),
}

impl fmt::Display for AlmostSplitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tau(error) => write!(f, "the AR translate failed: {error}"),
            Self::TauIndecomposability(error) => {
                write!(
                    f,
                    "the translate failed the indecomposability gate: {error}"
                )
            }
            Self::Hom(error) => write!(f, "morphism rejected: {error}"),
            Self::Space(error) => write!(f, "hom space rejected the input: {error}"),
            Self::Ext(error) => write!(f, "Ext class rejected the input: {error}"),
            Self::Sequence(error) => write!(f, "short exact sequence rejected: {error}"),
            Self::Radical(error) => write!(f, "category radical failed: {error}"),
            Self::Defect(kind) => write!(f, "internal cross-check failed: {kind}"),
        }
    }
}

impl std::error::Error for AlmostSplitError {}

impl From<TauError> for AlmostSplitError {
    fn from(error: TauError) -> AlmostSplitError {
        AlmostSplitError::Tau(error)
    }
}

impl From<IndecError> for AlmostSplitError {
    fn from(error: IndecError) -> AlmostSplitError {
        AlmostSplitError::TauIndecomposability(error)
    }
}

impl From<HomError> for AlmostSplitError {
    fn from(error: HomError) -> AlmostSplitError {
        AlmostSplitError::Hom(error)
    }
}

impl From<HomSpaceError> for AlmostSplitError {
    fn from(error: HomSpaceError) -> AlmostSplitError {
        AlmostSplitError::Space(error)
    }
}

impl From<ExtClassError> for AlmostSplitError {
    fn from(error: ExtClassError) -> AlmostSplitError {
        AlmostSplitError::Ext(error)
    }
}

impl From<SequenceError> for AlmostSplitError {
    fn from(error: SequenceError) -> AlmostSplitError {
        AlmostSplitError::Sequence(error)
    }
}

impl From<ArQuiverError> for AlmostSplitError {
    fn from(error: ArQuiverError) -> AlmostSplitError {
        AlmostSplitError::Radical(error)
    }
}

/// The subspace of maps in `space` that factor through a projective module.
///
/// By the factorization lemma of the module docs, `f: M -> N` factors through
/// a projective exactly when it factors through the projective cover
/// `pi_N: P(N) -> N`. So the subspace is the image of
/// `Hom(M, P(N)) -> Hom(M, N)`, `h -> h.then(pi_N)`, and one composition per
/// basis element of `Hom(M, P(N))` computes it.
pub fn projectively_trivial(space: &HomSpace) -> Result<HomSubspace, AlmostSplitError> {
    let (cover, pi) = projective_cover(space.target());
    let through = hom(space.source(), &cover)?;
    let composites: Vec<Morphism> = through
        .iter()
        .map(|h| h.then(&pi))
        .collect::<Result<_, _>>()?;
    Ok(space.subspace(&composites)?)
}

/// `Hom(M, N)` modulo the projectively trivial maps, with the deterministic
/// complement representatives of [`HomQuotient`].
///
/// # Errors
/// [`AlmostSplitError::Hom`] when the modules do not share one algebra.
pub fn stable_hom(m: &Module, n: &Module) -> Result<HomQuotient, AlmostSplitError> {
    let space = HomSpace::new(m, n)?;
    let trivial = projectively_trivial(&space)?;
    Ok(space.full_subspace().quotient_by(&trivial)?)
}

/// `stable_hom(m, m)`: the stable endomorphism algebra of `m` as a vector
/// space.
pub fn stable_end(m: &Module) -> Result<HomQuotient, AlmostSplitError> {
    stable_hom(m, m)
}

/// The matrix `A_phi` of `Ext^1(phi, N)` in the fixed Ext basis of
/// `space = Ext^1(M, N)`, for `phi` an endomorphism of `M`: row `i` holds the
/// coordinates of the image of basis class `i`, computed through the chain
/// lifts of the module docs.
///
/// The functor is contravariant, so `A_{phi.then(psi)} = A_psi A_phi`. Every
/// lift solves its systems with zeroed free variables, so the matrix is
/// deterministic.
fn action_matrix(space: &ExtSpace, phi: &Morphism) -> Result<DenseMat, AlmostSplitError> {
    let d = space.dim();
    if d == 0 {
        return Ok(DenseMat::zero(0, 0));
    }
    let res = space.resolution();
    let rhs0 = res.augmentation.then(phi)?;
    let phi0 = lift_through(&res.terms[0], &res.augmentation, &rhs0);
    let d1 = &res.maps[0];
    let rhs1 = d1.then(&phi0)?;
    let phi1 = lift_through(&res.terms[1], d1, &rhs1);
    let mut a = DenseMat::zero(d, d);
    for (i, rep) in space.representatives().iter().enumerate() {
        let moved = phi1.then(rep)?;
        let class = space.class_from_cocycle(&moved)?;
        for (c, &v) in class.coordinates().iter().enumerate() {
            a.set(i, c, v);
        }
    }
    Ok(a)
}

/// One [`action_matrix`] per radical basis element of `End(M)`, in radical
/// basis order, over `space = Ext^1(M, tau M)`.
fn action_matrices(
    m: &IndecomposableModule,
    space: &ExtSpace,
) -> Result<Vec<DenseMat>, AlmostSplitError> {
    let endo = m.endo();
    let radical = endo.radical_basis();
    (0..radical.rows())
        .map(|j| action_matrix(space, &endo.morphism(radical.row(j))))
        .collect()
}

/// The RREF basis of `{ e : e . r_j = 0 for every j }`: the left kernel of
/// the horizontally stacked action matrices. With no radical elements the
/// socle is the whole space.
fn socle_kernel(action: &[DenseMat], dim: usize, field: &PrimeField) -> DenseMat {
    let mut stacked = DenseMat::zero(dim, dim * action.len());
    for (j, a) in action.iter().enumerate() {
        for r in 0..dim {
            for c in 0..dim {
                stacked.set(r, j * dim + c, a.get(r, c));
            }
        }
    }
    stacked.left_kernel_basis(field).into_row_space_basis(field)
}

/// The morphism with the given coordinates over the RREF basis of `sub`, or
/// `None` on a length mismatch.
fn subspace_combination(sub: &HomSubspace, coords: &[Fp]) -> Option<Morphism> {
    if coords.len() != sub.dim() {
        return None;
    }
    let mut acc = zero_morphism(sub.source(), sub.target())
        .expect("a subspace's endpoints share one algebra");
    for (k, &c) in coords.iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        acc = add_morphisms(&acc, &scale_morphism(&sub.basis_morphism(k), c));
    }
    Some(acc)
}

/// The outcome of [`almost_split`]. A projective module has no almost-split
/// sequence ending at it, which is an outcome, not an error.
// An outcome is built once and matched once, so the size gap between the
// variants never costs a hot copy.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum AlmostSplitOutcome {
    /// The module is projective, so no almost-split sequence ends at it.
    Projective,
    /// The almost-split sequence ending at the module, with its witness.
    Sequence(AlmostSplitSequence),
}

/// An almost-split sequence `0 -> tau M -> E -> M -> 0` with the chosen AR
/// class it realizes and the witness that gates the claim.
///
/// Fields are private; construction goes through [`almost_split`] or
/// [`almost_split_via_catalog`], so every value passed the socle
/// construction and its internal gates.
#[derive(Clone, Debug)]
pub struct AlmostSplitSequence {
    sequence: ShortExactSequence,
    class: ExtClass,
    witness: AlmostSplitWitness,
}

impl AlmostSplitSequence {
    /// The sequence `0 -> tau M -> E -> M -> 0`.
    #[inline]
    pub fn sequence(&self) -> &ShortExactSequence {
        &self.sequence
    }

    /// The chosen AR class: the first RREF row of the Ext socle.
    ///
    /// The class is deterministic, not canonical. Any nonzero socle element
    /// gives an almost-split sequence isomorphic to this one after suitable
    /// automorphisms of the end terms. With the end terms fixed, distinct
    /// socle classes are inequivalent extensions.
    #[inline]
    pub fn chosen_ar_class(&self) -> &ExtClass {
        &self.class
    }

    /// The witness behind the almost-split claim.
    #[inline]
    pub fn witness(&self) -> &AlmostSplitWitness {
        &self.witness
    }

    /// Rechecks the AR duality witness against `m`, with the sequence and
    /// class this value holds.
    ///
    /// Returns false when the value carries the catalog witness instead; that
    /// route is [`AlmostSplitSequence::verify_with_catalog`]. See
    /// [`ArDualityWitness::verify`] for what is rechecked.
    pub fn verify(&self, m: &IndecomposableModule) -> bool {
        match &self.witness {
            AlmostSplitWitness::ArDuality(witness) => {
                witness.verify(m, &self.sequence, &self.class)
            }
            AlmostSplitWitness::ExhaustiveCatalog(_) => false,
        }
    }

    /// Rechecks the catalog witness against `m` and `catalog`, with the
    /// sequence and class this value holds.
    ///
    /// Returns false when the value carries the AR duality witness instead;
    /// that route is [`AlmostSplitSequence::verify`]. See
    /// [`CatalogWitness::verify`] for what is rechecked.
    pub fn verify_with_catalog(
        &self,
        m: &IndecomposableModule,
        catalog: &IndecomposableCatalog,
    ) -> bool {
        match &self.witness {
            AlmostSplitWitness::ExhaustiveCatalog(witness) => {
                witness.verify(m, catalog, &self.sequence, &self.class)
            }
            AlmostSplitWitness::ArDuality(_) => false,
        }
    }
}

/// Which route certified the sequence.
#[derive(Clone, Debug)]
pub enum AlmostSplitWitness {
    /// The AR duality route of [`almost_split`].
    ArDuality(ArDualityWitness),
    /// The exhaustive catalog route of [`almost_split_via_catalog`].
    ExhaustiveCatalog(CatalogWitness),
}

/// The stored data of the AR duality route: enough to recheck every gate of
/// the socle construction from the live modules.
#[derive(Clone, Debug)]
pub struct ArDualityWitness {
    // RREF coordinates of a basis of rad End(M), one element per row.
    radical_coords: DenseMat,
    // Coordinates of class . r_j per radical basis element, all zero.
    action_traces: Vec<Vec<Fp>>,
    // RREF basis of the socle kernel.
    socle_rref: DenseMat,
    // Index of the chosen socle row; the construction always picks 0.
    chosen_row: usize,
    ext_dim: usize,
    stable_end_dim: usize,
    socle_dim: usize,
    residue_degree: usize,
    non_split: NonSplitWitness,
}

impl ArDualityWitness {
    /// RREF coordinates of the stored `rad End(M)` basis, one element per
    /// row.
    #[inline]
    pub fn radical_basis_coords(&self) -> &DenseMat {
        &self.radical_coords
    }

    /// The coordinates of `class . r_j` per radical basis element; every
    /// entry is zero.
    #[inline]
    pub fn action_traces(&self) -> &[Vec<Fp>] {
        &self.action_traces
    }

    /// The RREF basis of the socle kernel.
    #[inline]
    pub fn socle_rref(&self) -> &DenseMat {
        &self.socle_rref
    }

    /// The index of the chosen socle row, always 0. The choice is
    /// deterministic, not canonical, and [`ArDualityWitness::verify`] rejects
    /// any other row.
    #[inline]
    pub fn chosen_row(&self) -> usize {
        self.chosen_row
    }

    /// The stored `dim_Fp Ext^1(M, tau M)`.
    #[inline]
    pub fn ext_dim(&self) -> usize {
        self.ext_dim
    }

    /// The stored `dim_Fp stable End(M)`.
    #[inline]
    pub fn stable_end_dim(&self) -> usize {
        self.stable_end_dim
    }

    /// The stored socle dimension.
    #[inline]
    pub fn socle_dim(&self) -> usize {
        self.socle_dim
    }

    /// The stored residue degree of `End(M)`.
    #[inline]
    pub fn residue_degree(&self) -> usize {
        self.residue_degree
    }

    /// The proof that the sequence does not split.
    #[inline]
    pub fn non_split(&self) -> &NonSplitWitness {
        &self.non_split
    }

    /// Rechecks the witness against the live modules.
    ///
    /// The recheck takes nothing on trust, starting with the class's own
    /// [`ExtSpace`]. Every other check reads that space, so a tampered
    /// resolution, cocycle basis, coboundary basis, complement, or
    /// representative would otherwise certify itself;
    /// [`ExtSpace::matches_recomputation`] rebuilds all of it from the live
    /// endpoint modules and compares. The checks are:
    ///
    /// - The class's space equals a fresh recomputation, field by field.
    /// - The AR translate, recomputed through the certified double route, is
    ///   isomorphic to the space's target and passes the indecomposability
    ///   gate.
    /// - The stored radical basis equals the live `rad End(M)` basis, and the
    ///   action matrices are recomputed from it.
    /// - The recomputed socle kernel equals the stored RREF, and every stored
    ///   socle row annihilates every action matrix.
    /// - The chosen row is row 0, the row the construction always picks, and
    ///   it carries the class's coordinates; the class is nonzero.
    /// - The stored action traces equal fresh products and are all zero.
    /// - The two dimension equalities hold against fresh computations.
    /// - The sequence is exact through the [`ShortExactSequence`] constructor
    ///   and recovers the class.
    /// - [`NonSplitWitness::verify`] passes.
    ///
    /// The sequence and class are the caller's, not this witness's own. For
    /// the pair the almost-split value holds, call
    /// [`AlmostSplitSequence::verify`].
    pub fn verify(
        &self,
        m: &IndecomposableModule,
        sequence: &ShortExactSequence,
        class: &ExtClass,
    ) -> bool {
        let space = class.space();
        if space.degree() != 1
            || !space.source().ptr_eq(m.module())
            || !sequence.quotient().ptr_eq(space.source())
            || !sequence.sub().ptr_eq(space.target())
            || !space.matches_recomputation()
        {
            return false;
        }
        // The construction uses tau(m) as the Ext space target, and the
        // recomputed translate is a fresh module value. So the comparison has
        // to be a certified isomorphism, not pointer identity. An Unknown
        // outcome fails verification.
        let Ok(translate) = tau(m.module()) else {
            return false;
        };
        if IndecomposableModule::new(&translate).is_err() {
            return false;
        }
        match is_isomorphic(&translate, space.target()) {
            Ok(IsoOutcome::Isomorphic(_)) => {}
            _ => return false,
        }
        let field = m.module().field();
        if self.radical_coords != *m.endo().radical_basis() {
            return false;
        }
        let d = space.dim();
        if self.ext_dim != d || self.ext_dim != self.stable_end_dim {
            return false;
        }
        let Ok(stable) = stable_end(m.module()) else {
            return false;
        };
        if stable.dim() != self.stable_end_dim {
            return false;
        }
        if self.socle_dim != self.socle_rref.rows()
            || self.residue_degree != m.residue_degree()
            || self.socle_dim != self.residue_degree
        {
            return false;
        }
        let Ok(action) = action_matrices(m, space) else {
            return false;
        };
        if socle_kernel(&action, d, &field) != self.socle_rref {
            return false;
        }
        for r in 0..self.socle_rref.rows() {
            for a in &action {
                if row_times(self.socle_rref.row(r), a, &field)
                    .iter()
                    .any(|v| !v.is_zero())
                {
                    return false;
                }
            }
        }
        // Row 0 is the crate's choice, and the determinism fingerprint pins
        // its coordinates. Another socle row would give an almost-split
        // sequence too, but not this crate's, so it is rejected here.
        if self.chosen_row != 0
            || self.socle_rref.rows() == 0
            || class.coordinates() != self.socle_rref.row(0)
            || class.is_zero()
        {
            return false;
        }
        if self.action_traces.len() != action.len() {
            return false;
        }
        for (trace, a) in self.action_traces.iter().zip(&action) {
            if *trace != row_times(class.coordinates(), a, &field)
                || trace.iter().any(|v| !v.is_zero())
            {
                return false;
            }
        }
        if ShortExactSequence::new(sequence.inclusion().clone(), sequence.projection().clone())
            .is_err()
        {
            return false;
        }
        match sequence.ext1_class(space) {
            Ok(recovered) => {
                if recovered.equals(class) != Ok(true) {
                    return false;
                }
            }
            Err(_) => return false,
        }
        self.non_split.verify(sequence)
    }
}

/// The stored factorization data of one catalog entry `X`.
///
/// Right side, through `g: E -> M`: coordinates that express each radical
/// basis map of `rad(X, M)` over the image of `Hom(X, E) -> Hom(X, M)`, and
/// coordinates that place each composite `h_i.then(g)` inside `rad(X, M)`.
/// Left side, through `f: tau M -> E`: the same two families for
/// `Hom(E, X) -> Hom(tau M, X)` against `rad(tau M, X)`.
///
/// The left side is provably redundant, not redundant by assumed symmetry.
/// Theorem (Auslander, Reiten, and Smalo V.1.14): for a non-split short exact
/// sequence with indecomposable end terms, right almost split, left almost
/// split, and almost split are equivalent. The right-side equality over an
/// exhaustive catalog already proves `g` right almost split, and both ends are
/// [`IndecomposableModule`] values, so the left side follows. It is computed
/// and stored anyway, because redundant independent routes are this crate's
/// house style.
#[derive(Clone, Debug)]
pub struct CatalogEntryCheck {
    right_factorizations: Vec<Vec<Fp>>,
    right_memberships: Vec<Vec<Fp>>,
    left_factorizations: Vec<Vec<Fp>>,
    left_memberships: Vec<Vec<Fp>>,
}

impl CatalogEntryCheck {
    /// Coordinates of each `rad(X, M)` basis map over the RREF basis of
    /// `im(Hom(X, E) -> Hom(X, M))`, in radical basis order.
    #[inline]
    pub fn right_factorizations(&self) -> &[Vec<Fp>] {
        &self.right_factorizations
    }

    /// Coordinates of each composite `h_i.then(g)` over the RREF basis of
    /// `rad(X, M)`, in `Hom(X, E)` basis order.
    #[inline]
    pub fn right_memberships(&self) -> &[Vec<Fp>] {
        &self.right_memberships
    }

    /// Coordinates of each `rad(tau M, X)` basis map over the RREF basis of
    /// `im(Hom(E, X) -> Hom(tau M, X))`, in radical basis order.
    #[inline]
    pub fn left_factorizations(&self) -> &[Vec<Fp>] {
        &self.left_factorizations
    }

    /// Coordinates of each composite `f.then(h_i)` over the RREF basis of
    /// `rad(tau M, X)`, in `Hom(E, X)` basis order.
    #[inline]
    pub fn left_memberships(&self) -> &[Vec<Fp>] {
        &self.left_memberships
    }
}

/// The stored data of the exhaustive catalog route: one
/// [`CatalogEntryCheck`] per catalog entry, in catalog order.
///
/// The right-side equality at the entry `X = M` already proves the sequence
/// non-split. `End(M)` is local, so the identity of `M` is not in
/// `rad(M, M)`, and therefore it does not factor through `g`.
#[derive(Clone, Debug)]
pub struct CatalogWitness {
    entries: Vec<CatalogEntryCheck>,
}

/// The per-entry subspaces and composites that the construction and the
/// verification both recompute and compare against.
struct EntryRecompute {
    image: HomSubspace,
    rad: HomSubspace,
    composites: Vec<Morphism>,
    left_image: HomSubspace,
    left_rad: HomSubspace,
    left_composites: Vec<Morphism>,
}

fn recompute_entry(
    m: &IndecomposableModule,
    tau_ind: &IndecomposableModule,
    sequence: &ShortExactSequence,
    x: &IndecomposableModule,
) -> Result<EntryRecompute, AlmostSplitError> {
    let g = sequence.projection();
    let f = sequence.inclusion();
    let hom_xe = hom(x.module(), sequence.middle())?;
    let composites: Vec<Morphism> = hom_xe.iter().map(|h| h.then(g)).collect::<Result<_, _>>()?;
    let space_xm = HomSpace::new(x.module(), m.module())?;
    let image = space_xm.subspace(&composites)?;
    let rad = category_radical(x, m)?;
    let hom_ex = hom(sequence.middle(), x.module())?;
    let left_composites: Vec<Morphism> =
        hom_ex.iter().map(|h| f.then(h)).collect::<Result<_, _>>()?;
    let space_tx = HomSpace::new(sequence.sub(), x.module())?;
    let left_image = space_tx.subspace(&left_composites)?;
    let left_rad = category_radical(tau_ind, x)?;
    Ok(EntryRecompute {
        image,
        rad,
        composites,
        left_image,
        left_rad,
        left_composites,
    })
}

impl CatalogWitness {
    /// The per-entry factorization data, in catalog order.
    #[inline]
    pub fn entry_checks(&self) -> &[CatalogEntryCheck] {
        &self.entries
    }

    /// Rechecks the witness against the live modules, for every catalog entry
    /// and in both directions.
    ///
    /// The stored coordinates are re-solved, not replayed: the image subspaces
    /// and the category radicals are recomputed, their equality is rechecked,
    /// and every stored factorization and membership vector must rebuild its
    /// morphism over the recomputed RREF basis. The class's [`ExtSpace`] is
    /// rebuilt and compared by [`ExtSpace::matches_recomputation`], because
    /// the class recovery below reduces against its stored bases. The sequence
    /// is also rechecked for exactness through the [`ShortExactSequence`]
    /// constructor, for recovery of the supplied class, and for
    /// indecomposability of the sub module. The whole recheck is
    /// deterministic.
    ///
    /// The sequence and class are the caller's, not this witness's own. For
    /// the pair the almost-split value holds, call
    /// [`AlmostSplitSequence::verify_with_catalog`].
    pub fn verify(
        &self,
        m: &IndecomposableModule,
        catalog: &IndecomposableCatalog,
        sequence: &ShortExactSequence,
        class: &ExtClass,
    ) -> bool {
        if !Arc::ptr_eq(m.module().algebra(), catalog.algebra())
            || self.entries.len() != catalog.len()
        {
            return false;
        }
        let space = class.space();
        if space.degree() != 1
            || !space.source().ptr_eq(m.module())
            || !sequence.quotient().ptr_eq(space.source())
            || !sequence.sub().ptr_eq(space.target())
            || class.is_zero()
            || !space.matches_recomputation()
        {
            return false;
        }
        if ShortExactSequence::new(sequence.inclusion().clone(), sequence.projection().clone())
            .is_err()
        {
            return false;
        }
        match sequence.ext1_class(space) {
            Ok(recovered) => {
                if recovered.equals(class) != Ok(true) {
                    return false;
                }
            }
            Err(_) => return false,
        }
        let Ok(tau_ind) = IndecomposableModule::new(sequence.sub()) else {
            return false;
        };
        for (check, x) in self.entries.iter().zip(catalog.entries()) {
            let Ok(EntryRecompute {
                image,
                rad,
                composites,
                left_image,
                left_rad,
                left_composites,
            }) = recompute_entry(m, &tau_ind, sequence, x)
            else {
                return false;
            };
            if image != rad || left_image != left_rad {
                return false;
            }
            let radical_maps = |rad: &HomSubspace| -> Vec<Morphism> {
                (0..rad.dim()).map(|i| rad.basis_morphism(i)).collect()
            };
            let ok = family_solves(&check.right_factorizations, &image, &radical_maps(&rad))
                && family_solves(&check.right_memberships, &rad, &composites)
                && family_solves(
                    &check.left_factorizations,
                    &left_image,
                    &radical_maps(&left_rad),
                )
                && family_solves(&check.left_memberships, &left_rad, &left_composites);
            if !ok {
                return false;
            }
        }
        true
    }
}

/// Whether each stored coordinate vector rebuilds the matching expected
/// morphism over the RREF basis of `over`.
fn family_solves(stored: &[Vec<Fp>], over: &HomSubspace, expected: &[Morphism]) -> bool {
    if stored.len() != expected.len() {
        return false;
    }
    stored.iter().zip(expected).all(|(coords, target)| {
        matches!(subspace_combination(over, coords), Some(rebuilt) if rebuilt == *target)
    })
}

/// The shared output of the socle construction for a non-projective input.
struct SocleConstruction {
    tau_ind: IndecomposableModule,
    class: ExtClass,
    socle: DenseMat,
    traces: Vec<Vec<Fp>>,
    stable_end_dim: usize,
    sequence: ShortExactSequence,
    non_split: NonSplitWitness,
}

enum Construction {
    Projective,
    Built(Box<SocleConstruction>),
}

/// Runs the socle construction of the module docs: the double-route
/// translate with the projectivity cross-check, the indecomposability gate
/// on the translate, the action matrices, the socle kernel, the two
/// dimension gates, the extension of the chosen class, and its non-split
/// witness.
fn construct(m: &IndecomposableModule) -> Result<Construction, AlmostSplitError> {
    let projective = m.is_projective();
    let tau_module = tau(m.module())?;
    if tau_module.is_zero() != projective {
        return Err(AlmostSplitError::Defect(
            DefectKind::ProjectivityDisagreement {
                resolution_projective: projective,
                tau_zero: tau_module.is_zero(),
            },
        ));
    }
    if projective {
        return Ok(Construction::Projective);
    }
    let tau_ind = IndecomposableModule::new(&tau_module)?;
    let space = ExtSpace::new(m.module(), tau_ind.module(), 1)
        .expect("the translate lives over the module's algebra Arc");
    let stable = stable_end(m.module())?;
    if space.dim() != stable.dim() {
        return Err(AlmostSplitError::Defect(
            DefectKind::DualityDimensionMismatch {
                ext_dim: space.dim(),
                stable_end_dim: stable.dim(),
            },
        ));
    }
    let field = m.module().field();
    let action = action_matrices(m, &space)?;
    let socle = socle_kernel(&action, space.dim(), &field);
    if socle.rows() != m.residue_degree() {
        return Err(AlmostSplitError::Defect(
            DefectKind::SocleDimensionMismatch {
                socle_dim: socle.rows(),
                residue_degree: m.residue_degree(),
            },
        ));
    }
    let class = space.class_from_coordinates(socle.row(0))?;
    let traces: Vec<Vec<Fp>> = action
        .iter()
        .map(|a| row_times(class.coordinates(), a, &field))
        .collect();
    let sequence = ShortExactSequence::from_ext1(&class)?;
    // The chosen class is a nonzero socle row, so the expected answer is
    // NonSplit; the one-pass route is the cheaper one for that answer.
    let non_split = match sequence.split_status_one_pass() {
        SplitStatus::NonSplit(witness) => witness,
        SplitStatus::Split(_) => {
            return Err(AlmostSplitError::Defect(DefectKind::NonzeroClassSplit));
        }
    };
    Ok(Construction::Built(Box::new(SocleConstruction {
        tau_ind,
        class,
        socle,
        traces,
        stable_end_dim: stable.dim(),
        sequence,
        non_split,
    })))
}

/// The almost-split sequence ending at `m`, certified through the AR
/// duality route.
///
/// A projective input returns [`AlmostSplitOutcome::Projective`]: valid
/// mathematics, not an error. Otherwise the socle construction runs and the
/// result carries an [`ArDualityWitness`].
///
/// # Errors
/// [`AlmostSplitError::Tau`] when the translate fails,
/// [`AlmostSplitError::TauIndecomposability`] when the translate fails the
/// indecomposability gate, and [`AlmostSplitError::Defect`] when an internal
/// cross-check fails, which is a crate defect. The Hom, Ext, and sequence
/// layers report their own endpoint rejections through
/// [`AlmostSplitError::Hom`], [`AlmostSplitError::Space`],
/// [`AlmostSplitError::Ext`], and [`AlmostSplitError::Sequence`].
pub fn almost_split(m: &IndecomposableModule) -> Result<AlmostSplitOutcome, AlmostSplitError> {
    let built = match construct(m)? {
        Construction::Projective => return Ok(AlmostSplitOutcome::Projective),
        Construction::Built(built) => built,
    };
    let SocleConstruction {
        tau_ind: _,
        class,
        socle,
        traces,
        stable_end_dim,
        sequence,
        non_split,
    } = *built;
    let witness = ArDualityWitness {
        radical_coords: m.endo().radical_basis().clone(),
        action_traces: traces,
        socle_dim: socle.rows(),
        socle_rref: socle,
        chosen_row: 0,
        ext_dim: class.space().dim(),
        stable_end_dim,
        residue_degree: m.residue_degree(),
        non_split,
    };
    Ok(AlmostSplitOutcome::Sequence(AlmostSplitSequence {
        sequence,
        class,
        witness: AlmostSplitWitness::ArDuality(witness),
    }))
}

/// The almost-split sequence ending at `m`, certified against every entry
/// of an exhaustive catalog.
///
/// The construction is the one of [`almost_split`]; the witness instead
/// stores, for the right map `g: E -> M` and every catalog entry `X`, the
/// data behind `im(Hom(X, E) -> Hom(X, M)) = rad(X, M)`, and the dual left
/// data for `f: tau M -> E`.
///
/// # Errors
/// [`AlmostSplitError::Hom`] with [`HomError::DifferentAlgebras`] when `m`
/// and the catalog do not share one algebra; otherwise as
/// [`almost_split`].
pub fn almost_split_via_catalog(
    m: &IndecomposableModule,
    catalog: &IndecomposableCatalog,
) -> Result<AlmostSplitOutcome, AlmostSplitError> {
    if !Arc::ptr_eq(m.module().algebra(), catalog.algebra()) {
        return Err(AlmostSplitError::Hom(HomError::DifferentAlgebras));
    }
    let built = match construct(m)? {
        Construction::Projective => return Ok(AlmostSplitOutcome::Projective),
        Construction::Built(built) => built,
    };
    let SocleConstruction {
        tau_ind,
        class,
        sequence,
        ..
    } = *built;
    let mut entries = Vec::with_capacity(catalog.len());
    for (entry, x) in catalog.entries().iter().enumerate() {
        let EntryRecompute {
            image,
            rad,
            composites,
            left_image,
            left_rad,
            left_composites,
        } = recompute_entry(m, &tau_ind, &sequence, x)?;
        if image != rad {
            return Err(AlmostSplitError::Defect(
                DefectKind::RightFactorizationMismatch { entry },
            ));
        }
        if left_image != left_rad {
            return Err(AlmostSplitError::Defect(
                DefectKind::LeftFactorizationMismatch { entry },
            ));
        }
        let express =
            |over: &HomSubspace, maps: &[Morphism]| -> Result<Vec<Vec<Fp>>, AlmostSplitError> {
                maps.iter()
                    .map(|map| {
                        Ok(over.witness_contains(map)?.expect(
                            "the subspaces were just proved equal, so every map solves; \
                         this is a bug in auslander",
                        ))
                    })
                    .collect()
            };
        let radical_maps = |rad: &HomSubspace| -> Vec<Morphism> {
            (0..rad.dim()).map(|i| rad.basis_morphism(i)).collect()
        };
        entries.push(CatalogEntryCheck {
            right_factorizations: express(&image, &radical_maps(&rad))?,
            right_memberships: express(&rad, &composites)?,
            left_factorizations: express(&left_image, &radical_maps(&left_rad))?,
            left_memberships: express(&left_rad, &left_composites)?,
        });
    }
    Ok(AlmostSplitOutcome::Sequence(AlmostSplitSequence {
        sequence,
        class,
        witness: AlmostSplitWitness::ExhaustiveCatalog(CatalogWitness { entries }),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::{Algebra, commutative_square, kronecker, linear_an, truncated_poly};
    use crate::completion::CompletionLimits;
    use crate::decompose::{KrullSchmidtOutcome, krull_schmidt};
    use crate::field::PrimeField;
    use crate::linalg::RowReducer;
    use crate::module::direct_sum;
    use crate::quiver::{ArrowId, Quiver};
    use crate::radical::radical;
    use crate::relation::{Presentation, Relation};

    fn f2() -> PrimeField {
        PrimeField::new(2).unwrap()
    }

    fn f5() -> PrimeField {
        PrimeField::new(5).unwrap()
    }

    fn indec(m: &Module) -> IndecomposableModule {
        IndecomposableModule::new(m).unwrap()
    }

    fn sequence_of(m: &IndecomposableModule) -> AlmostSplitSequence {
        match almost_split(m).unwrap() {
            AlmostSplitOutcome::Sequence(sequence) => sequence,
            AlmostSplitOutcome::Projective => panic!("expected a sequence, got Projective"),
        }
    }

    fn catalog_sequence_of(
        m: &IndecomposableModule,
        catalog: &IndecomposableCatalog,
    ) -> AlmostSplitSequence {
        match almost_split_via_catalog(m, catalog).unwrap() {
            AlmostSplitOutcome::Sequence(sequence) => sequence,
            AlmostSplitOutcome::Projective => panic!("expected a sequence, got Projective"),
        }
    }

    fn duality_witness(sequence: &AlmostSplitSequence) -> &ArDualityWitness {
        match sequence.witness() {
            AlmostSplitWitness::ArDuality(witness) => witness,
            AlmostSplitWitness::ExhaustiveCatalog(_) => panic!("expected the AR duality witness"),
        }
    }

    fn catalog_witness(sequence: &AlmostSplitSequence) -> &CatalogWitness {
        match sequence.witness() {
            AlmostSplitWitness::ExhaustiveCatalog(witness) => witness,
            AlmostSplitWitness::ArDuality(_) => panic!("expected the catalog witness"),
        }
    }

    /// Krull-Schmidt classes of the middle term as sorted
    /// (dimension vector, multiplicity) pairs.
    fn middle_classes(middle: &Module) -> Vec<(Vec<usize>, usize)> {
        match krull_schmidt(middle) {
            KrullSchmidtOutcome::Classes(classes) => {
                let mut dims: Vec<(Vec<usize>, usize)> = classes
                    .iter()
                    .map(|c| (c.representative.dim_vector().to_vec(), c.multiplicity))
                    .collect();
                dims.sort();
                dims
            }
            KrullSchmidtOutcome::Unknown { reason } => panic!("krull_schmidt failed: {reason}"),
        }
    }

    fn ids(raw: &[u32]) -> Vec<ArrowId> {
        raw.iter().copied().map(ArrowId).collect()
    }

    /// The preprojective algebra of A_3 over F_2, the constructor of
    /// tests/acceptance_nonmonomial.rs: double quiver a: 0 -> 1 (id 0),
    /// b: 1 -> 2 (1), abar: 1 -> 0 (2), bbar: 2 -> 1 (3) with relations
    /// a.abar, abar.a - b.bbar, bbar.b. Dimension 10, self-injective.
    fn preprojective_a3() -> Arc<Algebra> {
        let field = f2();
        let quiver = Quiver::new(3, &[(0, 1), (1, 2), (1, 0), (2, 1)]).unwrap();
        let relations = vec![
            Relation::new(&quiver, field, vec![(field.one(), ids(&[0, 2]))]).unwrap(),
            Relation::new(
                &quiver,
                field,
                vec![(field.one(), ids(&[2, 0])), (field.elem(-1), ids(&[1, 3]))],
            )
            .unwrap(),
            Relation::new(&quiver, field, vec![(field.one(), ids(&[3, 1]))]).unwrap(),
        ];
        let presentation = Presentation::new(quiver, field, relations).unwrap();
        Algebra::new(presentation, &CompletionLimits::default()).unwrap()
    }

    // A = k[x]/(x^3) is symmetric, so tau = Omega^2. Omega S = ker(P -> S) =
    // rad P, of dimension 2. The cover of rad P is P again (top rad P = S),
    // with kernel soc P = S, so Omega^2 S = S and tau S = S. The minimal
    // resolution of S is period-2 with every term P and Hom(P, S) = k with
    // zero differentials, so Ext^1(S, S) has dimension 1. End(S) = k, and
    // the one map S -> P lands in soc P, so its composite with P ->> S is
    // zero: stable End(S) has dimension 1 = Ext dimension, the radical of
    // End(S) is zero, and the socle is the whole Ext space, of dimension 1 =
    // residue degree. The chosen class is the generator, and its extension
    // is the unique non-split self-extension of S: the uniserial module of
    // dimension 2. The sequence is 0 -> S -> rad P -> S -> 0.
    #[test]
    fn truncated_poly_3_simple_has_the_uniserial_almost_split_sequence() {
        for field in [f5(), f2()] {
            let algebra = truncated_poly(3, field).unwrap();
            let s = indec(&Module::simple(&algebra, 0));
            let sequence = sequence_of(&s);
            assert_eq!(sequence.sequence().sub().dim_vector(), &[1]);
            assert_eq!(sequence.sequence().middle().dim_vector(), &[2]);
            assert_eq!(sequence.sequence().quotient().dim_vector(), &[1]);
            assert_eq!(
                middle_classes(sequence.sequence().middle()),
                vec![(vec![2], 1)]
            );
            let witness = duality_witness(&sequence);
            assert_eq!(witness.ext_dim(), 1);
            assert_eq!(witness.stable_end_dim(), 1);
            assert_eq!(witness.socle_dim(), 1);
            assert_eq!(witness.residue_degree(), 1);
            assert_eq!(witness.chosen_row(), 0);
            assert!(witness.action_traces().is_empty(), "rad End(S) = 0");
            assert!(witness.verify(&s, sequence.sequence(), sequence.chosen_ar_class()));
        }
    }

    // R = rad P over k[x]/(x^3) is (x) = A/(x^2), of dimension 2. The cover
    // P -> R (1 |-> x) has kernel ann(x) = (x^2) = S, so Omega R = S and
    // tau R = Omega^2 R = Omega S = rad P = R. End(R) = A/(x^2) has
    // dimension 2 with radical spanned by multiplication by x. Hom(R, P) =
    // ann(x^2) = span{x, x^2} has dimension 2, and composing with P ->> R
    // kills x^2 and keeps x, so the projectively trivial part of End(R) has
    // dimension 1 and stable End(R) has dimension 1 = Ext^1(R, tau R). The
    // socle then has dimension 1 = residue degree, and the sequence of the
    // chosen class is the unique non-split extension class up to scalar. One
    // such sequence is explicit: 0 -> A/(x^2) -> A/(x) (+) A/(x^3) ->
    // A/(x^2) -> 0 with a |-> (a mod x, x a) and (b, c) |-> x b - c; it is
    // exact by the dimension count 2 = 1 + 3 - 2 and non-split because
    // S (+) P has no summand of dimension 2. So the middle is S (+) P with
    // dimension vectors [1] and [3].
    #[test]
    fn truncated_poly_3_rad_p_has_middle_simple_plus_projective() {
        for field in [f5(), f2()] {
            let algebra = truncated_poly(3, field).unwrap();
            let p = Module::projective(&algebra, 0);
            let r = indec(&radical(&p).0);
            let sequence = sequence_of(&r);
            assert_eq!(sequence.sequence().sub().dim_vector(), &[2]);
            assert_eq!(sequence.sequence().middle().dim_vector(), &[4]);
            assert_eq!(sequence.sequence().quotient().dim_vector(), &[2]);
            assert_eq!(
                middle_classes(sequence.sequence().middle()),
                vec![(vec![1], 1), (vec![3], 1)]
            );
            let witness = duality_witness(&sequence);
            assert_eq!(witness.ext_dim(), 1);
            assert_eq!(witness.stable_end_dim(), 1);
            assert_eq!(witness.socle_dim(), 1);
            assert_eq!(
                witness.action_traces().len(),
                1,
                "rad End(R) has dimension 1"
            );
            assert!(
                witness
                    .action_traces()
                    .iter()
                    .all(|trace| trace.iter().all(|v| v.is_zero()))
            );
            assert!(witness.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
        }
    }

    // Right modules over linear A_3 with arrows a: 0 -> 1, b: 1 -> 2.
    // P_1 = e_1 A has basis {e_1, b} with top S_1 and rad P_1 = S_2, so
    // 0 -> S_2 -> P_1 -> S_1 -> 0 is exact and non-split. tau S_1 = S_2 (the
    // tau tests of ar.rs pin the dimension vector (0, 0, 1)), and
    // Ext^1(S_1, S_2) = k: one dimension per arrow 1 -> 2. End(S_1) = k,
    // and Hom(S_1, P_1) = 0 because A-linearity at b forces the vertex-1
    // component to vanish against the isomorphism P_1(b), so stable
    // End(S_1) = k and the socle is the whole Ext space. The chosen class
    // is the generator, whose middle is the non-split extension P_1.
    #[test]
    fn linear_a3_sequence_ending_at_s1_has_middle_p1() {
        let algebra = linear_an(3, f5());
        let s1 = indec(&Module::simple(&algebra, 1));
        let sequence = sequence_of(&s1);
        assert_eq!(sequence.sequence().sub().dim_vector(), &[0, 0, 1]);
        assert_eq!(sequence.sequence().middle().dim_vector(), &[0, 1, 1]);
        assert_eq!(sequence.sequence().quotient().dim_vector(), &[0, 1, 0]);
        assert_eq!(
            middle_classes(sequence.sequence().middle()),
            vec![(vec![0, 1, 1], 1)]
        );
        let witness = duality_witness(&sequence);
        assert_eq!(witness.socle_dim(), 1);
        assert_eq!(witness.residue_degree(), 1);
        assert!(witness.verify(&s1, sequence.sequence(), sequence.chosen_ar_class()));
    }

    // I_1 over linear A_3 has dimension vector (1, 1, 0), top S_0, and
    // cover P_0 with kernel P_2, so its presentation is P_2 -> P_0 -> I_1.
    // tau I_1 = ker(nu(d_1): I_2 -> I_0) has dimension 3 - 1 + dim nu(I_1)
    // = 2 by exactness, because Hom(I_1, A) = 0 (any component into a
    // projective dies against the isomorphisms P_i(b) or the zero spaces),
    // so tau I_1 = (0, 1, 1) = P_1. Zigzag through the meshes: the mesh
    // 0 -> S_2 -> P_1 -> S_1 -> 0 gives the irreducible map P_1 -> S_1, and
    // rad P_0 = P_1 gives the irreducible inclusion P_1 -> P_0. These are
    // the two arrows out of tau I_1 = P_1, so the middle of the mesh ending
    // at I_1 is S_1 (+) P_0, of dimension vector (1, 2, 1): the D4-free
    // mesh 0 -> P_1 -> S_1 (+) P_0 -> I_1 -> 0.
    #[test]
    fn linear_a3_sequence_ending_at_i1_matches_the_mesh() {
        let algebra = linear_an(3, f5());
        let i1 = indec(&Module::injective(&algebra, 1));
        assert_eq!(i1.module().dim_vector(), &[1, 1, 0]);
        let sequence = sequence_of(&i1);
        assert_eq!(sequence.sequence().sub().dim_vector(), &[0, 1, 1]);
        assert_eq!(sequence.sequence().middle().dim_vector(), &[1, 2, 1]);
        assert_eq!(
            middle_classes(sequence.sequence().middle()),
            vec![(vec![0, 1, 0], 1), (vec![1, 1, 1], 1)]
        );
        let witness = duality_witness(&sequence);
        assert_eq!(witness.socle_dim(), 1);
        assert!(witness.verify(&i1, sequence.sequence(), sequence.chosen_ar_class()));
    }

    // S_1 over the commutative square is not projective: P_1 has dimension
    // vector (0, 1, 0, 1). tau comes from the crate's double-route tau; the
    // test pins the checkable invariants instead of a full hand value: the
    // sequence is exact with dim tau + dim S_1 = dim E, non-split with a
    // verifying witness, and End(S_1) = k forces a one-dimensional socle.
    #[test]
    fn commutative_square_s1_sequence_invariants_hold() {
        let algebra = commutative_square(f5());
        let s1 = indec(&Module::simple(&algebra, 1));
        let sequence = sequence_of(&s1);
        assert_eq!(sequence.sequence().quotient().dim_vector(), &[0, 1, 0, 0]);
        assert_eq!(
            sequence.sequence().sub().total_dim() + sequence.sequence().quotient().total_dim(),
            sequence.sequence().middle().total_dim()
        );
        let witness = duality_witness(&sequence);
        assert_eq!(witness.ext_dim(), witness.stable_end_dim());
        assert_eq!(witness.socle_dim(), 1);
        assert_eq!(witness.residue_degree(), 1);
        assert!(witness.verify(&s1, sequence.sequence(), sequence.chosen_ar_class()));
    }

    // The preprojective algebra of A_3 over F_2 is self-injective, so no
    // simple is projective and every simple has an almost-split sequence.
    // The hand derivation of tau S_0 is not pinned; the test pins the
    // checkable invariants: the dimension count, a passing witness, and the
    // one-dimensional socle forced by End(S_0) = k.
    #[test]
    fn preprojective_a3_simple_sequence_invariants_hold() {
        let algebra = preprojective_a3();
        let s0 = indec(&Module::simple(&algebra, 0));
        assert!(!s0.is_projective());
        let sequence = sequence_of(&s0);
        assert_eq!(
            sequence.sequence().sub().total_dim() + sequence.sequence().quotient().total_dim(),
            sequence.sequence().middle().total_dim()
        );
        let witness = duality_witness(&sequence);
        assert_eq!(witness.ext_dim(), witness.stable_end_dim());
        assert_eq!(witness.socle_dim(), 1);
        assert_eq!(witness.residue_degree(), 1);
        assert!(witness.verify(&s0, sequence.sequence(), sequence.chosen_ar_class()));
    }

    // Over A = k[x]/(x^4) let M = A/(x^2) = rad^2 P, of dimension 2.
    // Omega M = (x^2), which is isomorphic to A/ann(x^2) = A/(x^2) = M, so
    // tau M = Omega^2 M = M for this symmetric algebra. The minimal
    // resolution repeats A -x^2-> A, and Hom(A, tau M) = tau M has dimension
    // 2 with zero induced differentials because x^2 kills A/(x^2), so
    // Ext^1(M, tau M) has dimension 2. End(M) = A/(x^2) has dimension 2;
    // Hom(M, A) = ann(x^2) = span{x^2, x^3}, and both composites with
    // A ->> M are zero, so stable End(M) has dimension 2 as well. The
    // radical of End(M) is spanned by x, so the socle gate forces dimension
    // 1 = residue degree: a genuine proper socle inside a two-dimensional
    // Ext space. The right map of the mesh 0 -> A/(x^2) ->
    // A/(x) (+) A/(x^3) -> A/(x^2) -> 0, (b, c) |-> x b - c, is right
    // almost split: a non-retraction A/(x^i) -> M either lands in rad M and
    // factors through the A/(x) leg (h = x u factors as x b with b the mod-x
    // reduction of u), or is epi with i >= 3 and factors through the
    // A/(x^3) leg. So the middle is A/(x) (+) A/(x^3), dimensions 1 and 3.
    #[test]
    fn truncated_poly_4_interval_module_has_a_proper_socle() {
        let field = f5();
        let algebra = truncated_poly(4, field).unwrap();
        let p = Module::projective(&algebra, 0);
        let m = indec(&radical(&radical(&p).0).0);
        assert_eq!(m.module().dim_vector(), &[2]);
        let sequence = sequence_of(&m);
        assert_eq!(sequence.sequence().sub().dim_vector(), &[2]);
        assert_eq!(sequence.sequence().middle().dim_vector(), &[4]);
        assert_eq!(
            middle_classes(sequence.sequence().middle()),
            vec![(vec![1], 1), (vec![3], 1)]
        );
        let witness = duality_witness(&sequence);
        assert_eq!(witness.ext_dim(), 2);
        assert_eq!(witness.stable_end_dim(), 2);
        assert_eq!(witness.socle_dim(), 1);
        assert_eq!(witness.residue_degree(), 1);
        assert_eq!(witness.action_traces().len(), 1);
        assert_eq!(witness.action_traces()[0].len(), 2);
        assert!(witness.action_traces()[0].iter().all(|v| v.is_zero()));
        assert!(witness.verify(&m, sequence.sequence(), sequence.chosen_ar_class()));
    }

    // S_2 = P_2 over linear A_3 is projective, so its identity factors
    // through the cover and stable End(S_2) = 0. S_1 is not projective and
    // Hom(S_1, P_1) = 0, so stable End(S_1) = End(S_1) = k. Over k[x]/(x^3)
    // the space Hom(rad P, rad P) = End(A/(x^2)) has dimension 2; the
    // projectively trivial part is the image of Hom(rad P, P) =
    // span{x, x^2} under composition with P ->> rad P, which kills x^2 and
    // keeps x: dimension 1, so stable End(rad P) has dimension 1.
    #[test]
    fn stable_hom_dimensions_match_hand_counts() {
        let a3 = linear_an(3, f5());
        let s2 = Module::simple(&a3, 2);
        assert_eq!(stable_end(&s2).unwrap().dim(), 0);
        let s1 = Module::simple(&a3, 1);
        assert_eq!(stable_end(&s1).unwrap().dim(), 1);
        for field in [f5(), f2()] {
            let algebra = truncated_poly(3, field).unwrap();
            let p = Module::projective(&algebra, 0);
            let r = radical(&p).0;
            let space = HomSpace::new(&r, &r).unwrap();
            assert_eq!(space.dim(), 2);
            assert_eq!(projectively_trivial(&space).unwrap().dim(), 1);
            assert_eq!(stable_end(&r).unwrap().dim(), 1);
        }
    }

    #[test]
    fn projective_inputs_return_the_projective_outcome() {
        let a3 = linear_an(3, f5());
        for v in 0..3 {
            let p = indec(&Module::projective(&a3, v));
            assert!(matches!(
                almost_split(&p).unwrap(),
                AlmostSplitOutcome::Projective
            ));
        }
        let algebra = truncated_poly(3, f2()).unwrap();
        let p = indec(&Module::projective(&algebra, 0));
        assert!(matches!(
            almost_split(&p).unwrap(),
            AlmostSplitOutcome::Projective
        ));
        let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
        assert!(matches!(
            almost_split_via_catalog(&p, &catalog).unwrap(),
            AlmostSplitOutcome::Projective
        ));
    }

    // tau is deterministic, so the two routes compute translate modules
    // with identical vertex and arrow matrices, and class coordinates
    // transport verbatim between their identically computed Ext bases. The
    // transport below is checked entry by entry before equals() runs.
    #[test]
    fn via_catalog_agrees_with_the_ar_duality_route() {
        let x3 = truncated_poly(3, f2()).unwrap();
        let x3_catalog = IndecomposableCatalog::nakayama(&x3).unwrap();
        let a3 = linear_an(3, f5());
        let a3_catalog = IndecomposableCatalog::dynkin(&a3).unwrap();
        let cases = [
            (indec(&Module::simple(&x3, 0)), x3_catalog),
            (indec(&Module::simple(&a3, 1)), a3_catalog),
        ];
        for (m, catalog) in &cases {
            let duality = sequence_of(m);
            let through_catalog = catalog_sequence_of(m, catalog);
            assert_eq!(
                duality.sequence().middle().dim_vector(),
                through_catalog.sequence().middle().dim_vector()
            );
            let left = duality.sequence().sub();
            let right = through_catalog.sequence().sub();
            assert_eq!(left.dim_vector(), right.dim_vector());
            for a in 0..left.algebra().quiver().num_arrows() {
                let arrow = ArrowId(a as u32);
                assert_eq!(
                    left.map(arrow).entries_u64(),
                    right.map(arrow).entries_u64()
                );
            }
            let transported = duality
                .chosen_ar_class()
                .space()
                .class_from_coordinates(through_catalog.chosen_ar_class().coordinates())
                .unwrap();
            assert!(transported.equals(duality.chosen_ar_class()).unwrap());
            let witness = catalog_witness(&through_catalog);
            assert!(witness.verify(
                m,
                catalog,
                through_catalog.sequence(),
                through_catalog.chosen_ar_class()
            ));
        }
    }

    #[test]
    fn via_catalog_rejects_a_catalog_over_another_algebra() {
        let x3 = truncated_poly(3, f2()).unwrap();
        let m = indec(&Module::simple(&x3, 0));
        let a3 = linear_an(3, f5());
        let catalog = IndecomposableCatalog::dynkin(&a3).unwrap();
        assert!(matches!(
            almost_split_via_catalog(&m, &catalog),
            Err(AlmostSplitError::Hom(HomError::DifferentAlgebras))
        ));
    }

    #[test]
    fn a_tampered_action_trace_fails_verification() {
        let algebra = truncated_poly(3, f5()).unwrap();
        let p = Module::projective(&algebra, 0);
        let r = indec(&radical(&p).0);
        let sequence = sequence_of(&r);
        let mut bad = duality_witness(&sequence).clone();
        assert_eq!(bad.action_traces.len(), 1);
        bad.action_traces[0][0] = f5().one();
        assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
    }

    #[test]
    fn a_swapped_socle_row_fails_verification() {
        let field = f5();
        let algebra = truncated_poly(4, field).unwrap();
        let p = Module::projective(&algebra, 0);
        let m = indec(&radical(&radical(&p).0).0);
        let sequence = sequence_of(&m);
        let witness = duality_witness(&sequence);
        let socle = witness.socle_rref().clone();
        let dim = witness.ext_dim();
        let mut reducer = RowReducer::new(dim);
        for r in 0..socle.rows() {
            reducer.push(socle.row(r), &field);
        }
        let candidate = (0..dim)
            .map(|k| {
                let mut row = vec![field.zero(); dim];
                row[k] = field.one();
                row
            })
            // A rejected row already lies in the socle span, so the push that
            // rejects it leaves the reducer alone.
            .find(|row| reducer.push(row, &field))
            .expect("the socle is proper, so some unit vector lies outside it");
        let action = action_matrices(&m, sequence.chosen_ar_class().space()).unwrap();
        assert!(
            action.iter().any(|a| row_times(&candidate, a, &field)
                .iter()
                .any(|v| !v.is_zero())),
            "the replacement vector is not annihilated, so it is not in the socle"
        );
        let mut bad = witness.clone();
        bad.socle_rref = DenseMat::from_rows(&[candidate]);
        assert!(!bad.verify(&m, sequence.sequence(), sequence.chosen_ar_class()));
    }

    // The dual vectors of the S sequence and the rad P sequence over
    // k[x]/(x^3) certify retraction systems of different sizes. Grafting
    // one into the other's witness is a tamper the dual-vector recheck
    // rejects.
    #[test]
    fn a_tampered_dual_vector_fails_verification() {
        let algebra = truncated_poly(3, f5()).unwrap();
        let s = indec(&Module::simple(&algebra, 0));
        let p = Module::projective(&algebra, 0);
        let r = indec(&radical(&p).0);
        let s_sequence = sequence_of(&s);
        let r_sequence = sequence_of(&r);
        let s_witness = duality_witness(&s_sequence);
        let r_witness = duality_witness(&r_sequence);
        assert_ne!(
            s_witness.non_split().dual().len(),
            r_witness.non_split().dual().len()
        );
        let mut bad = s_witness.clone();
        bad.non_split = r_witness.non_split().clone();
        assert!(!bad.verify(&s, s_sequence.sequence(), s_sequence.chosen_ar_class()));
    }

    #[test]
    fn a_tampered_catalog_factorization_coordinate_fails_verification() {
        let field = f2();
        let algebra = truncated_poly(3, field).unwrap();
        let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
        let m = indec(&Module::simple(&algebra, 0));
        let sequence = catalog_sequence_of(&m, &catalog);
        let witness = catalog_witness(&sequence);
        assert!(witness.verify(
            &m,
            &catalog,
            sequence.sequence(),
            sequence.chosen_ar_class()
        ));
        let entry = witness
            .entries
            .iter()
            .position(|check| {
                check
                    .right_factorizations
                    .first()
                    .is_some_and(|row| !row.is_empty())
            })
            .expect("some catalog entry has a nonzero radical into M");
        let mut bad = witness.clone();
        let old = bad.entries[entry].right_factorizations[0][0];
        bad.entries[entry].right_factorizations[0][0] = field.add(old, field.one());
        assert!(!bad.verify(
            &m,
            &catalog,
            sequence.sequence(),
            sequence.chosen_ar_class()
        ));
        let mut missing = witness.clone();
        missing.entries[entry].right_factorizations.pop();
        assert!(!missing.verify(
            &m,
            &catalog,
            sequence.sequence(),
            sequence.chosen_ar_class()
        ));
    }

    // The catalog witness stores no class coordinates, so realizing the
    // class is the sequence-recovery gate's job: a scaled nonzero class
    // shares the space and every endpoint but is not the class the
    // sequence realizes.
    #[test]
    fn a_scaled_class_fails_catalog_verification() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
        let m = indec(&Module::simple(&algebra, 0));
        let sequence = catalog_sequence_of(&m, &catalog);
        let witness = catalog_witness(&sequence);
        assert!(witness.verify(
            &m,
            &catalog,
            sequence.sequence(),
            sequence.chosen_ar_class()
        ));
        let scaled = sequence.chosen_ar_class().scale(field.elem(2));
        assert!(!scaled.is_zero());
        assert!(!witness.verify(&m, &catalog, sequence.sequence(), &scaled));
    }

    // A witness grafted onto an Ext space whose target is not tau M: every
    // stored matrix and dimension matches the recomputation over the wrong
    // space (rad End(S) = 0 on both sides), and the grafted non-split
    // witness certifies the wrong sequence, so only the translate gate can
    // reject.
    #[test]
    fn a_space_with_the_wrong_target_fails_duality_verification() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = indec(&Module::simple(&algebra, 0));
        let genuine = sequence_of(&s);
        let witness = duality_witness(&genuine);
        let r = radical(&Module::projective(&algebra, 0)).0;
        let wrong_space = ExtSpace::new(s.module(), &r, 1).unwrap();
        assert_eq!(wrong_space.dim(), 1);
        let class = wrong_space.class_from_coordinates(&[field.one()]).unwrap();
        let sequence = ShortExactSequence::from_ext1(&class).unwrap();
        let SplitStatus::NonSplit(non_split) = sequence.split_status() else {
            panic!("the nonzero class does not split");
        };
        let mut bad = witness.clone();
        bad.non_split = non_split;
        assert!(!bad.verify(&s, &sequence, &class));
    }

    #[test]
    fn a_dimension_field_altered_in_either_direction_fails_verification() {
        let algebra = truncated_poly(3, f5()).unwrap();
        let p = Module::projective(&algebra, 0);
        let r = indec(&radical(&p).0);
        let sequence = sequence_of(&r);
        let witness = duality_witness(&sequence);
        assert!(witness.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
        for delta in [1isize, -1] {
            let shift = |v: usize| (v as isize + delta) as usize;
            let mut bad = witness.clone();
            bad.ext_dim = shift(bad.ext_dim);
            assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
            let mut bad = witness.clone();
            bad.stable_end_dim = shift(bad.stable_end_dim);
            assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
            let mut bad = witness.clone();
            bad.socle_dim = shift(bad.socle_dim);
            assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
            let mut bad = witness.clone();
            bad.residue_degree = shift(bad.residue_degree);
            assert!(!bad.verify(&r, sequence.sequence(), sequence.chosen_ar_class()));
        }
    }

    // Defect values are not constructible through the public API; only
    // their Display texts are pinned.
    #[test]
    fn defect_kind_display_is_stable() {
        assert_eq!(
            DefectKind::DualityDimensionMismatch {
                ext_dim: 2,
                stable_end_dim: 1
            }
            .to_string(),
            "Ext^1(M, tau M) has dimension 2, stable End(M) has dimension 1; crate defect"
        );
        assert_eq!(
            DefectKind::SocleDimensionMismatch {
                socle_dim: 0,
                residue_degree: 1
            }
            .to_string(),
            "the Ext socle has dimension 0, the residue degree is 1; crate defect"
        );
        assert_eq!(
            DefectKind::ProjectivityDisagreement {
                resolution_projective: true,
                tau_zero: false
            }
            .to_string(),
            "the resolution route reports projective = true, tau reports zero = false; \
             crate defect"
        );
        assert_eq!(
            DefectKind::NonzeroClassSplit.to_string(),
            "the sequence of a nonzero chosen class splits; crate defect"
        );
        assert_eq!(
            DefectKind::RightFactorizationMismatch { entry: 3 }.to_string(),
            "the image of Hom(X, E) in Hom(X, M) differs from rad(X, M) at catalog entry 3; \
             crate defect"
        );
        assert_eq!(
            DefectKind::LeftFactorizationMismatch { entry: 0 }.to_string(),
            "the image of Hom(E, X) in Hom(tau M, X) differs from rad(tau M, X) at catalog \
             entry 0; crate defect"
        );
    }

    // Both catalog domains of this release contain only modules of residue
    // degree 1, so the socle-dimension gate forces a one-dimensional socle
    // on every non-projective entry.
    #[test]
    fn catalog_domains_have_one_dimensional_socles() {
        let x3 = truncated_poly(3, f2()).unwrap();
        let a3 = linear_an(3, f5());
        let catalogs = [
            IndecomposableCatalog::nakayama(&x3).unwrap(),
            IndecomposableCatalog::dynkin(&a3).unwrap(),
        ];
        for catalog in &catalogs {
            for entry in catalog.entries() {
                assert_eq!(entry.residue_degree(), 1);
                if entry.is_projective() {
                    continue;
                }
                let sequence = sequence_of(entry);
                let witness = duality_witness(&sequence);
                assert_eq!(witness.socle_dim(), 1);
                assert_eq!(witness.residue_degree(), 1);
            }
        }
    }

    /// The Kronecker representation `(I_6, J)` over F_2, for `J` the block
    /// matrix with the companion matrix `C` of `x^3 + x + 1` on the diagonal
    /// and the identity above it. `C` is irreducible over F_2, so `(I_3, C)`
    /// has endomorphism field F_8; this module is the quasi-length-2 member
    /// of the same tube, and its endomorphism algebra is `F_8[t]/(t^2)`.
    fn quasi_length_two_in_the_f8_tube() -> Module {
        let field = f2();
        let algebra = kronecker(2, field);
        let mut j = DenseMat::zero(6, 6);
        for (r, c) in [(0, 1), (1, 2), (2, 0), (2, 1)] {
            j.set(r, c, field.one());
            j.set(3 + r, 3 + c, field.one());
        }
        for r in 0..3 {
            j.set(r, 3 + r, field.one());
        }
        Module::new(algebra, vec![6, 6], vec![DenseMat::identity(6), j])
            .expect("the Kronecker representation is a module")
    }

    // The first fixture with residue degree above 1. Every shipped fixture
    // before it has residue degree 1, so its socle is a line and the socle
    // gate is one-dimensional. Here the residue field is F_8, so the socle is
    // a 3-dimensional proper subspace of a 6-dimensional Ext space.
    #[test]
    fn the_quasi_length_two_module_has_a_three_dimensional_socle_in_a_six_dimensional_ext_space() {
        let w = indec(&quasi_length_two_in_the_f8_tube());
        assert_eq!(w.endo().dim(), 6);
        assert_eq!(w.endo().radical_dim(), 3);
        assert_eq!(w.residue_degree(), 3);
        let sequence = sequence_of(&w);
        let witness = duality_witness(&sequence);
        assert_eq!(witness.ext_dim(), 6);
        assert_eq!(witness.stable_end_dim(), 6);
        assert_eq!(witness.socle_dim(), 3);
        assert_eq!(sequence.chosen_ar_class().space().dim(), 6);
        assert_eq!(witness.chosen_row(), 0);
        assert!(sequence.verify(&w));
        // tau fixes every regular Kronecker module, and the middle term of a
        // mesh in a homogeneous tube is the module twice.
        assert_eq!(sequence.sequence().sub().dim_vector(), &[6, 6]);
        assert_eq!(sequence.sequence().middle().dim_vector(), &[12, 12]);
    }

    // Section 15 of the design, at residue degree above 1: a witness built
    // from socle row 1 carries that row's own valid non-split witness and
    // annihilates every action matrix, so the sequence it names is genuinely
    // almost split. It is not the crate's chosen class, whose coordinates the
    // fresh-process fingerprint pins, so verify rejects the row index.
    #[test]
    fn a_chosen_row_other_than_zero_fails_duality_verification() {
        let w = indec(&quasi_length_two_in_the_f8_tube());
        let sequence = sequence_of(&w);
        let witness = duality_witness(&sequence);
        let space = sequence.chosen_ar_class().space();
        let socle = witness.socle_rref();
        assert!(socle.rows() >= 2, "the socle has a row other than 0");
        let field = w.module().field();
        let other = space.class_from_coordinates(socle.row(1)).unwrap();
        let action = action_matrices(&w, space).unwrap();
        let traces: Vec<Vec<Fp>> = action
            .iter()
            .map(|a| row_times(other.coordinates(), a, &field))
            .collect();
        assert!(
            traces.iter().flatten().all(|v| v.is_zero()),
            "socle row 1 annihilates rad End(M)"
        );
        let other_sequence = ShortExactSequence::from_ext1(&other).unwrap();
        let SplitStatus::NonSplit(non_split) = other_sequence.split_status() else {
            panic!("a nonzero socle class gives a non-split sequence");
        };
        assert!(non_split.verify(&other_sequence));
        let row_one = ArDualityWitness {
            radical_coords: witness.radical_basis_coords().clone(),
            action_traces: traces,
            socle_rref: socle.clone(),
            chosen_row: 1,
            ext_dim: witness.ext_dim(),
            stable_end_dim: witness.stable_end_dim(),
            socle_dim: witness.socle_dim(),
            residue_degree: witness.residue_degree(),
            non_split,
        };
        assert!(!row_one.verify(&w, &other_sequence, &other));
    }

    /// The AR duality fixture whose Ext space carries no coboundaries: over
    /// `k[x]/(x^3)` the simple has `rad End(S) = 0`, so `B^1` has no rows, the
    /// action matrix list is empty, and the socle is the whole line.
    fn simple_over_truncated_poly_3() -> IndecomposableModule {
        let algebra = truncated_poly(3, f5()).unwrap();
        indec(&Module::simple(&algebra, 0))
    }

    // Section 15 of the design: the Ext space a witness certifies against is
    // untrusted data like any other. Here `B^1` has no rows, so replacing it
    // with the complement row leaves every gate intact: the action list is
    // empty, the socle stays the whole line, and `class_from_cocycle` still
    // returns [1] because the complement column pivots first. Only the recheck
    // of the space against a fresh computation rejects it.
    #[test]
    fn a_coboundary_basis_forged_from_the_complement_fails_duality_verification() {
        let s = simple_over_truncated_poly_3();
        let sequence = sequence_of(&s);
        let witness = duality_witness(&sequence);
        let class = sequence.chosen_ar_class();
        assert!(witness.verify(&s, sequence.sequence(), class));
        let space = class.space();
        assert_eq!(space.coboundary_basis().rows(), 0);
        assert_eq!(space.complement_basis().rows(), 1);
        let forged = space.with_bases(
            space.cocycle_basis().clone(),
            space.complement_basis().clone(),
            space.complement_basis().clone(),
        );
        let bad = forged.class_from_coordinates(class.coordinates()).unwrap();
        assert_eq!(bad.coordinates(), class.coordinates());
        assert!(!witness.verify(&s, sequence.sequence(), &bad));
    }

    // Section 15 of the design: nothing outside the space recheck ever reads
    // the stored cocycle basis, so an emptied `Z^1` passes every other gate.
    #[test]
    fn an_emptied_cocycle_basis_fails_duality_verification() {
        let s = simple_over_truncated_poly_3();
        let sequence = sequence_of(&s);
        let witness = duality_witness(&sequence);
        let class = sequence.chosen_ar_class();
        let space = class.space();
        let width = space.cocycle_basis().cols();
        let forged = space.with_bases(
            DenseMat::zero(0, width),
            space.coboundary_basis().clone(),
            space.complement_basis().clone(),
        );
        let bad = forged.class_from_coordinates(class.coordinates()).unwrap();
        assert!(!witness.verify(&s, sequence.sequence(), &bad));
    }

    // Section 15 of the design: `reps` is a cache of the complement, and with
    // `rad End(S) = 0` there is no action matrix to disturb, so a scaled
    // representative changes no other stored value. The space recheck is what
    // rejects it.
    #[test]
    fn a_scaled_representative_fails_duality_verification() {
        let s = simple_over_truncated_poly_3();
        let sequence = sequence_of(&s);
        let witness = duality_witness(&sequence);
        let class = sequence.chosen_ar_class();
        let space = class.space();
        assert_eq!(witness.radical_basis_coords().rows(), 0);
        let scaled = space
            .representatives()
            .iter()
            .map(|rep| scale_morphism(rep, f5().elem(2)))
            .collect();
        let forged = space.with_representatives(scaled);
        let bad = forged.class_from_coordinates(class.coordinates()).unwrap();
        assert!(!witness.verify(&s, sequence.sequence(), &bad));
    }

    // The action is a left one: Ext^1(-, N) is contravariant, so the matrix
    // assignment reverses the crate's diagrammatic product. Nothing computed
    // depends on the side, because rad End(M) is two-sided, but the docs used
    // to name the wrong side and this pins the real identity.
    #[test]
    fn the_action_matrices_reverse_composition() {
        let field = f5();
        let algebra = truncated_poly(3, field).unwrap();
        let s = Module::simple(&algebra, 0);
        // End(S (+) S) is the full 2 x 2 matrix algebra, so the basis has
        // pairs that do not commute.
        let (m, _, _) = direct_sum(&[&s, &s]);
        let space = ExtSpace::new(&m, &s, 1).unwrap();
        assert_eq!(space.dim(), 2);
        let end = hom(&m, &m).unwrap();
        let mut saw_noncommuting = false;
        for phi in &end {
            for psi in &end {
                let a_phi = action_matrix(&space, phi).unwrap();
                let a_psi = action_matrix(&space, psi).unwrap();
                let composite = action_matrix(&space, &phi.then(psi).unwrap()).unwrap();
                assert_eq!(composite, a_psi.mul(&a_phi, &field));
                if a_psi.mul(&a_phi, &field) != a_phi.mul(&a_psi, &field) {
                    saw_noncommuting = true;
                }
            }
        }
        assert!(
            saw_noncommuting,
            "the fixture exercises a noncommutative End"
        );
    }

    // The two verify entry points feed the sequence and class the value
    // holds, and each rejects the other route's witness.
    #[test]
    fn the_sequence_verifies_through_its_own_witness_and_rejects_the_other_route() {
        let algebra = truncated_poly(3, f5()).unwrap();
        let catalog = IndecomposableCatalog::nakayama(&algebra).unwrap();
        let s = indec(&Module::simple(&algebra, 0));
        let duality = sequence_of(&s);
        assert!(duality.verify(&s));
        assert!(!duality.verify_with_catalog(&s, &catalog));
        let through_catalog = catalog_sequence_of(&s, &catalog);
        assert!(through_catalog.verify_with_catalog(&s, &catalog));
        assert!(!through_catalog.verify(&s));
    }
}
