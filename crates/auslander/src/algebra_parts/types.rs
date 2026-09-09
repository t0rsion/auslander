use rustc_hash::FxHashMap;

use crate::certificate::{Certificate, RelationData};
use crate::completion::CompletionLimits;
use crate::field::{Fp, PrimeField};
use crate::linalg::DenseMat;
use crate::monomial::MonomialError;
use crate::quiver::{ArrowId, PathWord, Quiver};
use crate::relation::{Presentation, Relation, RelationError};
use crate::verify::{CycleWitness, VerifyError};

/// Index into [`Algebra::basis`].
pub type BasisIdx = usize;

/// Rejected [`Algebra`] construction input, or an exhausted or defective
/// pipeline run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgebraBuildError {
    /// A monomial family parameter was rejected before the pipeline ran.
    Monomial(MonomialError),
    /// A relation or presentation was rejected before the pipeline ran.
    Relation(RelationError),
    /// The ideal is not admissible: the arrow ideal `J` is not nilpotent.
    /// `J^stable_power` has dimension `dimension` and equals every higher
    /// power. Only the subspace chain decides this. Leading words cannot:
    /// for one loop `x`, the ideals `(x³)` and `(x³ - x²)` share every
    /// leading word, and the second has `J² = J³ = span(x²)`.
    NonAdmissible {
        stable_power: usize,
        dimension: usize,
    },
    /// The verified certificate's `input_relations` differ from the
    /// relations of the presentation, first at `index`. Nothing else in the
    /// certificate ties it to the caller's request.
    InputRelationsMismatch { index: usize },
    /// The verifier proved the quotient infinite dimensional. It carries the
    /// certificate of the completed basis and the cycle witness.
    InfiniteDimensional {
        certificate: Box<Certificate>,
        witness: CycleWitness,
    },
    /// Completion ran out of budget; no certificate exists.
    Truncated(crate::completion::TruncationDiagnostics),
    /// The verifier rejected the engine's own certificate for a reason other
    /// than infinite dimension. This is an engine defect.
    Verification(VerifyError),
}

display_error! { AlgebraBuildError {
    Self::Monomial(error) => "monomial input rejected: {error}";
    Self::Relation(error) => "relation rejected: {error}";
    Self::NonAdmissible { stable_power, dimension } => "the ideal is not admissible: J^{stable_power} has dimension {dimension} and equals every higher power, so J is not nilpotent";
    Self::InputRelationsMismatch { index } => "the certificate's input relations differ from the presentation at index {index}";
    Self::InfiniteDimensional { witness, .. } => "the quotient is infinite dimensional: prefix {:?}, cycle {:?}" , witness.prefix, witness.cycle;
    Self::Truncated(diagnostics) => "completion ran out of budget ({:?}): basis {}, pending ambiguities {}, steps {}", diagnostics.reason, diagnostics.basis_len, diagnostics.pending_ambiguities, diagnostics.steps_used;
    Self::Verification(error) => "the engine's certificate failed verification: {error}";
} }

error_source!(AlgebraBuildError {
    Self::Monomial(error) => Some(error),
    Self::Relation(error) => Some(error),
    Self::Verification(error) => Some(error),
    _ => None,
});

/// Rejects a certificate whose `input_relations` are not the relations of
/// `presentation`, term for term in stored order.
pub(super) fn check_input_relations(
    presentation: &Presentation,
    certificate: &Certificate,
) -> Result<(), AlgebraBuildError> {
    let asked = presentation.relations();
    let found = &certificate.input_relations;
    let differs =
        |index: &usize| asked.get(*index).map(relation_data).as_ref() != found.get(*index);
    match (0..asked.len().max(found.len())).find(differs) {
        Some(index) => Err(AlgebraBuildError::InputRelationsMismatch { index }),
        None => Ok(()),
    }
}

/// A relation as certificate data: raw coefficients and arrow-id words, in
/// the stored descending order.
fn relation_data(relation: &Relation) -> RelationData {
    relation
        .terms()
        .iter()
        .map(|(coeff, word)| (coeff.raw(), word.arrows().iter().map(|a| a.0).collect()))
        .collect()
}

/// The index maps of a normal-word basis: word to index for the
/// non-trivial words, plus the source, target, and component partitions.
pub(super) type BasisIndexes = (
    FxHashMap<Vec<ArrowId>, BasisIdx>,
    Vec<Vec<BasisIdx>>,
    Vec<Vec<BasisIdx>>,
    Vec<Vec<Vec<BasisIdx>>>,
);

pub(super) fn index_basis(quiver: &Quiver, basis: &[PathWord]) -> BasisIndexes {
    let n = quiver.num_vertices() as usize;
    let mut index_of = FxHashMap::default();
    for (i, p) in basis.iter().enumerate() {
        if !p.is_trivial() {
            index_of.insert(p.arrows().to_vec(), i);
        }
    }
    let mut from = vec![Vec::new(); n];
    let mut to = vec![Vec::new(); n];
    let mut between = vec![vec![Vec::new(); n]; n];
    for (i, p) in basis.iter().enumerate() {
        from[p.source() as usize].push(i);
        to[p.target() as usize].push(i);
        between[p.source() as usize][p.target() as usize].push(i);
    }
    (index_of, from, to, between)
}

/// The runtime algebra `kQ/I` over a checked prime field.
///
/// Construction runs the full pipeline: completion of the relations into the
/// reduced Groebner basis, certificate emission, independent verification of
/// the certificate, and the admissibility decision. The ideal is admissible:
/// `I ⊆ J²` holds term by term, and the arrow ideal `J` is nilpotent. Every
/// construction path decides nilpotence by iterating the radical step.
///
/// A normal word is a path that contains no Groebner leading word as a
/// factor. The basis is those words, in the fixed order: `basis[v]` is the
/// trivial path `e_v` for `v < num_vertices`. Remaining entries are sorted
/// by length, then source vertex, then lexicographic arrow word.
/// Multiplication tables store normal forms, so every product is exact.
///
/// ```
/// use auslander::algebra::dual_numbers;
/// use auslander::field::PrimeField;
/// let a = dual_numbers(PrimeField::new(5).unwrap());
/// assert_eq!(a.dim(), 2); // k[x]/(x²): basis e, x
/// ```
#[derive(Debug)]
pub struct Algebra {
    pub(super) quiver: Quiver,
    pub(super) field: PrimeField,
    pub(super) relations: Vec<Relation>,
    pub(super) certificate: Certificate,
    pub(super) limits: CompletionLimits,
    pub(super) basis: Vec<PathWord>,
    pub(super) index_of: FxHashMap<Vec<ArrowId>, BasisIdx>,
    pub(super) from: Vec<Vec<BasisIdx>>,
    pub(super) to: Vec<Vec<BasisIdx>>,
    pub(super) between: Vec<Vec<Vec<BasisIdx>>>,
    // right_mul[i][a] is NF(basis[i]·a) and left_mul[a][i] is NF(a·basis[i]),
    // each row sorted by basis index. Every word in a right_mul row runs from
    // the source of basis[i] to the target of a. Every word in a left_mul row
    // runs from the source of a to the target of basis[i].
    pub(super) right_mul: Vec<Vec<Vec<(BasisIdx, Fp)>>>,
    pub(super) left_mul: Vec<Vec<Vec<(BasisIdx, Fp)>>>,
    // The chain J^0 ⊇ J^1 ⊇ ... ⊇ J^d = 0, one entry per power, built once at
    // construction by radical_chain. The last index d is the nilpotency
    // degree. An Algebra is immutable and lives behind an Arc, so every
    // reader shares this one copy.
    pub(super) radical_powers: Vec<Vec<Vec<DenseMat>>>,
}
