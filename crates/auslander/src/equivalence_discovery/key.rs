use crate::control::WorkMeter;
use crate::perfect::ProjectiveComplex;
use crate::tilting_complex::{CertifiedSiltingComplex, Interrupt, summands_isomorphic};

/// The sorted summand shapes of a silting complex with minimal summands.
///
/// A summand shape is the lower degree and the canonical-projective
/// multiplicities of each term. Isomorphic minimal complexes have equal
/// shapes, so the key depends neither on summand order nor on the mutation
/// path to the vertex. Distinct vertices can share a key.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TiltingComplexKey(String);

impl TiltingComplexKey {
    /// Builds the key from the sorted shapes of the summands.
    pub fn new(complex: &CertifiedSiltingComplex) -> TiltingComplexKey {
        let mut shapes: Vec<String> = complex
            .candidate()
            .summands()
            .iter()
            .map(summand_shape)
            .collect();
        shapes.sort();
        TiltingComplexKey(shapes.join("|"))
    }

    /// The canonical key bytes.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// The lower degree and the canonical-projective multiplicities of each term.
fn summand_shape(summand: &ProjectiveComplex) -> String {
    let complex = summand.complex();
    let vertices = complex.terms()[0].algebra().quiver().num_vertices() as usize;
    let terms: Vec<Vec<usize>> = summand
        .terms()
        .iter()
        .map(|term| {
            let mut counts = vec![0; vertices];
            term.vertices()
                .iter()
                .for_each(|&vertex| counts[vertex as usize] += 1);
            counts
        })
        .collect();
    format!("{}:{terms:?}", complex.lower())
}

/// Whether two certified tilting complexes are isomorphic in `K^b(proj A)`.
///
/// Summands of a certified tilting complex are pairwise non-isomorphic with
/// local endomorphism rings. So each summand of `left` matches at most one
/// summand of `right`, and distinct summands of `left` match distinct ones.
/// The complexes are isomorphic exactly when they have equally many summands
/// and every summand of `left` has a match. Only summands of equal shape are
/// compared.
pub(super) fn isomorphic(
    left: &CertifiedSiltingComplex,
    right: &CertifiedSiltingComplex,
    meter: &mut WorkMeter,
) -> Result<bool, Interrupt> {
    let shapes: Vec<String> = right
        .candidate()
        .summands()
        .iter()
        .map(summand_shape)
        .collect();
    if left.candidate().len() != shapes.len() {
        return Ok(false);
    }
    for (index, summand) in left.candidate().summands().iter().enumerate() {
        let shape = summand_shape(summand);
        let mut matched = false;
        for other in (0..shapes.len()).filter(|&other| shapes[other] == shape) {
            if summands_isomorphic(left, index, right, other, meter)? {
                matched = true;
                break;
            }
        }
        if !matched {
            return Ok(false);
        }
    }
    Ok(true)
}
