use crate::quiver::ArrowId;
use crate::tilting_complex::CertifiedTiltingComplex;

/// Stable matrix data for one ordered tilting-complex candidate.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TiltingComplexKey(String);

impl TiltingComplexKey {
    /// Builds the key from degree, dimension-vector, action, and differential data.
    pub fn new(tilting: &CertifiedTiltingComplex) -> TiltingComplexKey {
        let mut text = String::new();
        for summand in tilting.candidate().summands() {
            let complex = summand.complex();
            text.push_str(&format!("{}:{}[", complex.lower(), complex.upper()));
            for term in complex.terms() {
                text.push_str(&format!("{:?}", term.dim_vector()));
                for arrow in 0..term.algebra().quiver().num_arrows() {
                    text.push_str(&format!(
                        "{:?}",
                        term.map(ArrowId(arrow as u32)).entries_u64()
                    ));
                }
                text.push(';');
            }
            text.push('|');
            for differential in complex.differentials() {
                for vertex in 0..complex.terms()[0].algebra().quiver().num_vertices() {
                    text.push_str(&format!("{:?}", differential.map_at(vertex).entries_u64()));
                }
                text.push(';');
            }
            text.push(']');
        }
        TiltingComplexKey(text)
    }

    /// The canonical key bytes.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}
