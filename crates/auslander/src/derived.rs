//! Strict bounded transport for a split tilting target.
//!
//! The transport applies `Hom_A(T, -)` to terms with an
//! [`crate::basic::AddClosureWitness`].
//! Its inverse applies the checked target isomorphism to a stored projective
//! decomposition. It does not resolve arbitrary modules.

mod certificate;
mod transport;

pub use certificate::{
    DegreeZeroEndIdentification, DerivedCertificateError, DerivedEquivalenceCertificate,
    GradedHomotopyEndomorphisms,
};
pub use transport::{
    AddTComplex, ChainIsomorphism, ProjectiveTargetComplex, StrictTransport, TransportError,
};

#[cfg(test)]
mod tests;
