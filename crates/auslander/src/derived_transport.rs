//! Automatic transport through a checked classical tilting equivalence.

mod comparison;
mod model;
mod transport;

pub use model::ProjectiveAddTModel;
pub use transport::{
    DerivedForwardOutcome, DerivedForwardTransport, DerivedReverseOutcome, DerivedReverseTransport,
    DerivedTransport,
};

use crate::derived::TransportError;
use crate::hom::HomError;
use crate::homotopy::{BoundedComplexError, ChainMapError};
use crate::perfect::{QuasiIsomorphismError, ReplacementError};

/// Why automatic derived transport failed its next checked construction.
#[derive(Clone, Debug)]
pub enum DerivedTransportError {
    /// The derived-equivalence certificate did not verify.
    InvalidCertificate,
    /// A bounded complex failed construction.
    Complex(BoundedComplexError),
    /// A chain map or comparison failed construction.
    Chain(ChainMapError),
    /// A module morphism failed construction.
    Hom(HomError),
    /// A strict transport step failed.
    Strict(TransportError),
    /// A source or target replacement failed structurally.
    Replacement(ReplacementError),
    /// A quasi-isomorphism failed its cone check.
    QuasiIsomorphism(QuasiIsomorphismError),
    /// A projective coresolution stopped before zero.
    Coresolution { reason: String },
    /// A strict comparison map did not exist.
    Comparison,
    /// A degree calculation overflowed.
    DegreeOverflow,
}

display_error! { DerivedTransportError {
    Self::InvalidCertificate => "derived transport certificate does not verify";
    Self::Complex(error) => "derived transport complex failed: {error}";
    Self::Chain(error) => "derived transport chain map failed: {error}";
    Self::Hom(error) => "derived transport morphism failed: {error}";
    Self::Strict(error) => "strict derived transport failed: {error}";
    Self::Replacement(error) => "derived transport replacement failed: {error}";
    Self::QuasiIsomorphism(error) => "derived transport comparison is not a quasi-isomorphism: {error}";
    Self::Coresolution { reason } => "projective add(T) coresolution failed: {reason}";
    Self::Comparison => "projective add(T) comparison has no strict chain-map solution";
    Self::DegreeOverflow => "derived transport degree overflowed";
} }

error_source! { DerivedTransportError {
    Self::Complex(error) => Some(error),
    Self::Chain(error) => Some(error),
    Self::Hom(error) => Some(error),
    Self::Strict(error) => Some(error),
    Self::Replacement(error) => Some(error),
    Self::QuasiIsomorphism(error) => Some(error),
    _ => None,
} }

from_variants! { DerivedTransportError {
    BoundedComplexError => Complex,
    ChainMapError => Chain,
    HomError => Hom,
    TransportError => Strict,
    ReplacementError => Replacement,
    QuasiIsomorphismError => QuasiIsomorphism,
} }
