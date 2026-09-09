use super::types::EuclideanType;

/// Rejected input for [`crate::dynkin::dynkin_indecomposables`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DynkinError {
    /// The algebra has relations, so it is a proper quotient of `kQ`.
    /// Gabriel's theorem lists the indecomposables of `kQ` itself.
    NonzeroIdeal {
        /// Number of elements in the algebra's reduced Groebner basis.
        relations: usize,
    },
    /// The underlying graph of the quiver is no Dynkin diagram, so `kQ` is not
    /// representation finite by Gabriel's theorem. `euclidean` reports the
    /// Euclidean type when the graph has one.
    NotDynkin {
        /// The Euclidean type of the underlying graph, when it has one.
        euclidean: Option<EuclideanType>,
    },
}

display_error! { error DynkinError {
    Self::NonzeroIdeal { relations } => "the algebra has {relations} relations; Gabriel's theorem needs the full path algebra";
    Self::NotDynkin { euclidean: None } => "the underlying graph is not a Dynkin diagram";
    Self::NotDynkin { euclidean: Some(t) } => "the underlying graph is {t}, not a Dynkin diagram";
} }
