use std::sync::Arc;

use crate::algebra::Algebra;
use crate::decompose::Certificate;
use crate::dynkin::{DynkinError, dynkin_indecomposables};
use crate::enumerate::{EnumerateError, nakayama_indecomposables};
use crate::indec::IndecomposableModule;
use crate::module::Module;

/// Which classification theorem lists the entries of a catalog.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CatalogProvenance {
    /// The Nakayama classification: the indecomposables of a Nakayama algebra
    /// are the uniserial quotients `P_i / rad^l P_i`.
    Nakayama,
    /// Gabriel's theorem: the indecomposables of a path algebra of Dynkin
    /// type are one per positive root of the underlying graph.
    DynkinZeroIdeal,
}

display_error! { CatalogProvenance {
    Self::Nakayama => "Nakayama classification";
    Self::DynkinZeroIdeal => "Gabriel's theorem";
} }

/// A complete list of the indecomposable modules of one algebra, each
/// certified by its local endomorphism algebra.
///
/// Fields are private, and the only constructors are
/// [`IndecomposableCatalog::nakayama`] and [`IndecomposableCatalog::dynkin`],
/// which wrap the two complete enumerations of the crate. A plain list of
/// modules never becomes a catalog, so a value of this type carries the
/// completeness of its [`CatalogProvenance`].
///
/// Entry order is enumerator order. The stable identifier of an entry is its
/// index.
pub struct IndecomposableCatalog {
    algebra: Arc<Algebra>,
    provenance: CatalogProvenance,
    // Shared, so an AR vertex can hold its entry without running the
    // locality gate a second time.
    entries: Vec<Arc<IndecomposableModule>>,
}

debug_fields!(IndecomposableCatalog |this| {
    "provenance" => this.provenance;
    "entries" => this.entries.len();
});

/// Puts every listed module through the indecomposability gate.
///
/// # Panics
/// Panics when the gate rejects a module the enumerator listed. Both
/// enumerators list only modules their classification theorem proves
/// indecomposable, and both attach a [`Certificate`], so a rejection is a
/// crate defect.
fn certified_entries(listed: Vec<(Module, Certificate)>) -> Vec<Arc<IndecomposableModule>> {
    listed
        .into_iter()
        .map(|(m, certificate)| {
            Arc::new(IndecomposableModule::new(&m).unwrap_or_else(|error| {
                panic!(
                    "the enumerator listed the module {:?} with certificate {certificate:?}, \
                     and the locality gate rejected it: {error}; crate defect",
                    m.dim_vector()
                )
            }))
        })
        .collect()
}

impl IndecomposableCatalog {
    /// The indecomposables of a Nakayama algebra, in the order of
    /// [`nakayama_indecomposables`].
    ///
    /// # Errors
    /// [`EnumerateError`] when the algebra is not Nakayama.
    pub fn nakayama(algebra: &Arc<Algebra>) -> Result<IndecomposableCatalog, EnumerateError> {
        let listed = nakayama_indecomposables(algebra)?;
        Ok(IndecomposableCatalog {
            algebra: algebra.clone(),
            provenance: CatalogProvenance::Nakayama,
            entries: certified_entries(listed),
        })
    }

    /// The indecomposables of a path algebra of Dynkin type, in the order of
    /// [`dynkin_indecomposables`].
    ///
    /// # Errors
    /// [`DynkinError`] when the algebra has relations or the underlying graph
    /// of its quiver is no Dynkin diagram.
    pub fn dynkin(algebra: &Arc<Algebra>) -> Result<IndecomposableCatalog, DynkinError> {
        let listed = dynkin_indecomposables(algebra)?;
        Ok(IndecomposableCatalog {
            algebra: algebra.clone(),
            provenance: CatalogProvenance::DynkinZeroIdeal,
            entries: certified_entries(listed),
        })
    }

    accessor_methods! {
        /// The algebra the entries are modules over.
        pub algebra() -> &Arc<Algebra> = |this| &this.algebra;
        /// The classification theorem that makes the list complete.
        pub provenance() -> CatalogProvenance = |this| this.provenance;
        /// The entries in enumerator order. An entry's index is its identifier.
        pub entries() -> &[Arc<IndecomposableModule>] = |this| &this.entries;
        /// The number of entries.
        pub len() -> usize = |this| this.entries.len();
        /// Whether the catalog has no entries. An algebra with at least one
        /// vertex has at least one simple module, so both enumerators return a
        /// nonempty list.
        pub is_empty() -> bool = |this| this.entries.is_empty();
    }
}
