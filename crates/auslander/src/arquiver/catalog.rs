use std::sync::Arc;

use crate::algebra::Algebra;
use crate::decompose::Certificate;
use crate::dynkin::{DynkinError, dynkin_indecomposables};
use crate::enumerate::{EnumerateError, nakayama_indecomposables};
use crate::gentle::{GentleError, gentle_tree_indecomposables};
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
    /// The string classification for a gentle algebra whose underlying graph
    /// is a tree. There are no band modules because a tree has no closed
    /// reduced walk.
    GentleTree,
}

display_error! { CatalogProvenance {
    Self::Nakayama => "Nakayama classification";
    Self::DynkinZeroIdeal => "Gabriel's theorem";
    Self::GentleTree => "the string classification for a gentle tree";
} }

/// Rejected automatic catalog selection, with the reason for each route.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CatalogError {
    /// Dynkin, Nakayama, and gentle-tree classifications all reject the
    /// algebra.
    UnsupportedDomain {
        /// Why Gabriel's theorem does not apply.
        dynkin: DynkinError,
        /// Why the Nakayama classification does not apply.
        nakayama: EnumerateError,
        /// Why the gentle-tree string classification does not apply.
        gentle: GentleError,
    },
}

display_error! { error CatalogError {
    Self::UnsupportedDomain { dynkin, nakayama, gentle } => "no complete enumeration applies: the Dynkin route reports {dynkin}, the Nakayama route reports {nakayama}, and the gentle-tree route reports {gentle}";
} }

/// A complete list of the indecomposable modules of one algebra, each
/// certified by its local endomorphism algebra.
///
/// Fields are private. The route constructors
/// [`IndecomposableCatalog::nakayama`], [`IndecomposableCatalog::dynkin`], and
/// [`IndecomposableCatalog::gentle_tree`] wrap the three complete
/// enumerations. [`IndecomposableCatalog::complete`] selects the first route
/// that applies. A plain list of modules never becomes a catalog, so a value
/// of this type carries the completeness of its [`CatalogProvenance`].
///
/// Entry order is enumerator order. The stable identifier of an entry is its
/// index.
#[derive(Clone)]
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
/// Panics when the gate rejects a module the enumerator listed. The route
/// constructors list only modules their classification theorem proves
/// indecomposable, and attach a [`Certificate`], so a rejection is a crate
/// defect.
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

    /// The indecomposables of a gentle algebra with a tree as its underlying
    /// graph, in canonical endpoint order.
    ///
    /// # Errors
    /// [`GentleError`] when the checked reduced presentation is not a gentle
    /// tree algebra.
    pub fn gentle_tree(algebra: &Arc<Algebra>) -> Result<IndecomposableCatalog, GentleError> {
        let listed = gentle_tree_indecomposables(algebra)?;
        Ok(IndecomposableCatalog {
            algebra: algebra.clone(),
            provenance: CatalogProvenance::GentleTree,
            entries: certified_entries(listed),
        })
    }

    /// Selects the first complete classification that applies to `algebra`.
    ///
    /// The order is Dynkin, Nakayama, then gentle tree. The first two routes
    /// retain their existing precedence.
    ///
    /// # Errors
    /// [`CatalogError::UnsupportedDomain`] when all three classifications
    /// reject the algebra.
    pub fn complete(algebra: &Arc<Algebra>) -> Result<IndecomposableCatalog, CatalogError> {
        let dynkin = match Self::dynkin(algebra) {
            Ok(catalog) => return Ok(catalog),
            Err(error) => error,
        };
        let nakayama = match Self::nakayama(algebra) {
            Ok(catalog) => return Ok(catalog),
            Err(error) => error,
        };
        Self::gentle_tree(algebra).map_err(|gentle| CatalogError::UnsupportedDomain {
            dynkin,
            nakayama,
            gentle,
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
        /// vertex has at least one simple module, so the enumerators return a
        /// nonempty list.
        pub is_empty() -> bool = |this| this.entries.is_empty();
    }
}
