use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::sync::Arc;

use crate::algebra::{Algebra, AlgebraBuildError};
use crate::ar::{TauError, tau_with_opposite};
use crate::module::Module;
use crate::opposite::{OppositeMap, opposite};
use crate::profile::{Site, hit};

/// Opposite algebras kept by the address of their [`Arc<Algebra>`].
///
/// Building an opposite algebra runs the completion and verification pipeline,
/// and every `tau` needs one. The stored [`Arc`] keeps the algebra alive, so
/// the key address stays allocated and no later algebra can reuse it while the
/// entry lives.
#[derive(Clone, Debug, Default)]
struct OppositeCache {
    entries: HashMap<usize, (Arc<Algebra>, OppositeMap)>,
}

impl OppositeCache {
    fn get(&mut self, algebra: &Arc<Algebra>) -> Result<&OppositeMap, AlgebraBuildError> {
        let key = Arc::as_ptr(algebra) as usize;
        match self.entries.entry(key) {
            Entry::Occupied(slot) => Ok(&slot.into_mut().1),
            Entry::Vacant(slot) => {
                let map = opposite(algebra)?;
                Ok(&slot.insert((algebra.clone(), map)).1)
            }
        }
    }
}

/// AR translates kept by the nominal identity of the module they belong to.
///
/// Module identity in this crate is nominal ([`Module::ptr_eq`]), so the key
/// is the address of the module value and the entry keeps a clone of it. A
/// clone of a stored module hits. A separately built module misses, even when
/// it is isomorphic to a stored one: recognizing that would take a certified
/// isomorphism test against every entry of the same dimension vector, and an
/// uncertified guess is what made an earlier cache return the wrong translate
/// for two of the `kronecker(2)` indecomposables. A miss costs one `tau` and
/// never a wrong answer. Callers that hold a decomposition avoid the miss by
/// keeping the summand values, as [`crate::basic::BasicDecomposition::without`]
/// does.
///
/// The cache also holds the opposite algebra of every algebra it has seen,
/// which the design measured at 25 to 45 percent of a `tau` on an
/// indecomposable.
#[derive(Debug, Default)]
pub struct TauCache {
    opposite: OppositeCache,
    entries: HashMap<usize, CacheEntry>,
    hits: u64,
    misses: u64,
}

#[derive(Clone, Debug)]
struct CacheEntry {
    // The module the key addresses. Holding it keeps that address allocated,
    // so no later module can take the key while the entry lives.
    module: Module,
    translate: Module,
}

impl TauCache {
    /// An empty cache.
    pub fn new() -> TauCache {
        TauCache::default()
    }

    /// The translate of `x`, computed on a miss and returned from the store
    /// on a hit.
    ///
    /// A hit needs `x` to be a clone of a module already passed in. Two
    /// isomorphic modules built separately are two entries.
    pub fn tau_of(&mut self, x: &Module) -> Result<&Module, TauError> {
        hit(Site::TauCacheLookup);
        let key = x.addr();
        if self.entries.contains_key(&key) {
            debug_assert!(
                self.entries[&key].module.ptr_eq(x),
                "TauCache: the entry keeps its module alive, so the key cannot be reused"
            );
            self.hits += 1;
        } else {
            let op = self.opposite.get(x.algebra()).map_err(TauError::Opposite)?;
            let translate = tau_with_opposite(x, op)?;
            self.misses += 1;
            self.entries.insert(
                key,
                CacheEntry {
                    module: x.clone(),
                    translate,
                },
            );
        }
        Ok(&self.entries[&key].translate)
    }

    accessor_methods! {
        /// The number of stored translates.
        pub len() -> usize = |this| this.entries.len();
        /// Whether the cache holds no translate.
        pub is_empty() -> bool = |this| this.entries.is_empty();
        /// The number of [`TauCache::tau_of`] calls answered from the store.
        pub hits() -> u64 = |this| this.hits;
        /// The number of [`TauCache::tau_of`] calls that computed a translate.
        pub misses() -> u64 = |this| this.misses;
    }
}
