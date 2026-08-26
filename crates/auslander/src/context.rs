//! Memoized certified computations for one top-level verification.
//!
//! A [`VerificationContext`] holds one [`Memo`] per primitive a verification
//! repeats: the opposite algebra, `End`, `hom_dim`, `tau`, `decompose`, and
//! `pair_iso`. The invariant that makes it safe is quoted on the type.
//!
//! Two rules keep that invariant true. The context stores computations, never
//! witness verdicts: no `verify() -> bool` result is ever put in a memo, so a
//! hit can never stand in for a check. Every key carries the nominal identity
//! of its operands, the identity morphism endpoints already use, and owns
//! them, so two entrywise identical modules built separately are two entries.
//! A cache keyed by a caller label instead of module identity returned
//! another module's translate, and so called a module tau-rigid though its
//! `Hom(M, tau M)` is one dimensional.
//! `verification_context_separates_nominal_kronecker_modules` holds the two
//! modules that did it apart in every memo here.
//!
use std::collections::hash_map::Entry;
use std::convert::Infallible;
use std::fmt;
use std::hash::Hash;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use rustc_hash::FxHashMap;

use crate::algebra::{Algebra, AlgebraBuildError};
use crate::ar::TauError;
use crate::ar::tau_with_opposite;
use crate::basic::{
    BasicDecomposition, BasicError, ProjectiveSupport, SupportPairIsoOutcome, pair_iso,
};
use crate::decompose::Decomposition;
use crate::endo::EndoAlgebra;
use crate::hom::HomError;
use crate::module::Module;
use crate::opposite::OppositeMap;

/// The nominal identity of a module value, owning the module.
///
/// Equality is [`Module::ptr_eq`] and the hash is the module's address, so a
/// clone of a keyed module hits and a separately built module misses even when
/// it is entrywise identical. The key holds its own clone: a dropped module
/// frees its address for the next allocation, and a key that stored only the
/// number would then name a different module.
#[derive(Clone)]
pub(crate) struct ModuleKey(Module);

debug_fields!(
    /// Prints the address the key hashes and the dimension vector, not the module.
    /// A failed key comparison prints two keys, and the module carries its whole
    /// algebra.
    ModuleKey |this| {
    "addr" => this.0.addr();
    "dim_vector" => this.0.dim_vector();
});

impl ModuleKey {
    /// The key of `module`, cloning it into the key.
    pub(crate) fn new(module: &Module) -> ModuleKey {
        Self(module.clone())
    }

    accessor_methods! {
        /// The module the key names.
        #[cfg(test)]
        pub(crate) module() -> &Module = |this| &this.0;
    }
}

nominal_key!(ModuleKey, |this, other| this.0.ptr_eq(&other.0), |this| {
    this.0.addr()
});

/// The nominal identity of an algebra value, owning the [`Arc`].
///
/// Equality is [`Arc::ptr_eq`] and the hash is the pointer, matching the
/// crate's algebra identity policy: two algebras built from one presentation
/// are two values, and every cross-algebra check in the crate is
/// [`Arc::ptr_eq`]. The key owns its clone for the reason [`ModuleKey`] does.
#[derive(Clone)]
pub(crate) struct AlgebraKey(Arc<Algebra>);

debug_fields!(
    /// Prints the address the key hashes, not the algebra, for the reason
    /// [`ModuleKey`] does.
    AlgebraKey |this| {
    "addr" => Arc::as_ptr(&this.0) as usize;
});

impl AlgebraKey {
    /// The key of `algebra`, cloning the [`Arc`] into the key.
    pub(crate) fn new(algebra: &Arc<Algebra>) -> AlgebraKey {
        Self(algebra.clone())
    }
}

nominal_key!(
    AlgebraKey,
    |this, other| Arc::ptr_eq(&this.0, &other.0),
    |this| Arc::as_ptr(&this.0) as usize
);

/// The identity of a basic decomposition: the assembled module and the
/// summands in decomposition order.
///
/// The order is part of the key because it binds the returned morphisms.
/// [`crate::basic::pair_iso`] reports its bijection, inclusions, and
/// projections by summand position, so an entry computed under one order names
/// the wrong summands under another. The assembled module is part of it
/// because [`BasicDecomposition::without`] and
/// [`BasicDecomposition::with_new_summand`] reassemble a fresh module over
/// kept summand values, so the summand list alone does not fix it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct BasicKey {
    assembled: ModuleKey,
    summands: Box<[ModuleKey]>,
}

impl BasicKey {
    /// The key of `decomposition`, cloning the assembled module and every
    /// summand into the key.
    pub(crate) fn new(decomposition: &BasicDecomposition) -> BasicKey {
        let assembled = ModuleKey::new(decomposition.module());
        let summands = decomposition
            .summands()
            .iter()
            .map(|summand| ModuleKey::new(summand.module()))
            .collect();
        BasicKey {
            assembled,
            summands,
        }
    }
}

/// The identity of a projective support: the algebra and the sorted vertex
/// list.
///
/// The algebra is required. [`ProjectiveSupport`] compares equal on the vertex
/// list alone and deliberately ignores the algebra, so a key that copied that
/// equality would answer for a support over another algebra with the same
/// vertex numbering, and `P_0` of one algebra is not `P_0` of another.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SupportKey {
    algebra: AlgebraKey,
    vertices: Box<[u32]>,
}

impl SupportKey {
    /// The key of `support`, taking the vertices sorted and deduplicated as
    /// [`ProjectiveSupport`] stores them.
    pub(crate) fn new(support: &ProjectiveSupport) -> SupportKey {
        Self {
            algebra: AlgebraKey::new(support.algebra()),
            vertices: support.vertices().into(),
        }
    }
}

/// The identity of a basic pair `(M, P)`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct PairKey {
    module: BasicKey,
    projective: SupportKey,
}

impl PairKey {
    /// The key of the pair `(module, projective)`.
    pub(crate) fn new(module: &BasicDecomposition, projective: &ProjectiveSupport) -> PairKey {
        Self {
            module: BasicKey::new(module),
            projective: SupportKey::new(projective),
        }
    }
}

/// The results of one certified operation, keyed by the identity of its
/// operands.
///
/// [`Memo::get_or_compute`] is the only way in. There is no `insert`, no
/// `extend`, no constructor taking entries, and no `Default`, so a stored
/// value is the output of the closure that first asked for its key.
///
/// A failed computation stores its exact error and is not run again.
pub(crate) struct Memo<K, V, E> {
    cells: Mutex<FxHashMap<K, MemoCell<V, E>>>,
    hits: AtomicU64,
    misses: AtomicU64,
}

/// One result, or the error the computation reported. The outer [`Arc`] lets
/// [`Memo::get_or_compute`] drop the map lock before it runs the computation.
///
/// The error is stored, not discarded. A failure here can be a defect signal,
/// `TauError::RoutesDisagree` for instance, which says the two certified
/// routes disagree and the library has a bug. Collapsing that to a bare miss
/// would let the first caller see a defect and every later caller see an
/// ordinary absence. That is the one downgrade this crate must never make.
type MemoCell<V, E> = Arc<OnceLock<Result<Arc<V>, Arc<E>>>>;

impl<K: Eq + Hash, V, E> fmt::Debug for Memo<K, V, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Memo").field("len", &self.len()).finish()
    }
}

impl<K: Eq + Hash, V, E> Memo<K, V, E> {
    /// An empty memo.
    pub(crate) fn new() -> Memo<K, V, E> {
        Memo {
            cells: Mutex::new(FxHashMap::default()),
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
        }
    }

    /// The stored value for `key`, or the value `compute` returns after
    /// storing it.
    ///
    /// The map lock covers only finding or creating the cell. `compute` runs
    /// outside it, so one long computation blocks no other key, and two
    /// threads asking for one key run `compute` once.
    ///
    /// `compute` must not ask the memo it is filling for anything.
    /// [`OnceLock::get_or_init`] deadlocks when the closure re-enters its own
    /// cell, and two keys of one memo that ask for each other deadlock the
    /// same way. The memos of [`VerificationContext`] are declared in
    /// dependency order, and a closure may ask only for memos declared before
    /// its own. `tau` is the case that comes up: it needs the opposite
    /// algebra, which is declared first. No primitive needs its own memo. A
    /// stored error is returned to every later caller unchanged, so a defect
    /// stays a defect rather than becoming a miss.
    pub(crate) fn get_or_compute<F>(&self, key: K, compute: F) -> Result<Arc<V>, Arc<E>>
    where
        F: FnOnce() -> Result<V, E>,
    {
        let (cell, miss) = {
            let mut cells = self
                .cells
                .lock()
                .expect("the map lock covers one map operation, which does not panic");
            match cells.entry(key) {
                Entry::Occupied(entry) => (Arc::clone(entry.get()), false),
                Entry::Vacant(entry) => {
                    let cell = entry.insert(Arc::new(OnceLock::new()));
                    (Arc::clone(cell), true)
                }
            }
        };
        (if miss { &self.misses } else { &self.hits }).fetch_add(1, Ordering::Relaxed);
        cell.get_or_init(|| compute().map(Arc::new).map_err(Arc::new))
            .clone()
    }

    fn value<F>(&self, key: K, compute: F) -> Result<Arc<V>, E>
    where
        E: Clone,
        F: FnOnce() -> Result<V, E>,
    {
        self.get_or_compute(key, compute)
            .map_err(|error| (*error).clone())
    }

    accessor_methods! {
        /// The number of keys requested, counting a key whose computation
        /// failed or is still running on another thread. It is not a count of
        /// completed work.
        pub(crate) len() -> usize = |this| this.cells
            .lock()
            .expect("the map lock covers one map operation, which does not panic")
            .len();
        /// The requests answered by an existing key and the requests that created one.
        #[cfg(test)]
        stats() -> (u64, u64) = |this| (
            this.hits.load(Ordering::Relaxed),
            this.misses.load(Ordering::Relaxed),
        );
        /// Whether no key has been requested.
        #[cfg(test)]
        pub(crate) is_empty() -> bool = |this| this.len() == 0;
    }
}

/// The memos of one top-level verification.
///
/// > Every context entry is the output of the crate's certified operation,
/// > computed during the current top-level verification from the exact
/// > operands in its key. A hit replaces only a second call with identical
/// > operands. It never replaces an endpoint binding, witness check, or
/// > comparison against stored data.
///
/// [`VerificationContext::new`] is the only constructor and it is empty. There
/// is no `Default`, no `insert`, no constructor taking entries, no
/// serialization, and no clone of a warm context, so a context that reaches a
/// verifier holds only what that verification computed. The type is
/// `pub(crate)`, so no caller outside the crate can build one, warm one, or
/// hand one in.
///
/// The memos hold computations, never witness verdicts. Nothing of the form
/// `verify() -> bool` is stored.
///
/// The fields are declared in the dependency order [`Memo::get_or_compute`]
/// requires.
#[derive(Debug)]
pub(crate) struct VerificationContext {
    opposite: Memo<AlgebraKey, OppositeMap, AlgebraBuildError>,
    endo: Memo<ModuleKey, EndoAlgebra, Infallible>,
    hom_dim: Memo<(ModuleKey, ModuleKey), usize, HomError>,
    tau: Memo<ModuleKey, Module, TauError>,
    decompose: Memo<ModuleKey, Decomposition, Infallible>,
    pair_iso: Memo<(PairKey, PairKey), SupportPairIsoOutcome, BasicError>,
}

impl VerificationContext {
    /// An empty context.
    pub(crate) fn new() -> VerificationContext {
        VerificationContext {
            opposite: Memo::new(),
            endo: Memo::new(),
            hom_dim: Memo::new(),
            tau: Memo::new(),
            decompose: Memo::new(),
            pair_iso: Memo::new(),
        }
    }

    /// Gets the certified opposite map for one algebra value.
    pub(crate) fn opposite_for(
        &self,
        algebra: &Arc<Algebra>,
    ) -> Result<Arc<OppositeMap>, AlgebraBuildError> {
        self.opposite.value(AlgebraKey::new(algebra), || {
            crate::opposite::opposite(algebra)
        })
    }

    /// Gets `End(X)` for one module value.
    pub(crate) fn endo_for(&self, module: &Module) -> Arc<EndoAlgebra> {
        self.endo
            .value(ModuleKey::new(module), || Ok(EndoAlgebra::new(module)))
            .unwrap_or_else(|never| match never {})
    }

    /// Gets `dim Hom(X, Y)` for one ordered module pair.
    pub(crate) fn hom_dim_for(&self, source: &Module, target: &Module) -> Result<usize, HomError> {
        self.hom_dim
            .value((ModuleKey::new(source), ModuleKey::new(target)), || {
                crate::hom::hom_dim(source, target)
            })
            .map(|value| *value)
    }

    /// Gets the certified AR translate of one module value.
    pub(crate) fn tau_for(&self, module: &Module) -> Result<Arc<Module>, TauError> {
        self.tau.value(ModuleKey::new(module), || {
            let opposite = self
                .opposite_for(module.algebra())
                .map_err(TauError::Opposite)?;
            tau_with_opposite(module, &opposite)
        })
    }

    /// Gets the certified decomposition of one module value.
    pub(crate) fn decompose_for(&self, module: &Module) -> Arc<Decomposition> {
        self.decompose
            .value(ModuleKey::new(module), || {
                let root = (!module.is_zero()).then(|| self.endo_for(module).as_ref().clone());
                Ok(crate::decompose::decompose_with_root_endo(module, root))
            })
            .unwrap_or_else(|never| match never {})
    }

    /// Gets the certified identity outcome of one ordered basic-pair pair.
    pub(crate) fn pair_iso_for(
        &self,
        first_module: &BasicDecomposition,
        first_projective: &ProjectiveSupport,
        second_module: &BasicDecomposition,
        second_projective: &ProjectiveSupport,
    ) -> Result<Arc<SupportPairIsoOutcome>, BasicError> {
        self.pair_iso.value(
            (
                PairKey::new(first_module, first_projective),
                PairKey::new(second_module, second_projective),
            ),
            || {
                pair_iso(
                    first_module,
                    first_projective,
                    second_module,
                    second_projective,
                )
            },
        )
    }

    /// The requests answered from existing keys and the requests that created keys.
    #[cfg(test)]
    pub(crate) fn memo_stats(&self) -> (u64, u64) {
        let stats = [
            self.opposite.stats(),
            self.endo.stats(),
            self.hom_dim.stats(),
            self.tau.stats(),
            self.decompose.stats(),
            self.pair_iso.stats(),
        ];
        (
            stats.iter().map(|(hits, _)| hits).sum(),
            stats.iter().map(|(_, misses)| misses).sum(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::algebra::{kronecker, linear_an};
    use crate::ar::tau;
    use crate::basic::pair_iso;
    use crate::decompose::decompose;
    use crate::field::PrimeField;
    use crate::hom::hom_dim;
    use crate::iso::{IsoOutcome, is_isomorphic};
    use crate::linalg::DenseMat;

    fn fields() -> [PrimeField; 2] {
        [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
    }

    /// The two `(1, 1)` Kronecker modules `k --1--> k, k --0--> k` and its
    /// mirror. Both are regular with `tau X` isomorphic to `X`, they are not
    /// isomorphic to each other, and `Hom` between them is zero.
    fn kronecker_pair(field: PrimeField) -> (Module, Module) {
        let algebra = kronecker(2, field);
        let one = DenseMat::from_rows(&[vec![field.one()]]);
        let zero = DenseMat::zero(1, 1);
        let build = |maps: Vec<DenseMat>| {
            Module::new(algebra.clone(), vec![1, 1], maps).expect("a kronecker representation")
        };
        (
            build(vec![one.clone(), zero.clone()]),
            build(vec![zero, one]),
        )
    }

    fn basic(m: &Module) -> BasicDecomposition {
        BasicDecomposition::new(m).expect("a kronecker regular module is indecomposable")
    }

    // The v0.5 defect this type exists to prevent. X and Y share the dimension
    // vector (1, 1) and are not isomorphic, tau X is X and tau Y is Y, and Hom
    // between them is zero. A cache keyed by a caller index answered the
    // second question with tau X and called Y tau-rigid, which it is not:
    // dim Hom(Y, tau Y) is 1. Every memo below is warmed with X and then asked
    // for Y. Weakening ModuleKey to the dimension vector makes the entry for Y
    // the entry for X, and the first assertion then reads Hom(Y, tau Y) as 0,
    // which is the certification the defect granted.
    #[test]
    fn verification_context_separates_nominal_kronecker_modules() {
        for field in fields() {
            let (x, y) = kronecker_pair(field);
            let context = VerificationContext::new();

            let tau_x = context
                .tau
                .get_or_compute(ModuleKey::new(&x), || tau(&x))
                .expect("kronecker translates");
            let tau_y = context
                .tau
                .get_or_compute(ModuleKey::new(&y), || tau(&y))
                .expect("kronecker translates");
            // The certification a collapsed key would grant: Hom(Y, tau Y)
            // is one dimensional, and Hom(Y, tau X) is zero.
            assert_eq!(hom_dim(&y, &tau_y).expect("one algebra"), 1);
            assert_eq!(hom_dim(&y, &tau_x).expect("one algebra"), 0);
            assert_eq!(context.tau.len(), 2);
            let uncached = tau(&y).expect("kronecker translates");
            assert!(matches!(
                is_isomorphic(&tau_y, &uncached).expect("one algebra"),
                IsoOutcome::Isomorphic(_)
            ));

            let endo_x = context
                .endo
                .get_or_compute(ModuleKey::new(&x), || Ok(EndoAlgebra::new(&x)))
                .expect("End is total");
            let endo_y = context
                .endo
                .get_or_compute(ModuleKey::new(&y), || Ok(EndoAlgebra::new(&y)))
                .expect("End is total");
            assert_eq!(context.endo.len(), 2);
            assert!(endo_x.module().ptr_eq(&x));
            assert!(endo_y.module().ptr_eq(&y));

            let split_x = context
                .decompose
                .get_or_compute(ModuleKey::new(&x), || Ok(decompose(&x)))
                .expect("decompose is total");
            let split_y = context
                .decompose
                .get_or_compute(ModuleKey::new(&y), || Ok(decompose(&y)))
                .expect("decompose is total");
            assert_eq!(context.decompose.len(), 2);
            assert!(split_x.split().total().ptr_eq(&x));
            assert!(split_y.split().total().ptr_eq(&y));

            let mut dims = Vec::new();
            for (source, target) in [(&x, &x), (&x, &y), (&y, &x), (&y, &y)] {
                let key = (ModuleKey::new(source), ModuleKey::new(target));
                dims.push(
                    *context
                        .hom_dim
                        .get_or_compute(key, || hom_dim(source, target))
                        .expect("one algebra"),
                );
            }
            assert_eq!(context.hom_dim.len(), 4);
            assert_eq!(dims, vec![1, 0, 0, 1]);

            let (dec_x, dec_y) = (basic(&x), basic(&y));
            let support = ProjectiveSupport::new(x.algebra(), &[]).expect("the empty support");
            let (key_x, key_y) = (
                PairKey::new(&dec_x, &support),
                PairKey::new(&dec_y, &support),
            );
            let same = context
                .pair_iso
                .get_or_compute((key_x.clone(), key_x.clone()), || {
                    pair_iso(&dec_x, &support, &dec_x, &support)
                })
                .expect("both pairs are certified");
            let cross = context
                .pair_iso
                .get_or_compute((key_x, key_y), || {
                    pair_iso(&dec_x, &support, &dec_y, &support)
                })
                .expect("both pairs are certified");
            assert_eq!(context.pair_iso.len(), 2);
            assert!(matches!(*same, SupportPairIsoOutcome::Isomorphic(_)));
            assert!(matches!(*cross, SupportPairIsoOutcome::NotIsomorphic(_)));

            // The opposite algebra is keyed by the algebra, which X and Y
            // share, so one entry answers both.
            for module in [&x, &y] {
                context
                    .opposite
                    .get_or_compute(AlgebraKey::new(module.algebra()), || {
                        crate::opposite::opposite(module.algebra())
                    })
                    .expect("the kronecker algebra has an opposite");
            }
            assert_eq!(context.opposite.len(), 1);
        }
    }

    // A hit returns the value the first closure produced, not an equal one.
    #[test]
    fn the_second_request_for_one_key_returns_the_stored_value() {
        let (x, _) = kronecker_pair(fields()[1]);
        let context = VerificationContext::new();
        let first = context
            .tau
            .get_or_compute(ModuleKey::new(&x), || tau(&x))
            .expect("kronecker translates");
        let second = context
            .tau
            .get_or_compute(ModuleKey::new(&x), || {
                unreachable!("a stored entry answers the second request")
            })
            .expect("kronecker translates");
        assert!(Arc::ptr_eq(&first, &second));
        assert_eq!(context.tau.len(), 1);
    }

    // A failure is an entry too, so a second request does not run the
    // computation again, and the second caller sees the same error. A defect
    // signal must not decay into a bare absence between callers.
    #[test]
    fn a_stored_failure_answers_later_callers_with_the_same_error() {
        let (x, _) = kronecker_pair(fields()[1]);
        let memo: Memo<ModuleKey, usize, String> = Memo::new();
        let first = memo
            .get_or_compute(ModuleKey::new(&x), || Err("routes disagree".into()))
            .expect_err("the computation failed");
        assert_eq!(memo.len(), 1);
        let second = memo
            .get_or_compute(ModuleKey::new(&x), || {
                unreachable!("a stored failure answers the second request")
            })
            .expect_err("the stored failure is returned again");
        assert_eq!(*second, "routes disagree");
        assert!(Arc::ptr_eq(&first, &second));
    }

    #[test]
    fn a_new_verification_context_holds_no_entries() {
        let context = VerificationContext::new();
        assert!(context.opposite.is_empty());
        assert!(context.endo.is_empty());
        assert!(context.hom_dim.is_empty());
        assert!(context.tau.is_empty());
        assert!(context.decompose.is_empty());
        assert!(context.pair_iso.is_empty());
    }

    // The key owns its module, so the address it hashes stays that module's
    // address. Without the owned clone the module below would be freed at the
    // end of the statement and a later module could take its address.
    #[test]
    fn a_module_key_keeps_its_address_out_of_later_allocations() {
        let algebra = kronecker(2, fields()[1]);
        let key = ModuleKey::new(&Module::simple(&algebra, 0));
        for _ in 0..64 {
            let later = Module::simple(&algebra, 0);
            assert_ne!(key, ModuleKey::new(&later));
        }
        assert_eq!(key, ModuleKey::new(key.module()));
    }

    // ProjectiveSupport compares vertex lists and ignores the algebra, so the
    // support alone cannot key an entry.
    #[test]
    fn a_support_key_separates_two_algebras_whose_supports_compare_equal() {
        let field = fields()[1];
        let (first, second) = (kronecker(2, field), kronecker(2, field));
        let a = ProjectiveSupport::new(&first, &[0]).expect("vertex 0 is a vertex");
        let b = ProjectiveSupport::new(&second, &[0]).expect("vertex 0 is a vertex");
        assert_eq!(a, b);
        assert_ne!(SupportKey::new(&a), SupportKey::new(&b));
    }

    // pair_iso returns its bijection by summand position, so the summand order
    // is part of the key.
    #[test]
    fn a_basic_key_separates_two_orders_of_one_summand_list() {
        let (x, y) = kronecker_pair(fields()[1]);
        let (sum, _, _) = crate::module::direct_sum(&[&x, &y]);
        let assembled = ModuleKey::new(&sum);
        let forward = BasicKey {
            assembled: assembled.clone(),
            summands: Box::new([ModuleKey::new(&x), ModuleKey::new(&y)]),
        };
        let backward = BasicKey {
            assembled,
            summands: Box::new([ModuleKey::new(&y), ModuleKey::new(&x)]),
        };
        assert_ne!(forward, backward);
    }

    // Hom is not symmetric, so the memo key is the ordered pair.
    #[test]
    fn the_hom_dim_key_separates_the_two_orders_of_one_module_pair() {
        let algebra = linear_an(2, fields()[1]);
        let projective = Module::projective(&algebra, 0);
        let simple = Module::simple(&algebra, 0);
        let forward = hom_dim(&projective, &simple).expect("one algebra");
        let backward = hom_dim(&simple, &projective).expect("one algebra");
        assert_ne!(
            forward, backward,
            "the fixture has to be asymmetric for the memo test below to bite"
        );
        let context = VerificationContext::new();
        let mut stored = Vec::new();
        for (source, target) in [(&projective, &simple), (&simple, &projective)] {
            let key = (ModuleKey::new(source), ModuleKey::new(target));
            stored.push(
                *context
                    .hom_dim
                    .get_or_compute(key, || hom_dim(source, target))
                    .expect("one algebra"),
            );
        }
        assert_eq!(context.hom_dim.len(), 2);
        assert_eq!(stored, vec![forward, backward]);
    }

    // The parallel walk shares one context across worker threads.
    #[test]
    fn a_verification_context_is_shareable_across_threads() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<VerificationContext>();
    }
}
