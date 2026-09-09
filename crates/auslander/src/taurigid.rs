//! Tau-rigidity, decided one indecomposable at a time.
//!
//! A module `M` is tau-rigid when `Hom(M, tau M) = 0`. A vanishing claim has
//! no element to exhibit, so [`TauRigidModule`] stores no positive witness:
//! its private construction is the proof token, and
//! [`TauRigidModule::verify`] recomputes every translate and every dimension.
//! The negative answer does have an element to exhibit, and
//! [`NonTauRigidWitness`] carries it.
//!
//! Both `tau` and `Hom` are additive, so for `M = X_1 + ... + X_s`,
//! `Hom(M, tau M) = 0` exactly when `hom_dim(X_i, tau X_j) = 0` for every
//! ordered pair `(i, j)`. [`is_tau_rigid_summandwise`] decides that way, with
//! `tau` computed once per summand and kept in a [`TauCache`]. The identity
//! holds for any direct-sum decomposition, not only indecomposables.
//! Indecomposable summands are what reuse cache entries.
//!
//! Every `tau` still runs both routes of [`crate::ar`] and cross-checks them
//! with [`crate::iso::is_isomorphic`]. On an indecomposable the check is cheap.

mod cache;
mod decision;
mod types;

pub use cache::TauCache;
pub(crate) use decision::is_tau_rigid_summandwise_with_context;
pub use decision::{is_tau_rigid, is_tau_rigid_summandwise};
pub use types::{NonTauRigidWitness, TauRigidError, TauRigidModule, TauRigidityOutcome};

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::algebra::{Algebra, commutative_square, linear_an, truncated_poly};
    use crate::ar::tau;
    use crate::arquiver::IndecomposableCatalog;
    use crate::dynkin::{DynkinType, dynkin_quiver};
    use crate::field::PrimeField;
    use crate::hom::{hom_dim, zero_morphism};
    use crate::iso::{IsoOutcome, is_isomorphic};
    use crate::linalg::DenseMat;
    use crate::module::Module;
    use crate::module::direct_sum;

    fn fields() -> [PrimeField; 2] {
        [PrimeField::new(2).unwrap(), PrimeField::new(5).unwrap()]
    }

    fn d4(field: PrimeField) -> Arc<Algebra> {
        let quiver = dynkin_quiver(DynkinType::D(4)).expect("D_4 has a quiver");
        crate::algebra::path_algebra(quiver, field)
            .expect("the zero ideal over an acyclic quiver completes")
    }

    fn tp3(field: PrimeField) -> Arc<Algebra> {
        truncated_poly(3, field).expect("k[x]/(x^3) is admissible")
    }

    /// The uniserial `k[x]/(x^m)` over `k[x]/(x^n)`, as a module of dimension
    /// `m`. On the basis `1, x, ..., x^(m-1)` the loop sends each element to
    /// the next and the last to zero, so the row-vector matrix has ones on the
    /// superdiagonal.
    fn uniserial(algebra: &Arc<Algebra>, m: usize) -> Module {
        let field = algebra.field();
        let mut action = DenseMat::zero(m, m);
        for i in 0..m.saturating_sub(1) {
            action.set(i, i + 1, field.one());
        }
        Module::new(algebra.clone(), vec![m], vec![action]).expect("a Jordan block is a module")
    }

    /// The fixture algebras with a module list each, named for failure
    /// messages. The additivity identity holds for any direct-sum
    /// decomposition, so the lists need not be catalogs. The commutative-square
    /// list mixes simples, projectives, and injectives.
    fn fixtures(field: PrimeField) -> Vec<(String, Vec<Module>)> {
        let mut out = Vec::new();
        for n in [2usize, 3] {
            let algebra = linear_an(n, field);
            let catalog = IndecomposableCatalog::dynkin(&algebra).expect("A_n is Dynkin");
            let modules = catalog
                .entries()
                .iter()
                .map(|e| e.module().clone())
                .collect();
            out.push((format!("A_{n} over F_{}", field.modulus()), modules));
        }
        let tp = tp3(field);
        out.push((
            format!("truncated_poly(3) over F_{}", field.modulus()),
            (1..=3).map(|m| uniserial(&tp, m)).collect(),
        ));
        let cs = commutative_square(field);
        let mut square = Vec::new();
        for v in 0..cs.quiver().num_vertices() {
            square.push(Module::simple(&cs, v));
            square.push(Module::projective(&cs, v));
            square.push(Module::injective(&cs, v));
        }
        out.push((
            format!("commutative_square over F_{}", field.modulus()),
            square,
        ));
        out
    }

    /// Every subset of `0..n` of size at most three, in lexicographic order.
    fn subsets_up_to_three(n: usize) -> Vec<Vec<usize>> {
        let mut out = vec![Vec::new()];
        for i in 0..n {
            out.push(vec![i]);
            for j in i + 1..n {
                out.push(vec![i, j]);
                for k in j + 1..n {
                    out.push(vec![i, j, k]);
                }
            }
        }
        out
    }

    fn indexed(modules: &[Module], subset: &[usize]) -> Vec<(usize, Module)> {
        subset.iter().map(|&i| (i, modules[i].clone())).collect()
    }

    /// `sum_{i, j} dim Hom(X_i, tau X_j)`, the summandwise reading.
    fn summandwise_dim(summands: &[(usize, Module)], cache: &mut TauCache) -> usize {
        let translates: Vec<Module> = summands
            .iter()
            .map(|(_, x)| cache.tau_of(x).expect("the fixture translates").clone())
            .collect();
        let mut total = 0;
        for (_, x) in summands {
            for translate in &translates {
                if !translate.is_zero() {
                    total += hom_dim(x, translate).expect("one algebra");
                }
            }
        }
        total
    }

    /// `dim Hom(M, tau M)` with `M` assembled and `tau` called on it. Production
    /// code does not take this route.
    fn assembled_dim(modules: &[&Module]) -> usize {
        if modules.is_empty() {
            return 0;
        }
        let (m, _, _) = direct_sum(modules);
        let t = tau(&m).expect("the fixture translates");
        if t.is_zero() {
            0
        } else {
            hom_dim(&m, &t).expect("one algebra")
        }
    }

    fn expect_rigid(outcome: TauRigidityOutcome) -> TauRigidModule {
        match outcome {
            TauRigidityOutcome::TauRigid(rigid) => rigid,
            TauRigidityOutcome::NotTauRigid(witness) => {
                panic!(
                    "expected tau-rigid, got a witness at {:?}",
                    (witness.source_index(), witness.target_index())
                )
            }
        }
    }

    fn expect_not_rigid(outcome: TauRigidityOutcome) -> NonTauRigidWitness {
        match outcome {
            TauRigidityOutcome::NotTauRigid(witness) => witness,
            TauRigidityOutcome::TauRigid(_) => panic!("expected a nonzero witness"),
        }
    }

    #[test]
    fn the_cached_double_route_matches_the_uncached_one() {
        for field in fields() {
            for (name, modules) in fixtures(field) {
                let mut cache = TauCache::new();
                for (index, x) in modules.iter().enumerate() {
                    let cached = cache.tau_of(x).expect("the fixture translates").clone();
                    let plain = tau(x).expect("the fixture translates");
                    assert_eq!(
                        cached.is_zero(),
                        plain.is_zero(),
                        "{name}: one route called module {index} projective"
                    );
                    assert!(
                        cached.is_zero()
                            || matches!(
                                is_isomorphic(&cached, &plain),
                                Ok(IsoOutcome::Isomorphic(_))
                            ),
                        "{name}: cached and plain translates of module {index} differ"
                    );
                }
            }
        }
    }

    #[test]
    fn cache_counters_are_exact_and_a_hit_repeats_the_miss_value() {
        let algebra = linear_an(3, PrimeField::new(5).unwrap());
        let s0 = Module::simple(&algebra, 0);
        let s1 = Module::simple(&algebra, 1);
        let mut cache = TauCache::new();
        assert!(cache.is_empty());
        let first = cache.tau_of(&s0).expect("A_3 translates").clone();
        assert_eq!((cache.len(), cache.hits(), cache.misses()), (1, 0, 1));
        let again = cache.tau_of(&s0).expect("A_3 translates").clone();
        assert_eq!((cache.len(), cache.hits(), cache.misses()), (1, 1, 1));
        // tau S_0 = S_1 over A_3, so the hit returns the same module value the
        // miss stored, not a fresh copy.
        assert!(first.ptr_eq(&again));
        assert_eq!(first.dim_vector(), &[0, 1, 0]);
        cache.tau_of(&s1).expect("A_3 translates");
        assert_eq!((cache.len(), cache.hits(), cache.misses()), (2, 1, 2));
        for _ in 0..3 {
            cache.tau_of(&s1.clone()).expect("A_3 translates");
        }
        assert_eq!((cache.len(), cache.hits(), cache.misses()), (2, 4, 2));
        // A rebuilt S_0 is another module value, so it takes its own entry.
        // The miss is the price of keying by identity.
        cache
            .tau_of(&Module::simple(&algebra, 0))
            .expect("A_3 translates");
        assert_eq!((cache.len(), cache.hits(), cache.misses()), (3, 4, 3));
    }

    // tau of a projective is zero, so the regular module A = sum of all P_v is
    // tau-rigid over every algebra and needs no Hom system at all.
    #[test]
    fn every_projective_is_tau_rigid() {
        for field in fields() {
            for algebra in [
                linear_an(2, field),
                linear_an(3, field),
                tp3(field),
                commutative_square(field),
                d4(field),
            ] {
                let projectives: Vec<(usize, Module)> = (0..algebra.quiver().num_vertices())
                    .map(|v| (v as usize, Module::projective(&algebra, v)))
                    .collect();
                let mut cache = TauCache::new();
                for single in &projectives {
                    let rigid = expect_rigid(
                        is_tau_rigid_summandwise(std::slice::from_ref(single), &mut cache)
                            .expect("the fixture translates"),
                    );
                    assert!(rigid.translates()[0].is_zero());
                    assert!(rigid.vanishing_pairs().is_empty());
                    assert!(rigid.verify());
                }
                let rigid = expect_rigid(
                    is_tau_rigid_summandwise(&projectives, &mut cache)
                        .expect("the fixture translates"),
                );
                assert!(rigid.vanishing_pairs().is_empty());
                assert_eq!(rigid.summands().len(), projectives.len());
                assert!(rigid.verify());
            }
        }
    }

    #[test]
    fn the_zero_module_is_tau_rigid() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let rigid = expect_rigid(
                is_tau_rigid_summandwise(&[], &mut TauCache::new()).expect("no summand, no work"),
            );
            assert!(rigid.is_zero_module());
            assert!(rigid.vanishing_pairs().is_empty());
            assert!(rigid.translates().is_empty());
            assert!(rigid.verify());
            let through_decompose = expect_rigid(
                is_tau_rigid(&Module::zero(&algebra)).expect("the zero module needs no translate"),
            );
            assert!(through_decompose.is_zero_module());
            assert!(through_decompose.verify());
        }
    }

    // Hand table over linearly oriented A_2 (arrow 0 -> 1). P_1 = S_1 = (0, 1)
    // and P_0 = (1, 1) are projective, so their translates are zero. The only
    // non-projective is S_0 = (1, 0), with tau S_0 = S_1 from the AR sequence
    // 0 -> P_1 -> P_0 -> S_0 -> 0. So the one pair that can fail is
    // Hom(X, tau S_0) = Hom(X, S_1), whose dimension is dim (top X)_1: that is
    // 0 for S_0 and for P_0, and 1 for S_1. A subset is therefore tau-rigid
    // exactly when it does not hold both S_0 and S_1, which leaves 6 of the 8
    // subsets, and every failure is witnessed at the pair (S_1, S_0).
    #[test]
    fn the_a2_subsets_match_the_hand_table() {
        for field in fields() {
            let algebra = linear_an(2, field);
            let modules = [
                Module::simple(&algebra, 0),
                Module::simple(&algebra, 1),
                Module::projective(&algebra, 0),
            ];
            let mut cache = TauCache::new();
            assert_eq!(
                cache
                    .tau_of(&modules[0])
                    .expect("A_2 translates")
                    .dim_vector()
                    .to_vec(),
                vec![0, 1]
            );
            let mut rigid_count = 0;
            for subset in subsets_up_to_three(3) {
                let summands = indexed(&modules, &subset);
                let both = subset.contains(&0) && subset.contains(&1);
                let outcome =
                    is_tau_rigid_summandwise(&summands, &mut cache).expect("A_2 translates");
                assert_eq!(
                    outcome.is_tau_rigid(),
                    !both,
                    "subset {subset:?} over F_{}",
                    field.modulus()
                );
                match outcome {
                    TauRigidityOutcome::TauRigid(r) => {
                        rigid_count += 1;
                        assert!(r.verify());
                    }
                    TauRigidityOutcome::NotTauRigid(w) => {
                        assert_eq!((w.source_index(), w.target_index()), (1, 0));
                        assert!(w.verify());
                    }
                }
            }
            assert_eq!(rigid_count, 6);
        }
    }

    // Hand table over linearly oriented A_3 (arrows 0 -> 1 -> 2). The
    // non-projectives are S_0 with tau S_0 = S_1, S_1 with tau S_1 = S_2, and
    // (1, 1, 0) with tau = P_1 = (0, 1, 1). Hom(X, S_1) has dimension
    // dim (top X)_1, so it is nonzero exactly for X = S_1 and X = P_1. So
    // {S_0, S_1} is not tau-rigid: Hom(S_1, tau S_0) = End(S_1) has dimension
    // 1. Scanning pairs in (i, j) order over the summand list [S_0, S_1] gives
    // (0, 0) with Hom(S_0, S_1) = 0, then (0, 1) with Hom(S_0, S_2) = 0, then
    // (1, 0), the first nonzero pair.
    #[test]
    fn the_a3_pair_of_simples_fails_at_the_first_nonzero_pair_in_order() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let s0 = Module::simple(&algebra, 0);
            let s1 = Module::simple(&algebra, 1);
            let summands = vec![(0, s0.clone()), (1, s1.clone())];
            let witness = expect_not_rigid(
                is_tau_rigid_summandwise(&summands, &mut TauCache::new()).expect("A_3 translates"),
            );
            assert_eq!(witness.source_index(), 1);
            assert_eq!(witness.target_index(), 0);
            assert!(witness.source().ptr_eq(&s1));
            assert!(witness.target_summand().ptr_eq(&s0));
            assert_eq!(witness.translate().dim_vector(), &[0, 1, 0]);
            assert!(!witness.morphism().is_zero());
            assert!(witness.verify());
            // The reversed summand order moves the first nonzero pair to
            // (0, 1) and keeps the same indices on the witness.
            let reversed = vec![(1, s1), (0, s0)];
            let other = expect_not_rigid(
                is_tau_rigid_summandwise(&reversed, &mut TauCache::new()).expect("A_3 translates"),
            );
            assert_eq!((other.source_index(), other.target_index()), (1, 0));
            assert!(other.verify());
        }
    }

    // Over A = k[x]/(x^3) the indecomposables are the uniserials
    // U_m = k[x]/(x^m) for m = 1, 2, 3, and U_3 = A is projective. The algebra
    // is symmetric, so the Nakayama functor is the identity and tau = Omega^2.
    // The cover A -> U_m has kernel x^m A = U_(3-m), so Omega U_m = U_(3-m)
    // and tau U_m = U_m for m = 1, 2. Hom_A(A/(x^m), U_m) is the set of
    // elements of U_m killed by x^m, which is all of U_m, so
    // dim Hom(U_m, tau U_m) = m. Both U_1 and U_2 are therefore not tau-rigid,
    // and A is the only tau-rigid indecomposable. That matches the two support
    // tau-tilting pairs recorded for truncated_poly(3).
    #[test]
    fn the_truncated_poly_uniserials_are_not_tau_rigid() {
        for field in fields() {
            let algebra = tp3(field);
            for m in [1usize, 2] {
                let u = uniserial(&algebra, m);
                let mut cache = TauCache::new();
                let translate = cache.tau_of(&u).expect("k[x]/(x^3) translates").clone();
                assert!(!translate.is_zero(), "U_{m} is not projective");
                assert_eq!(translate.dim_vector(), &[m]);
                assert_eq!(hom_dim(&u, &translate).expect("one algebra"), m);
                let witness = expect_not_rigid(
                    is_tau_rigid_summandwise(&[(0, u.clone())], &mut cache)
                        .expect("k[x]/(x^3) translates"),
                );
                assert_eq!((witness.source_index(), witness.target_index()), (0, 0));
                assert!(!witness.morphism().is_zero());
                assert!(witness.verify());
                assert!(!is_tau_rigid(&u).expect("k[x]/(x^3)").is_tau_rigid());
            }
            let regular = uniserial(&algebra, 3);
            let rigid = expect_rigid(is_tau_rigid(&regular).expect("A is projective"));
            assert!(rigid.translates()[0].is_zero());
            assert!(rigid.verify());
        }
    }

    // On the D_4 path algebra with no relations the catalog has 12
    // indecomposables. The summandwise sum of dim Hom(X_i, tau X_j) is
    // compared against dim Hom(M, tau M) with M assembled and tau called on
    // it, for all 1 + 12 + 66 + 220 = 299 subsets of size at most three.
    #[test]
    fn summandwise_agrees_with_the_assembled_route_on_every_small_d4_subset() {
        for field in fields() {
            let algebra = d4(field);
            let catalog = IndecomposableCatalog::dynkin(&algebra).expect("D_4 is Dynkin");
            let modules: Vec<Module> = catalog
                .entries()
                .iter()
                .map(|e| e.module().clone())
                .collect();
            assert_eq!(modules.len(), 12, "D_4 has 12 indecomposables");
            let subsets = subsets_up_to_three(modules.len());
            assert_eq!(subsets.len(), 299);
            let mut cache = TauCache::new();
            for subset in &subsets {
                let summands = indexed(&modules, subset);
                let refs: Vec<&Module> = subset.iter().map(|&i| &modules[i]).collect();
                let split = summandwise_dim(&summands, &mut cache);
                assert_eq!(
                    split,
                    assembled_dim(&refs),
                    "subset {subset:?} over F_{}",
                    field.modulus()
                );
                let outcome = is_tau_rigid_summandwise(&summands, &mut cache)
                    .expect("the D_4 catalog translates");
                assert_eq!(outcome.is_tau_rigid(), split == 0, "subset {subset:?}");
                match outcome {
                    TauRigidityOutcome::TauRigid(rigid) => assert!(rigid.verify()),
                    TauRigidityOutcome::NotTauRigid(witness) => assert!(witness.verify()),
                }
            }
            // One translate per catalog entry, and every later lookup is a hit.
            assert_eq!(cache.len(), modules.len());
            assert_eq!(cache.misses(), modules.len() as u64);
        }
    }

    #[test]
    fn summandwise_agrees_with_the_assembled_route_on_the_small_fixtures() {
        for field in fields() {
            for (name, modules) in fixtures(field) {
                let mut cache = TauCache::new();
                for subset in subsets_up_to_three(modules.len()) {
                    let summands = indexed(&modules, &subset);
                    let refs: Vec<&Module> = subset.iter().map(|&i| &modules[i]).collect();
                    let split = summandwise_dim(&summands, &mut cache);
                    assert_eq!(split, assembled_dim(&refs), "{name}: subset {subset:?}");
                    let outcome = is_tau_rigid_summandwise(&summands, &mut cache)
                        .expect("the fixture translates");
                    assert_eq!(
                        outcome.is_tau_rigid(),
                        split == 0,
                        "{name}: subset {subset:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn the_convenience_entry_point_agrees_with_the_summandwise_one() {
        for field in fields() {
            for (name, modules) in fixtures(field) {
                let mut cache = TauCache::new();
                for subset in subsets_up_to_three(modules.len()) {
                    if subset.is_empty() {
                        continue;
                    }
                    let refs: Vec<&Module> = subset.iter().map(|&i| &modules[i]).collect();
                    let (assembled, _, _) = direct_sum(&refs);
                    let summands = indexed(&modules, &subset);
                    let split = is_tau_rigid_summandwise(&summands, &mut cache)
                        .expect("the fixture translates");
                    let whole = is_tau_rigid(&assembled).expect("the fixture translates");
                    assert_eq!(
                        split.is_tau_rigid(),
                        whole.is_tau_rigid(),
                        "{name}: subset {subset:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn a_tampered_non_tau_rigid_witness_fails_verification() {
        for field in fields() {
            let algebra = tp3(field);
            let u2 = uniserial(&algebra, 2);
            let witness = expect_not_rigid(
                is_tau_rigid_summandwise(&[(0, u2.clone())], &mut TauCache::new())
                    .expect("k[x]/(x^3) translates"),
            );
            assert!(witness.verify());
            let mut zeroed = witness.clone();
            zeroed.morphism =
                zero_morphism(witness.source(), witness.translate()).expect("one algebra");
            assert!(!zeroed.verify(), "a zero morphism proves nothing");
            // tau U_1 = U_1 has dimension 1 and the stored translate has
            // dimension 2, so the recomputed translate is not isomorphic to it.
            let mut wrong_summand = witness.clone();
            wrong_summand.target_summand = uniserial(&algebra, 1);
            assert!(!wrong_summand.verify());
            // A translate the morphism does not run into fails the endpoint
            // check before any recomputation.
            let mut wrong_translate = witness.clone();
            wrong_translate.translate = uniserial(&algebra, 2);
            assert!(!wrong_translate.verify());
        }
    }

    #[test]
    fn a_tampered_tau_rigid_module_fails_verification() {
        for field in fields() {
            let algebra = linear_an(3, field);
            let s0 = Module::simple(&algebra, 0);
            let s1 = Module::simple(&algebra, 1);
            let rigid = expect_rigid(
                is_tau_rigid_summandwise(&[(0, s0.clone())], &mut TauCache::new())
                    .expect("A_3 translates"),
            );
            assert!(rigid.verify());
            assert_eq!(rigid.vanishing_pairs(), vec![(0, 0)]);

            let mut truncated = rigid.clone();
            truncated.translates.clear();
            assert!(!truncated.verify(), "one translate per summand or nothing");

            let mut claimed_projective = rigid.clone();
            claimed_projective.translates[0] = Module::zero(&algebra);
            assert!(!claimed_projective.verify(), "S_0 is not projective");

            // tau S_0 = S_1 over A_3, so a stored S_0 is the wrong translate
            // and no stored witness can cover for it.
            let mut swapped_target = rigid.clone();
            swapped_target.translates[0] = s0.clone();
            assert!(
                !swapped_target.verify(),
                "S_0 is not the translate of S_0 over A_3"
            );

            // A pair that does not vanish presented as tau-rigid: Hom(S_1, tau
            // S_0) = End(S_1) has dimension 1, so the added summand breaks the
            // claim and no stored value can hide it.
            let mut forged = rigid.clone();
            forged.summands.push((1, s1));
            forged.translates.push(
                is_tau_rigid_summandwise(&[(1, Module::simple(&algebra, 1))], &mut TauCache::new())
                    .map(|outcome| match outcome {
                        TauRigidityOutcome::TauRigid(r) => r.translates()[0].clone(),
                        TauRigidityOutcome::NotTauRigid(_) => panic!("S_1 is tau-rigid alone"),
                    })
                    .expect("A_3 translates"),
            );
            assert!(!forged.verify());
        }
    }

    /// The two `(1, 1)` Kronecker modules `k --1--> k, k --0--> k` and its
    /// mirror. Both are regular with `tau X` isomorphic to `X`, they are not
    /// isomorphic to each other, and `Hom` between them is zero.
    fn kronecker_pair(field: PrimeField) -> (Module, Module) {
        let algebra = crate::algebra::kronecker(2, field);
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

    // The cache must answer from the module it was handed, not from a caller
    // label. X and Y here share the dimension vector (1, 1) and are not
    // isomorphic, tau X is X and tau Y is Y, and Hom(Y, X) is zero. A cache
    // keyed by a caller index answered the second question with tau X and
    // called Y tau-rigid, which it is not: dim Hom(Y, tau Y) is 1.
    #[test]
    fn a_shared_cache_separates_two_modules_with_one_dimension_vector() {
        for field in fields() {
            let (x, y) = kronecker_pair(field);
            let mut cache = TauCache::new();
            let tau_x = cache.tau_of(&x).expect("kronecker translates").clone();
            let tau_y = cache.tau_of(&y).expect("kronecker translates").clone();
            assert_eq!(hom_dim(&x, &tau_x).expect("one algebra"), 1);
            assert_eq!(hom_dim(&y, &tau_y).expect("one algebra"), 1);
            let outcome = is_tau_rigid_summandwise(&[(0, y.clone())], &mut cache)
                .expect("kronecker translates");
            assert!(
                !outcome.is_tau_rigid(),
                "Hom(Y, tau Y) has dimension 1, so Y is not tau-rigid"
            );
        }
    }
}
