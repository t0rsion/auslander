# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.5.0] - 2026-08-18

Support tau-tilting theory, with a closure certificate. The release adds
tau-rigidity, support tau-tilting pairs, left mutation, and the budgeted
mutation walk, in the crate and in Python. A drained walk hands back a
complete list of basic support tau-tilting pairs only after a separate
verifier accepts its closure witness.

Four correctness fixes lead the Fixed section. The tau cache could return
another module's translate, and call a module tau-rigid when it is not. A
closed graph was built without running its own verifier. A walk could charge
past `max_work_units` and still report closure. And the completeness citation
named the wrong theorem; it now names the one the obligations establish.

This release is not additive. `MonomialPresentation` and the monomial
constructors leave `algebra` for the new `monomial` module.
`Algebra::from_monomial`, the `Tau` enum, three witness types, the tilting
module, and the right approximation are gone. In Python, `Module.tau()`
returns the zero module where it returned `None`, and
`TauRigidModule.translates` no longer holds `None`. The crate is alpha and
breaks between versions by design, so there is no migration mapping here. The
Removed and Changed entries name what moved and what went.

### Added

- The live QPA oracle separates two claims that were conflated. That a real
  GAP+QPA run agrees with the library is asserted on any GAP, unconditionally,
  and is the reason the oracle exists. That the committed `qpa_expected.json`
  reproduces byte for byte holds only within one GAP version, so it is checked
  only when the fresh run's recorded `gap_version` matches the committed one.
  GAP 4.16dev and the Ubuntu distro package produce documents that differ while
  both agree with the library, so the old unconditional comparison failed on a
  true result. The workflow runs on manual dispatch and a monthly schedule, so
  it had not run against this crate since v0.1.0 and the conflation went
  unnoticed through two releases.
- `tests/determinism_graph.rs` gates the support tau-tilting graph across fresh
  processes and against committed goldens under `tests/golden-graph/`, which
  design section 14 promised and no test delivered. Two spawned children must
  agree with each other and with the parent on a fingerprint over the
  normalized renderings of D_4 over both fields, A_3, and a radical-square-zero
  cycle.
- The rendering covers every value the closed graph's witnesses store, not a
  projection of them. Vertex lines carry digests over the certified
  decomposition and the tau-rigid data with its AR translates. Edge lines carry
  digests over the endpoint isomorphisms, the mutation's own target pair, the
  almost complete pair, both add-closure witnesses, and the approximation's
  factorization coordinates, kernel basis, and radical coordinates. Each digest
  tags its domain and carries its lengths, so a change in one store cannot
  cancel a change in another: an earlier rendering recorded only the summand
  bijection, and rescaling a stored isomorphism by 2 with its inverse by 3 over
  F_5 left the golden byte for byte identical. The limit is stated in the test:
  the `EndoAlgebra` values with no public accessor are reached only through the
  basis and radical basis they are computed from.
- `BasicDecomposition` and `ProjectiveSupport`: the two parts of a pair
  `(M, P)`, each basic and each certified at construction.
  `BasicDecomposition::new` runs `krull_schmidt` and certifies every summand
  through `IndecomposableModule`. A repeated summand is `BasicError::NotBasic`
  and an undetermined split is `BasicError::CertificationBlocked`, never a
  silent distinct value. `pair_iso` decides identity of two pairs as a
  `SupportPairIsoOutcome`, either a verified `SupportPairIsoWitness` or a
  `SupportPairObstruction`, with no undecided variant: the radical criterion
  between certified indecomposables is total. `PairFingerprint` and
  `SummandFingerprint` are the invariants a caller screens on, and `AddMatch`
  and `AddClosureWitness` certify that a module lies in `add(T)` (`basic`).
- `is_tau_rigid` and `is_tau_rigid_summandwise` decide `Hom(M, tau M) = 0`.
  Both `tau` and `Hom` are additive, so the decision runs over ordered pairs of
  summands through `hom_dim(X_i, tau X_j)`, and `tau` runs once per summand
  through a `TauCache`. A vanishing claim has no element to exhibit, so
  `TauRigidModule` stores no positive witness: its private construction is the
  proof token, and `TauRigidModule::verify` recomputes every translate and
  every dimension. The negative answer does have an element, and
  `NonTauRigidWitness` carries one nonzero `X_i -> tau X_j` (`taurigid`).
- `SupportTauTiltingPair` and `AlmostCompletePair` classify a candidate
  `(M, P)` against the four conditions, with `|M| + |P| = n` for the first and
  `n - 1` for the second. A failed condition is a `PairRejection` value with
  its condition number, never an error. `enumerate_over_catalog` lists every
  pair of one algebra from the definition alone over an exhaustive
  `IndecomposableCatalog`: no mutation, no approximation, no theorem about the
  support tau-tilting quiver. Its completeness is the catalog's classification
  theorem, so it runs over catalog domains only (`supporttau`).
- `mutate_at` performs left mutation at a module-summand slot. Exactly one of
  two branches holds, and the function decides which by computation: a
  `Mutation` with its `MutationWitness`, or a `FacWitness` proving that `X_j`
  lies in `Fac(M/X_j)`, where the slot admits no left mutation. `ExchangeShape`
  names the two shapes, a summand moving into the projective part and a summand
  replaced by a module. Mutation at a summand of the projective part is always
  a right mutation, so a slot is an index into the module summands and nothing
  else (`mutation`).
- `support_tau_tilting_graph` walks the support tau-tilting quiver breadth
  first from `(A, 0)`, closing under left mutation alone, under the four
  budgets of `MutationGraphLimits`. The outcome is a
  `ClosedSupportTauTiltingGraph`, whose vertex list is every basic support
  tau-tilting pair of the algebra up to isomorphism, or an
  `IncompleteSupportTauTiltingGraph`, which keeps the certified part and makes
  no completeness claim. An exhausted budget and a blocked certification are
  both values on the incomplete type, under `reason` and `diagnostics`.
  Truncation is structurally biased: over `kronecker(2)` the walk descends the
  preprojective ray and reaches no preinjective vertex, so a truncated set is a
  sample and not a nearly complete list (`taugraph`).
- `crates/auslander/tests/residue_degree.rs` proves that over `kQ/I` with `k` a
  finite prime field, every tau-rigid indecomposable has residue degree 1. The
  proof base changes along `L/k` for `L = End(N)/rad End(N)`, which is Galois.
  It uses that base change commutes with `tau`, and contradicts the distinct
  g-vectors that the summands of a support tau-tilting pair carry. The proof
  needs `k` perfect and `A` split basic; both hold here, because `PrimeField`
  is a finite prime field and `I` is admissible, so `A / rad A` is `k^n`. Every
  approximation generator of the tau-tilting layer is a tau-rigid
  indecomposable, so the `D_i` case is unreachable on that path and its half of
  the certificate stays unexercised. The test runs the approximation
  multiplicity count from the public API over a non-hereditary algebra at
  `d = 2`. It pins the unreachability with two walks, one of them over an
  algebra whose module category does hold a `d = 2` brick.
- QPA oracle schema v7: schema v6 unchanged plus one `support_tau_tilting`
  block per fixture, 23 blocks, produced by a real GAP+QPA run. Every field is
  compared against a library route independent of QPA, or skipped with a typed
  reason. Totals, histograms, and pair lists come from
  `supporttau::enumerate_over_catalog` where a catalog exists and from
  `taugraph::support_tau_tilting_graph` where it does not, which must then
  return a closed graph; `tau_rigid_designated` from `taurigid::is_tau_rigid`;
  and sampled approximation slots from `approx::left_approximation`.
  `brute_agreement` is read and validated but never compared, because it is
  GAP's own cross-check against `AllIndecModulesOfLengthAtMost` and has no
  library counterpart. The `one_tilting` field is unread for the same reason
  the Removed section gives: the type that produced our side is cut. The
  reader accepts the key and compares nothing, and schema v8 drops the field
  from the generator and the document together. The harness implements two
  schema strings, v7 for the oracle and v6 for `native_snapshot.json`, and
  rejects every other, so a stale file fails loudly. Twenty of the 23 fixtures
  close; `kronecker-2`, `self-overlap`, and `inclusion-ambiguity` never do,
  and carry no total, no histogram, and no pair list. The always-on modes
  run 90 tests where the v6 layer ran 74. The live run takes 322 s, all but
  3 s of it inside GAP.
- The live QPA run requires the generator sentinel. `gap -q -T` with closed
  stdin exits 0 after an uncaught error, measured for a division by zero, an
  unbound variable, and a QPA "no method found", so an exit code says nothing.
  `qpa_oracle.rs` checks the two signals that do carry: the generator writes
  its output file in one final statement, so a run that dies leaves no file,
  and the last line of stdout is `qpa-oracle-generator-ok`, printed after the
  write. The generator also writes `qpa_generated.json`, never
  `qpa_expected.json`, so promoting a run is a deliberate copy.
- The `profiling` feature and `benches/perf.rs`. `profile::hit` adds one to a
  counter every time control enters a named call site. The counts are exact and
  machine-independent, so two commits compare where wall clock does not; they
  say how often a primitive ran, not how long it took. The feature is off by
  default and no released build carries the counters. The harness runs with
  `cargo bench -p auslander --bench perf`, calibrates each case to about 20 ms,
  and reports the best trial rather than the mean. `--counts` prints call
  counts instead of times, `--group` and `--case` filter, and the output is tab
  separated so a run pastes into a table without a number being retyped.
- `ExtSpace::matches_recomputation` rebuilds the space from its live endpoint
  modules and compares every stored value: the resolution prefix term by term
  and differential by differential, the cochain term, the cocycle, coboundary
  and complement bases, and the representatives. `ExtSpace::matches` is the
  same comparison against a space the caller already built. A recomputation
  owns fresh `Module` values, so terms, differentials, and representatives
  compare entry by entry, not by pointer.
- `ExtClass::then_in` and `ExtClass::then_with_witness_in` multiply into a
  space the caller supplies, where `then` builds one per product.
  `ExtClass::product_space` builds that space. Compatible recomputed spaces
  carry identical bases, so the coordinates are the ones `then` returns; an
  incompatible space is `ExtClassError::IncompatibleSpaces`. Two hundred
  products of `Ext^1(S, S)` with itself over `k[x]/(x^3)` take 1.25 ms
  through `then_in` and 5.18 ms through `then`.
- `ProductWitness::verify_against` takes the product space's recomputation
  from the caller, so verifying many products in one space rebuilds it once.
- `AlmostSplitSequence::verify` and `AlmostSplitSequence::verify_with_catalog`
  recheck the witness with the sequence and class the value holds. The
  free-standing `ArDualityWitness::verify` and `CatalogWitness::verify` stay,
  because the mutation corpus passes mismatched pairs on purpose. Each of the
  two new methods returns false for the other route's witness.
- `Relation::field` reports the prime field the relation was built over.
  `Relation` now stores that field, and `Presentation::new` rejects a
  relation from another one with the new `RelationError::FieldMismatch
  { expected, found }`. Coefficients are canonical representatives, so a
  relation built over F_5 with `-1` stored as the raw 4 used to be accepted
  by a presentation over F_7, where the same raw value means `+4`.
- `CompletionLimits::max_origin_terms` bounds the provenance terms of one
  origin, and `CompletionLimits::max_ambiguities` bounds the ambiguity keys
  held at once and the entries of the certificate's `ambiguities` list. Two
  paths grew without a budget. One reduction step adds up to the whole origin
  of the basis element it uses, so provenance compounds across the basis
  while `max_steps` charges one unit per step. The ambiguity queue is built
  over all pairs of leading words, and over a monomial ideal every
  composition is exactly zero, so the drain charges no steps however large
  the queue is. Exhausting either gives `TruncationReason::OriginBudget` or
  `TruncationReason::AmbiguityBudget`. Defaults: 4096 origin terms, 65536
  ambiguity keys. No input that completed before truncates now, and the
  golden certificates are byte for byte unchanged.
- Python: `Module.tau_rigidity` decides `Hom(M, tau M) = 0` as a `TauRigidity`,
  witnessed either way. The positive branch carries `vanishing`, a
  `TauRigidModule` with `summands`, `translates`, and `vanishing_pairs`; the
  negative branch carries `morphism`, one nonzero `X_i -> tau X_j`, and
  `summand_pair`. Neither branch raises. `verify()` recomputes every translate
  through the certified double route.
- Python: `SupportTauTiltingPair.classify(algebra, modules, vertices,
  field=None)` classifies a candidate `(M, P)` against the four conditions, and
  `AlmostCompletePair.classify` against `|M| + |P| = n - 1`. A failed condition
  is a `PairRejection` value with `condition()` (1 to 4), `kind`, `witness`,
  `hom_from_projective`, and `summand_counts`, never an exception. An accepted
  pair exposes
  `module_summands`, `projective_support`, `is_tau_tilting`, `summand_count`,
  and `verify()`.
- Python: `SupportTauTiltingPair.mutate_at(slot)` returns a `Mutation` or a
  `FacWitness`. The `Mutation` carries `slot`, `target`, `shape`
  (`"moves_to_projective"` with `exchanged_vertex`, `"replaced_by_module"` with
  `multiplicity`), and `verify()`. The `FacWitness` proves that `X_j` lies in
  `Fac(M/X_j)`, so the slot admits no left mutation; it carries `module`,
  `summand`, `maps`, `image_dims`, and `verify()`.
- Python: `Algebra.support_tau_tilting_graph(field=None, limits=None)` returns
  one of two classes. `ClosedSupportTauTiltingGraph` has `pairs()`,
  `mutations()`, `histogram()`, `work_units()`, `verify()`, and `len()`; its
  vertex list is every basic support tau-tilting pair of the algebra, certified
  by the closure witness. `IncompleteSupportTauTiltingGraph` has
  `vertices_found`, `verified_mutations`, `reason`, `diagnostics`,
  `work_units()`, and `verify_parts()`, and no `pairs()` accessor at all, so a
  truncated walk cannot be read as a complete list. An exhausted budget and a
  blocked certification are both values on that class, under `reason` and
  `diagnostics` (a `GraphBudgetDiagnostics` or a `CertificationBlocker`).
  `MutationGraphLimits(*, max_vertices=None, max_directed_mutations=None,
  max_work_units=None, max_matrix_entries=None)` sets the budgets.
- Python: `Algebra.enumerate_over_catalog(field=None)` lists every support
  tau-tilting pair from the definition over an exhaustive catalog, as a
  `CatalogEnumeration` with `pairs()`, `provenance`, `catalog_len`,
  `nodes_visited`, `histogram()`, `verify()`, and `len()`. Completeness is the
  catalog's classification theorem and nothing else, so the route runs on
  catalog domains only and any other algebra raises `UnsupportedDomainError`.
  It is independent of the mutation-graph certificate: no mutation, no
  approximation, no theorem about the support tau-tilting quiver. Both routes
  agree on the counts 4, 8, 16 for semisimple algebras on 2, 3, 4 vertices, 5
  for `linear_an(2)`, 14 for `linear_an(3)`, 2 for `truncated_poly(3)`, and 50
  for D_4 with histogram `[1, 4, 9, 16, 20]`.
- Python: `CertificationBlockedError`, a `RuntimeError` subclass, reports a step
  the crate could not certify: an undetermined split, an undetermined
  indecomposability gate, or an undecided isomorphism test inside the tau
  cross-check. It is not budget exhaustion, so it does not subclass
  `BudgetExhaustedError` and raising a limit does not help.
- Python: `from_relations` and `from_certificate` take the keywords
  `max_origin_terms` and `max_ambiguities`, so every budget whose exhaustion
  `TruncationError.reason` can name is now raisable from Python.
- Python: `Morphism` exposes its endpoints and its composition. `source`,
  `target`, and `is_zero` are getters, `then(other)` is the composite "first
  self, then other" and raises `ValueError` on mismatched endpoints, and
  `map_at(v)` reads one vertex matrix where `maps` rebuilds all of them.
- Python: `len(ar_quiver)` is the vertex count and `len(decomposition)` the
  summand count.
- Python: `ResolutionStatus`, `Bounded`, `DynkinType`, `EuclideanType`,
  `ResolutionKind`, `DiagramFamily`, and `AlmostSplitOutcome` hash by value,
  so each works as a dict key or set element. All of them compared by value
  already. PyO3 leaves `__hash__` unset for a class declared with `eq` alone,
  and CPython turns that into `__hash__ = None`, so a dict or set operation on
  any of them raised `TypeError: unhashable type`.
- `EndoAlgebra::quotient_dim` reports `dim_k End(M)/rad End(M)`. That is the
  residue degree only when the algebra is local, so the name says quotient;
  `IndecomposableModule::residue_degree` delegates to it and keeps the
  stronger name, because that type's invariant is locality.
- `Decomposition::endos` gives `End(S_k)` for every summand, and `IsoClass`
  carries the `endo` of its representative. Both come from the split that
  produced the summand. `IndecomposableModule::from_endo` runs the
  indecomposability gate on such an algebra, with the same outcomes as
  `IndecomposableModule::new` and one radical computation fewer.
- `EndoAlgebra` implements `Clone` and `Debug`. The `Debug` output is the
  dimension vector, `dim`, and `radical_dim`, not the basis.
- `DenseMat::solve_many` solves `A X = B` for every column of `B` in one
  elimination, and `DenseMat::inverse` is that solve against the identity.
  Column `j` of the result equals `DenseMat::solve` on column `j` of `B`,
  entry for entry, and the result is `None` when any column lies outside the
  image. Inverting a 120 x 120 matrix over F_p with p = 2^31 - 1 takes 4.5 ms
  where 120 calls to `solve` take 166 ms: one elimination against `n`.
- `RowReducer` accumulates rank one row at a time. `push` reduces a row
  against the rows kept so far and returns whether the rank went up, which is
  the test behind the deterministic complement rule. Selecting an independent
  subset of 120 rows of length 120 takes 1.0 ms where one `DenseMat::rank`
  call per prefix takes 48 ms.
- `SparseRow::add_scaled_into` merges through a caller-owned buffer and swaps,
  so an elimination loop allocates once instead of once per row operation.
  `SparseRow::add_scaled` stays as the allocating wrapper.
- `DenseMat::left_kernel_basis` and `SparseMat::left_kernel_basis` name the
  basis of {x : x A = 0}, spelled out as `transpose().kernel_basis(f)` at
  eight call sites.
- `Algebra::radical_power_matrix` returns the row-reduced component matrix of
  `e_u · J^k · e_v` by reference. Construction runs the row-space iteration and
  keeps the chain, so the call costs one index. It replaces
  `Algebra::radical_power_component`, which returned the same rows in the same
  order as an owned `Vec<Vec<Fp>>`; see Removed.

### Changed

- `HomSpace` keeps the flat rows as its primary form. `hom_rows` returns the
  kernel of the commuting-square system as a `DenseMat`, one row per basis
  element, and that row layout is already the flattening `HomSpace` stores:
  the per-vertex matrices row-major, concatenated in vertex order. The old
  path unflattened each kernel row into a `Morphism` and `HomSpace` reflattened
  it, a copy in each direction and nothing else. `HomSpace::dim` and every
  coordinate operation now read the rows and build no `Morphism`.
  `HomSpace::basis_morphism` unflattens one row, `HomSpace::basis_iter`
  unflattens the rows a caller consumes, and `HomSpace::basis` unflattens all
  of them once and keeps them. `hom` keeps its signature and its row order, and
  is now `HomSpace::new(m, n)?.into_basis()`.
- `enumerate_over_catalog` builds each candidate through
  `BasicDecomposition::from_catalog`. Both catalog enumerators emit one
  certified entry per isomorphism class, so a subset of a catalog is already a
  basic decomposition. `krull_schmidt` has nothing to decide there, and the
  certified isomorphism test that matched reassembled summands back to catalog
  positions has nothing to find. The walk names its summands directly. They are
  the catalog's own module values, so a `TauCache` keyed by module identity
  holds one translate per catalog entry across every subset. Release profile,
  best of three interleaved runs of `benches/perf.rs`:
  `enumerate_over_catalog d4-f5` 6483045.0 ns to 293785.1 ns.
- Building a `ClosedSupportTauTiltingGraph` runs `ClosureWitness::verify`
  first, and there is no flag to skip it, so a closing walk pays for the
  recheck. On D_4 the recheck costs 74.4 ms to 124.2 ms against 18.7 ms to
  30.9 ms for the walk, over four dev-profile runs per field, so a closing D_4
  run costs about five times what it did. The recheck is not charged to
  `max_work_units`, which budgets the search rather than the result. The cost
  is deliberate: a closed graph is a completeness claim, and the claim now
  rests on a check the walk itself did not make. The Fixed entry gives the
  reason.
- Every reduction on `DenseMat` and `SparseMat` has a consuming form.
  `into_rref`, `into_rank`, `into_kernel_basis`, and `into_row_space_basis`
  take the matrix by value and reduce it in place, where `rref`, `rank`,
  `kernel_basis`, and `row_space_basis` clone it first. Both forms return the
  same thing, and the consuming form is crate-private. What it saves is the
  copy alone: roughly 0.2 to 0.4 percent of retired instructions across the
  pipeline groups of `benches/perf.rs`, and nothing observable on the wall
  clock of this box. Do not plan a wall-clock gain around it.
- BREAKING: `TauCache::tau_of` takes the module alone and returns
  `Result<&Module, TauError>`. The caller-supplied index is gone, and so is
  the `Tau` enum it returned. A caller that owned indices drops them. See Fixed
  for why the index had to go.
- BREAKING: `TauRigidModule::translates` returns `&[Module]` where it returned
  `&[Tau]`, and `TauRigidModule::witnesses` is replaced by
  `TauRigidModule::vanishing_pairs`, which returns the ordered summand
  positions `(i, j)` as `Vec<(usize, usize)>`. The witness values it used to
  return carried no data beyond those positions.
- BREAKING: `SupportTauTiltingPair::projective` and
  `AlmostCompletePair::projective` return a `ProjectiveSupport` by value,
  derived from the module part on each call, where they returned a reference to
  a stored field. The four conditions force the projective part, so storing it
  stored nothing. `AlmostCompletePair::omitted_vertex` reports the vertex such
  a pair leaves out of the support complement, which is the one bit the module
  part does not fix.
- BREAKING: `PairRejection::HomFromProjectiveNonzero` carries `vertex` and
  `dim` instead of a witness morphism. For right modules `Hom(P_v, M) = M_v`,
  so the vertex and the dimension are the whole proof and no morphism is built.
  In Python, `PairRejection.witness` is now `None` for condition 2 and the new
  `hom_from_projective` getter carries the two counts.
- BREAKING, Python: `Module.tau()` returns the zero module where it returned
  `None`. A projective module has a zero translate, and the zero module keeps
  its algebra and its dimension vector, which is more than the old `None`
  carried. `TauRigidModule.translates` changes the same way: it is a list of
  modules with no `None` in it, and a projective summand contributes the zero
  module.
- `radical::joint_kernel_bases` reads its spanning rows from
  `Algebra::radical_power_matrix` and iterates the stored matrix row by row,
  where it used to take a `Vec<Vec<Fp>>` copy from
  `Algebra::radical_power_component` for every ordered vertex pair and every
  degree. Same rows, same order, so `socle` and `socle_series` return the same
  modules. Release profile, best of four interleaved alternations of
  `benches/perf.rs`, this change alone: `socle(A)` on D_4 over F_5 715.1 ns to
  566.1 ns, `socle_series(A)` on D_4 2582.2 ns to 2078.5 ns, and `socle(A)` on
  the regular module of `linear_an(12)` 39880.6 ns to 38923.1 ns, where the
  cost is `element_action` and `kernel_basis` rather than the copies. That left
  `Algebra::radical_power_component` with no caller in the crate, and it is now
  removed.
- `hom::submodule_with_inclusion` and `hom::quotient_with_projection` build
  their `Morphism` through `Morphism::new_unchecked`, and each states the
  theorem that lets them. The inclusion's square at arrow `a` is
  `bases[s(a)] · M(a) = S(a) · bases[t(a)]`, which is the equation
  `express_in_row_basis` solved; the projection's square is the equation
  `solve_columns` solved. Both solves panic rather than return a wrong answer.
  `submodule_with_inclusion` also carries an unstated precondition that is now
  written down: the spanning rows must be linearly independent. Without it
  `S(a)` is not determined and the argument that `S` satisfies the relations
  fails, since it needs `bases[t(ρ)]` to cancel on the left of
  `S(ρ) · bases[t(ρ)] = 0`. A `debug_assert` holds all four current callers to
  it. The four are safe by construction: `kernel_basis` rows carry distinct
  unit entries, `row_space_basis` returns reduced row echelon rows, and
  `decompose::split_from_bases` inverts the stacked bases before it calls.
- `decompose::add_morphisms`, `decompose::split_from_bases`,
  `endo::EndoAlgebra::morphism`, `homspace::scale_morphism`, and the private
  `homspace::morphism_from_flat` build their `Morphism` through
  `Morphism::new_unchecked`. Each is a linear combination of maps that are
  already A-linear for the same pair of modules, or the projection of a module
  onto one of two complementary submodules, and each docstring writes the
  argument out. `iso::verified` keeps its check: it exists to recheck an
  assembled witness, so a failure there is the defect it is looking for.
  `approx.rs` has no `Morphism::new` of its own and takes its share through
  `add_morphisms`. Release profile, best of three runs of `benches/perf.rs`
  before against best of three after, with the exact call counts from
  `--features profiling -- --counts` in parentheses:
  `support_tau_tilting_graph` on D_4 over F_5 30.072 ms to 25.312 ms (75381
  commuting-square checks to 3216), `krull_schmidt(A)` on `linear_an(12)`
  10593 checks to 0, `decompose(A)` on the same 8745 to 0,
  `is_isomorphic(A, A')` 21593 to 11, and `ar_quiver` on `linear_an(5)`
  1.0507 ms to 895.83 us (5284 to 240). `enumerate_over_catalog` on D_4 went
  from 10815 checks to 156; a later change in this release moved its time
  again, so read the pair under `BasicDecomposition::from_catalog` instead. The
  counts are exact; the times were taken on a loaded box and carry the noise of
  it.
- `MutationGraphLimits::max_work_units` now brakes a tau-tilting infinite walk.
  Every rate of the work-unit model gained the factor `e`, the unknown count
  `sum_v (dim M_v)^2` of `Hom(M, M)` for the module the walk is standing on, so
  one unit is one unknown of one Hom system. Charged by call alone the model was
  blind to module size: the Kronecker preprojective ray carries modules that
  grow without bound, and a Hom system at vertex 64 was charged the same single
  unit as one at vertex 1. Measured on `kronecker(2)` over F_5 in the release
  profile, before: 8 vertices 3258 units in 0.007 s, 16 vertices 7082 in 0.081
  s, 32 vertices 14730 in 2.207 s, 64 vertices 30026 in 75.442 s, so seconds
  per unit spread over a factor of 1200 and a 4 million ceiling never fired.
  After: 345293 units in 0.008 s, 3760301 in 0.083 s, 34864237 in 2.886 s, and
  a walk asked for 64 vertices stops at 37 on the default 50 million ceiling
  after 4.406 s, so seconds per unit spread over a factor of 3.8. The counts
  stay exact, deterministic, and field-independent. Every closed walk in the
  fixture set still closes; the asserted ceilings rose with the measured
  counts, A_2 from 1416 units to 6668 (ceiling 4096 to 16384), A_3 from 12895
  to 145712 (32768 to 524288), A_4 from 107808 to 2253257 (262144 to 8388608),
  and D_4 from 140428 to 3951020 (524288 to 8388608), each ceiling the next
  power of two at or above twice the measurement, as before. A finite type
  larger than the fixture set can now charge more than the default, so raise
  the budget rather than read a truncation there as tau-tilting infiniteness.
  A ceiling set to the exact count a walk charges can still truncate: the slot
  precheck reserves the left-mutation cost before the branch is known, and a
  `Fac` slot then charges less than the reservation, so D_4 does not close
  under a ceiling of 3951020. Leave headroom.
- `Algebra` keeps the chain `J^0 ⊇ J^1 ⊇ ... ⊇ J^d = 0` that construction
  already walks to decide nilpotency, and every radical-power query indexes
  it. The query rebuilt the chain from `J^0` on each call, and
  `radical::joint_kernel_bases` calls it once per ordered vertex pair, so over
  `n` vertices `socle` cost `n^4` row reductions and `socle_series` cost that
  again per degree. Construction does the same work as before; the value now
  holds one copy of each power. Release profile, best of three runs of
  `benches/perf.rs` on the regular module of `linear_an(12)` over F_5:
  `socle_series(A)` 62.398 ms to 531.55 us, `socle(A)` 1.3883 ms to 45.491
  us, `krull_schmidt(A)` 383.34 ms to 65.088 ms, `tau(S_0)` 3.2925 ms to
  189.17 us, and the radical-power query at `(0, 0, 12)` 54.081 us to 6.1 ns.
  Keeping the chain costs construction the allocations it used to drop:
  `Algebra::new` on the same fixture goes from 131.79 us to 134.60 us. The
  chain is the same chain, so every value is unchanged and the three
  determinism suites pass byte for byte.
- `hom` and `module::direct_sum` build their `Morphism` values through a
  crate-internal unchecked constructor, so a release build no longer
  revalidates squares that are theorems on those two paths. In `hom` the
  kernel rows are the commuting-square equations written out term by term,
  so every kernel vector is A-linear. In `direct_sum` the arrow matrices are
  block diagonal and the inclusions and projections are block selections.
  Both arguments are written out at `Morphism::new_unchecked`, which under
  `debug_assertions` runs the full `Morphism::new` on its own arguments and
  panics if it rejects them, so `cargo test` still checks every square. The
  dev profile keeps debug assertions on and therefore pays more than before
  on these two paths. Release profile, best of three runs, `linear_an(12)`
  over F_5: `direct_sum k=16` 72.376 us to 11.066 us and `hom(A, A)`
  624.48 us to 369.22 us.
- `hom_dim` counts the Hom basis as `columns - rank` of the commuting-square
  system instead of building and validating the basis and reading its length.
  `SparseMat::kernel_basis` emits one row per free column, so the two agree
  by construction, and rank needs the forward elimination alone. The system
  itself moved into a private `square_constraints`, which `hom` and `hom_dim`
  share. Release profile, best of three runs, `linear_an(12)` over F_5:
  623.39 us to 191.46 us.
- `PrimeField::reduce_wide`, the crate-internal reduction behind every dense
  matrix product, reduces a `u128` accumulator whose high half is zero
  through the 64-bit hardware divide, and keeps the 128-bit route for the
  rest. The 128-bit route is a call to `__umodti3` in the compiler
  runtime. Every product of reduced entries is below `2^62`, so the narrow
  route covers every fixture over F_2 and F_5 and the short dot products over
  F_{2^31-1}; a long dot product near the modulus bound still goes wide.
  Release profile, best of three runs: `krull_schmidt(A)` on `linear_an(12)`
  over F_5 66.101 ms to 48.866 ms, `word_action` over the 78 basis words of
  that algebra 26.980 us to 17.747 us, and `DenseMat::mul` on 10 by 10
  matrices over F_5 453.3 ns to 375.0 ns. Over F_{2^31-1} at 200 by 200 the
  accumulator always leaves 64 bits, and there the extra branch costs about
  2 percent: 2.7085 ms to 2.7523 ms.
- Python: `Algebra.completion_limits` reports five keys where it reported
  three, adding `max_origin_terms` and `max_ambiguities`. This breaks any test
  or caller comparing the dict for equality; read one key instead, or add the
  two new ones.
- Python: `TruncationError.reason` takes two further values, `"origin_budget"`
  and `"ambiguity_budget"`, one per new completion budget. A caller that
  matched the three old values exhaustively now falls through on these.

- `IndecomposableCatalog::entries` returns `&[Arc<IndecomposableModule>]`
  where it returned `&[IndecomposableModule]`. An `ArVertex` now holds the
  catalog's own entry instead of running the locality gate and rebuilding an
  `EndoAlgebra` per vertex. This breaks any external caller that names the
  element type; method calls on an entry are unchanged, because `Arc` derefs.
- `ArDualityWitness::verify` requires `chosen_row == 0`. The field is
  documented as always 0, and the fresh-process fingerprint pins the
  coordinates of that row, but `verify` only checked the index was in range.
  Above residue degree 1 the socle has several RREF rows, and a witness built
  from row 1 with that row's own non-split witness passed every check. The
  sequence it names is almost split; it is not the crate's chosen class, so
  it would fail the release gate that `verify` is meant to stand in for.
- `deterministic_complement` carries one `RowReducer` across the scan where
  it rebuilt a matrix and ran a full rank call per candidate row. Same
  decisions, same kept rows, same order: the kept rows are copies of ambient
  rows, and the golden AR renderings are byte for byte unchanged.
- Three membership solves read their answer off a stored RREF instead of
  eliminating a transpose: `HomSubspace::witness_contains`, the containment
  loop of `HomSubspace::quotient_by`, and the always-on `B^k` inside `Z^k`
  assertion in `ExtSpace::new`. The solution is unique on RREF input, so the
  free-variable convention cannot change it and the coordinates are
  bit-identical.
- The almost-split construction takes a crate-private split-status route that
  reduces `[A | b | I]` once, where the public `ShortExactSequence::
  split_status` reduces `[A | b]` and then `[A | b | I]` again to find the
  dual vector. Every almost-split sequence takes the non-split branch, so it
  paid for two eliminations. The public entry point is unchanged, because the
  wider reduction costs more on a split sequence.
- `ar_quiver` builds each `Hom(X, Y)` basis once. `quiver_of` rebuilt a
  `HomSpace` per catalog pair that `category_radical` had already built, and
  `radical_square_through_catalog` built one it used only for a span. Both
  now go through the new crate-private `HomSubspace::spanned_by`.
- `ExtClassError` gains `ResolutionDisagreement { degree }`. The Yoneda
  product compares the left class's resolution prefix against the product
  space's, term actions and differentials included, and returns this variant
  where a `debug_assert` on dimension vectors used to guard a release-mode
  `expect`. Both prefixes come from `resolve` on one module, so a
  disagreement is a crate defect; matching on `ExtClassError` breaks.
- Elimination on `DenseMat` runs as a forward pass and then a back
  substitution, where one Gauss-Jordan pass did both. `rank` runs the forward
  pass alone, which is `n^3/3` operations against `n^3/2`: 4.8 ms against 7.2
  ms on a 200 x 200 matrix over F_p with p = 2^31 - 1. The dense path now
  splits the way the sparse one already did.
- Elimination on `DenseMat` splits the pivot row out of the buffer and zips
  two slices, where it indexed through `&mut self` with three bounds checks
  and an index multiply-add per entry. Same operations in the same order:
  `rref` on the same 200 x 200 matrix takes 6.2 ms against 7.2 ms.
- `DenseMat::mul` and `DenseMat::mul_vec` accumulate an output entry in `u128`
  and reduce once, where they reduced modulo `p` per multiply-accumulate.
  Every product is below 2^62, so no accumulator a machine can hold
  overflows. A 200 x 200 product takes 2.7 ms against 14.3 ms.
- `SparseMat::kernel_basis` walks each reduced row once and pushes onto the
  output row of every free column in it, where it built each output row by
  repeated `SparseRow::set`, which is `Vec::insert`. Pivot rows are visited in
  increasing pivot column, so each output row comes out already sorted. A
  60 x 60 matrix takes 0.207 ms against 0.288 ms.
- `SparseMat` elimination reuses one merge buffer across its row operations. A
  200 x 200 `rref` takes 7.1 ms against 8.2 ms.
- `DenseMat::kernel_basis` reads the reduced form one whole row at a time,
  where it strided down a column of a row-major buffer.
- `DenseMat::row_space_basis` truncates the reduced form in place, where it
  copied the kept rows into a fresh buffer.
- `DenseMat::zero` panics with the shape in the message when `rows * cols`
  overflows `usize`, and `solve_many` checks its augmented shape the same way.
  That augmented matrix is wider than the input, so it can overflow where the
  input did not.
- `PrimeField::pow` debug-asserts that its argument is reduced, as every other
  arithmetic method on `PrimeField` does. `pow(a, 0)` returns 1 without
  touching `a`, so an unreduced argument used to pass unnoticed.
- None of the above changes a value any routine returns. Pivot selection, free
  column order, row order, and every returned basis are unchanged by
  construction, and `golden_cert`, `determinism_cert`, and `determinism_ar`
  pass against the committed bytes.

- Every `Algebra` constructor now decides admissibility, so
  `Algebra::from_verified` and `Algebra::from_verified_with_limits` return
  `Result<Arc<Algebra>, AlgebraBuildError>` instead of `Arc<Algebra>`. This
  breaks both call sites: add `?` or `.expect(...)`. The check needs the
  multiplication tables, and both entry points build an algebra without
  going through `Algebra::new`, so a reloaded certificate would otherwise
  bypass it.
- `Algebra::nilpotency_degree` reads the value construction decided instead
  of recomputing the radical chain. It is now O(1) and it no longer panics:
  the assert it fired on a stable nonzero power is now an internal invariant,
  because the non-nilpotent case is rejected before an `Algebra` exists. Its
  docstring no longer says "the radical of a finite-dimensional algebra is
  nilpotent"; that is true of the Jacobson radical and false of the arrow
  ideal `J` this method measures.
- `Presentation::new` no longer rechecks coefficients. Rejecting a field
  mismatch outright makes the check unreachable: `Relation::new` established
  canonical nonzero coefficients over the field the relation carries, and
  that field is now this field. The remaining per-term check is that every
  word is a path of the quiver, so `RelationError::ZeroCoefficient` and
  `RelationError::NonCanonicalCoefficient` no longer come out of
  `Presentation::new`. Both still come out of `Relation::new`.
- `Relation` compares with its field, so two relations with equal terms over
  different fields are no longer equal.
- Python: `Algebra.ar_quiver` and `Module.category_radical` report a failed
  hom or hom-space computation as `DefectError` instead of `ValueError`. Both
  entry points validate their endpoints first, so these variants mean the
  crate contradicted itself, and the module header and the v0.4 design both
  put defects under `RuntimeError`. This breaks a catch site: an `except
  ValueError` around either call no longer catches these two variants. No
  valid input reaches them, and a run that hits one is a bug report.
- Python: `Module.tau` reports a certified route disagreement as
  `DefectError` instead of a bare `RuntimeError`. `DefectError` subclasses
  `RuntimeError`, so every documented promise and existing catch site holds.
- Python: the message for a monomial algebra asked for a certificate or an AR
  quiver without a field now reads "a monomial presentation is field-free and
  a certificate is not; pass a field to build a certificate over it", with the
  construction named in both halves. One function writes both messages. The
  exception class stays `ValueError`.
- Python: long computations release the GIL. Building a monomial algebra over
  a field, `Algebra.from_relations`, `Algebra.from_certificate`,
  `ar_quiver`, `hom`, `ext_dim`, `ext_table`, `ext_space`, `resolve`,
  `coresolve`, `decompose`, `krull_schmidt`, `tau`, `almost_split`,
  `category_radical`, `is_isomorphic`, and the enumeration functions run
  detached, so other Python threads keep running instead of freezing until the
  call returns. A Ctrl-C still takes effect only when the call returns: there
  is no cancellation point inside a computation.
- `IsoClass` gained the public field `endo`, so a struct literal of it no
  longer compiles. Reading `representative` and `multiplicity` is unaffected.
- `EndoAlgebra::new` no longer composes all `dim²` basis pairs. The
  structure-constant table is built by the first `EndoAlgebra::multiply` and
  then kept; the radical, the semisimple quotient, and `is_local` read none of
  it, and `EndoAlgebra` stays `Sync`. Three more costs went with it. The
  coordinates of a morphism are read off its flattened row instead of solved
  for, because the `hom` basis carries the identity at the free columns of the
  system it solved. The first radical round is one matrix product, since its
  characteristic-polynomial coefficient is minus a trace. And `decompose`
  inherits each summand's radical from the node it was split off, through
  `rad(eAe) = e rad(A) e`, instead of running a fresh chain per node. On
  `P⊕P⊕P⊕P` over `F_5[x]/(x⁴)`, where `dim End` is 64, `EndoAlgebra::new`
  drops from 192 ms to 4.9 ms, `decompose` from 211 ms to 5.1 ms, and
  `krull_schmidt` from 210 ms to 5.2 ms in the dev profile;
  `cargo test -p auslander` drops from 35 s to 3.9 s. Every stored matrix is
  unchanged entry for entry, the radical basis and the quotient coordinates
  the AR machinery keys on included.
- `EndoAlgebra::in_radical` reduces against the radical rows, which are in
  reduced row echelon form, instead of ranking a stacked matrix:
  `radical_dim · dim` field operations, no elimination. 12800 queries against
  a 64-dimensional algebra drop from 133 ms to 2.3 ms.
- `krull_schmidt` compares invariants (dimension vector, radical and socle
  series, `dim End`, residue degree) before the radical criterion, and the
  criterion itself runs the two series tests and a Hom-dimension test before
  it composes anything. Each test is a proof of non-isomorphism, so `None`
  claims exactly what it claimed before.
- The radical chain cites Cohen, Ivanyos and Wales, J. Pure Appl. Algebra
  117/118 (1997), for its bound `p^i ≤ dim_k M`. Rónyai works from structure
  constants, so his bound is over `dim_k End(M)`, usually the larger; running
  to that one changes no output, and the docstring says why.
- `EndoAlgebra::split_idempotent` documents the Newton lift as convergent
  rather than budgeted. With `δ = e² − e` the iterate gives
  `f(e)² − f(e) = δ²(4δ − 3)` in every characteristic, so
  `ceil(log2(radical_dim + 1))` rounds suffice and the 64 rounds are a
  defensive stop. The Cantor-Zassenhaus draw count stays a real budget.

### Removed

- `ClassicalOneTiltingModule`, `TiltingClassification`, `CoresolutionTerm`,
  `TiltingError`, `tilting::classify`, the whole `tilting` module, and the
  Python `ClassicalOneTiltingModule` and `TiltingRejection`. The release theme
  is that enumeration stops being a list and becomes a certificate. This type
  verified one supplied `T` and enumerated nothing, and none of its four
  witnesses reached the closure certificate, so it did not carry the theme.
  Its projective dimension stopped at one only because the checked complex
  layer does not exist yet. Tilting comes back with that layer, where the
  generation axiom for `n` above one is a checked exact complex
  `0 -> A -> T^0 -> ... -> T^n -> 0` instead of a single short exact sequence.
  Nothing else in the crate called it.
- `MinimalRightApproximation` and `approx::right_approximation`. Left mutation
  is the only production caller of the approximation layer and uses the left
  side alone, so the right side was reached from tests and from
  `ClassicalOneTiltingModule` only, and it went with it.
  `MinimalLeftApproximation` and `approx::left_approximation` are unchanged,
  including the multiplicity count over the residue division ring.
- `MonomialPresentation` and the monomial constructors leave `algebra` for the
  new `monomial` module, and `Algebra::from_monomial` is gone. A monomial ideal
  is quiver data and forbidden words, and nothing about it needs a field, so
  `monomial::MonomialIdeal` carries that data and
  `monomial::MonomialPresentation` adds the field-free analysis: the
  standard-path basis, the finiteness decision, and the Cartan matrix. Neither
  type builds a runtime algebra. Monomial input takes the one pipeline every
  algebra takes: `algebra::monomial_presentation` turns an ideal into a
  `Presentation` of one-term relations, `algebra::monomial_limits` derives
  budgets for it, and `algebra::monomial_algebra` is the pair applied.
  `algebra.rs` went from 1915 lines to 1347.
  `algebra::monomial_completion_limits`, the `*_presentation` constructors, and
  `AlgebraError` went with the move. The named runtime constructors
  (`linear_an`, `kronecker`, and the rest) keep their names, signatures, and
  results.
- `HomVanishingWitness` and `SummandPairVanishing`. A vanishing claim has no
  element to exhibit, so a positive witness for `Hom(X_i, tau X_j) = 0` carried
  no data: the pair of indices was the whole content. The private construction
  of `TauRigidModule` is the proof token now, and `TauRigidModule::verify`
  recomputes every translate and every dimension rather than reading a stored
  one. The indices are `TauRigidModule::vanishing_pairs`.
- The `Tau` enum. `ar::tau` returns `Result<Module, TauError>`, and a
  projective module gives the zero module. That module keeps its algebra and
  its dimension vector, which is more than `Tau::Zero` carried, so the enum was
  a second spelling of a value the crate already had. Test the case with
  `Module::is_zero`. `tau_via_nakayama_kernel` and `tau_via_transpose_dual`
  already returned a `Module` and are unchanged.
- `NonVanishingHomWitness`, the stored projective part of
  `SupportTauTiltingPair` and `AlmostCompletePair`, and the subset generator
  behind `enumerate_over_catalog`. The projective part is forced by the four
  conditions, so the pair types derive it and the enumerator no longer walks
  vertex subsets looking for one. `NonVanishingHomWitness` went with the
  morphism condition 2 used to build; see the `PairRejection` entry under
  Changed.
- `Algebra::radical_power_component`. `Algebra::radical_power_matrix` returns
  the same rows in the same order, borrowed from the chain that construction
  keeps, where this method copied them into an owned `Vec<Vec<Fp>>` on every
  call. This breaks any external caller: take the `DenseMat` and read its rows.
- `PrimeField::batch_inv`, which had no caller. Montgomery's trick needs the
  whole slice up front, and the one hot loop that inverts many elements is
  the pivot normalization in `rref`, whose inversions are sequential: each
  pivot depends on the elimination the last one drove. This breaks any
  external caller. Invert entry by entry with `PrimeField::inv`.

### Fixed

- `TauCache` could hand back the translate of a different module. It was keyed
  by an index the caller supplied, guarded by a comparison of dimension vectors
  alone, so two non-isomorphic modules with one dimension vector filed under
  one index collided and the second query answered with the first module's
  translate. Over `kronecker(2)` the modules `X` and `Y` with arrow maps
  `(1, 0)` and `(0, 1)` are exactly that case: both have dimension vector
  `(1, 1)`, they are not isomorphic, and each is its own translate up to
  isomorphism. Handed `tau X` where it asked for `tau Y`, the caller certified
  `Y` tau-rigid, and `dim Hom(Y, tau Y)` is 1. The cache is now keyed by
  nominal `Module` identity: the key is the address of the module value, and
  the entry keeps a clone of it, so no later module can take a live key. A
  separately built isomorphic module misses and pays one `tau`. Recognizing it
  would take a certified isomorphism test against every entry of the same
  dimension vector, and an uncertified guess is what caused this. Callers that
  hold a decomposition avoid the miss by keeping the summand values, as
  `BasicDecomposition::without` and `BasicDecomposition::from_catalog` do. The
  regression test is
  `a_shared_cache_separates_two_modules_with_one_dimension_vector` in
  `taurigid.rs`, run over F_2 and F_5.
- The walk built a `ClosedSupportTauTiltingGraph` without running
  `ClosureWitness::verify`. A drained frontier says the builder found a branch
  at every slot and placed every target. It does not say the seven obligations
  hold, which is a separate recheck of the stored pairs and maps. So a
  construction defect could produce a closed graph whose own `verify` returns
  false, and the Python binding offered `pairs()` on it at once as the complete
  list. The type is now built only past the verifier, in one crate-private
  function with no other route to the value, in Rust and through Python. A
  failed recheck is `GraphError::Defect` and no graph comes back at all.
- A walk could charge past `max_work_units` and still report a closed graph.
  Only the slot precheck was checked against the budget. The work that follows
  a slot went on the ledger and was never checked: the `tau` misses, the
  fingerprints, the isomorphism tests, and a new vertex. The budget is now
  enforced after every slot and again when the frontier drains, so a closed
  outcome never reports more units than its limit. Without the second check the
  one-vertex algebra closed over its ceiling: its only slot lands on `(0, A)`,
  which has no further slot to precheck.
- The completeness citation named the wrong theorem. It read the closure
  argument as AIR Corollary 2.38, "a finite connected component of the support
  tau-tilting quiver is the whole quiver". What the obligations establish is
  finite left closure: a finite set of basic support tau-tilting pairs that
  holds `(A, 0)` and holds every left mutation of every member is every such
  pair. That is AIR Theorem 2.35(b), equivalently the descending half of the
  proof of Corollary 2.38. Appealing to Corollary 2.38 itself would also have
  to rule out mutations from outside the set landing inside it, which the walk
  never checks. Completeness rests on obligations 1 to 5. Obligation 6,
  connectivity, follows from them: the descending chain of Theorem 2.35(b)
  reaches every pair from `(A, 0)` along edges obligation 4 stores. Obligation
  7, `n`-regularity, is outside the argument altogether. Both stay gates, since
  a failure of either contradicts a theorem whose hypotheses hold and is a
  crate defect. No computed value changes.
- `ArDualityWitness::verify` rechecks the `ExtSpace` it certifies against,
  which it consumed on trust. It recomputed tau, the radical basis, the
  action matrices, the socle, both dimension gates, exactness, and the
  non-split witness, and every one of those recomputations reads the stored
  space: its resolution, its bases, its representatives. So a tampered space
  certified itself. Concretely, over `k[x]/(x^3)` with `M = S` the radical of
  `End(S)` is zero, so `B^1` has no rows; replacing `B^1` with the complement
  row left the action list empty, the socle the whole line, and the reduction
  of the class still `[1]`, and every gate passed. Emptying the cocycle basis
  or scaling a stored representative passed too, because no other path reads
  either. `verify` now calls `ExtSpace::matches_recomputation` first, and
  `CatalogWitness::verify` does the same before it recovers the class.
- `ProductWitness::verify` and `ArDualityWitness::verify` no longer overclaim
  in their docstrings. The product witness said it trusted no stored matrix
  while trusting both factor spaces entirely, and the duality witness said
  every stored value was recomputed, which the space above disproves. Each
  now states the boundary it actually checks.
- The `End(M)` action on `Ext^1(M, tau M)` is documented as a left action,
  equivalently a right `End(M)^op` action, where the module docs and the v0.4
  design called it a right action. `EndoAlgebra::multiply` is diagrammatic
  and `Ext^1(-, tau M)` is contravariant, so `A_{phi.then(psi)} = A_psi
  A_phi`, an anti-representation. No computed value changes: `rad End(M)` is
  two-sided, so its left and right annihilators are one set and the socle is
  the same. A test pins the identity on a module with noncommutative `End`.
- The radical criterion returns `None` for modules over separately built
  algebras instead of panicking. Equal dimension vectors sent the pair
  straight into `hom`, which errors on unrelated algebras, and the call
  unwrapped that error. Two modules of the same shape over two `Algebra`
  values reach it through `krull_schmidt` and through the AR machinery.
  Algebra identity is nominal, so such modules are never isomorphic.
- A non-admissible ideal is rejected instead of hanging or panicking later.
  Nothing enforced admissibility: `Relation::new` checks that every word has
  length >= 2, which gives `I ⊆ J²`, and completion decides finite dimension
  from the leading words alone. One loop `x` with the relation `x³ - x²`
  passes both, and the quotient is finite dimensional of dimension 3, but the
  arrow ideal `J = span(x, x²)` has `J² = J³ = span(x²)` and never reaches
  zero. `Algebra::nilpotency_degree` then fired its internal assert,
  `radical::socle_series` panicked through it, and `radical::radical_series`
  and `enumerate::nakayama_indecomposables` looped forever. Construction now
  iterates the radical step at most `dim` times: the chain either reaches
  zero, which gives the nilpotency degree, or repeats a nonzero dimension,
  which proves it stable and rejects the input with the new
  `AlgebraBuildError::NonAdmissible { stable_power, dimension }`. No
  leading-word criterion can decide this: `(x³)` and `(x³ - x²)` have the
  same leading word, the same automaton, and the same normal words, and only
  the first is admissible.
- `Algebra::new` checks that the verified certificate's `input_relations` are
  the relations of the presentation it was handed, and reports
  `AlgebraBuildError::InputRelationsMismatch { index }` when they are not.
  The certificate ties `origin` to `input_relations` and `input_relations`
  into the ideal through `membership`, but nothing tied `input_relations` to
  what the caller asked for.
- Python: a panic inside the crate no longer bricks a monomial `Algebra`. The
  per-field cache took its lock with `expect`, so a panic while the lock was
  held poisoned it and every later call on that object failed. The lock now
  recovers its data through `PoisonError::into_inner`, and it is no longer
  held across the build, which would deadlock a second thread that blocks on
  it while holding the GIL.

## [0.4.0] - 2026-08-06

The Auslander-Reiten layer, witnessed. The homological layer moves from
dimensions to objects that carry checkable witnesses: Ext classes, actual
extensions, almost-split sequences, irreducible morphisms, and valued AR
quivers. Every constructed object rechecks the claim its type makes, and no
public field permits building an unchecked value.

The release is additive. No public v0.3 API is removed or changed; `ext_dim`,
`ext_table`, `tau`, and every other v0.3 entry point keep their signatures and
behavior.

### Added

- `HomSpace`, `HomSubspace`, `HomQuotient`: `Hom_A(M, N)` as an explicit
  vector space over the deterministic `hom` basis, with flat coordinates,
  RREF subspace bases, membership witnesses, and quotients whose
  representatives come from one crate-wide deterministic complement rule
  (`homspace`).
- `IndecomposableModule`: a checked wrapper that exists only together with
  the locality proof of its endomorphism algebra, with `residue_degree`,
  `is_projective`, and `is_injective`. Rejections are typed: the zero
  module, a verified split with its summand count, or an honest
  `Undetermined` (`indec`).
- `ExtSpace` and `ExtClass`: `Ext^k(M, N)` as an explicit vector space over
  the minimal resolution prefix, with RREF cocycle and coboundary bases, the
  deterministic complement, and one representative cocycle per class.
  Degree 0 is `Hom(M, N)` and carries the Yoneda unit; class arithmetic and
  equality require compatible spaces, and incompatible operands are a typed
  error rather than `false` (`ext`).
- Yoneda products through stored chain lifts: `ExtClass::then` in the
  endpoint order of `Morphism::then`, and `then_with_witness`, whose
  `ProductWitness` rechecks the lift identities, the reduction by
  multiplication and membership, and the product space's bases against a
  fresh recomputation. The release gates split by level. Coboundary
  invariance of the product lift and splicing agreement through the
  realized extension are representative-level gates, and run as in-module
  unit tests in `ext.rs`. The class-level unit, bilinearity, and
  associativity laws run in `tests/acceptance_ar.rs` on every basis tuple
  within the acceptance degree bound (`ext`).
- `ShortExactSequence`: exact per vertex by construction (mono, epi, zero
  composite, and additive dimensions force exactness). `from_ext1` realizes
  a degree-1 class as an extension, `ext1_class` recovers the class, and the
  acceptance suite pins the round trip on every fixture basis class
  (`sequence`).
- `SplitStatus` with proof either way: a `SplitWitness` carrying a
  retraction and section that recheck by multiplication, or a
  `NonSplitWitness` carrying a dual vector that proves the retraction
  system inconsistent, both over the same fixed equation order (`sequence`).
- `stable_hom` and `stable_end`: Hom modulo the maps that factor through a
  projective, computed through the projective cover and returned as a
  deterministic quotient (`almost_split`).
- `almost_split`: witnessed almost-split sequences through the AR socle
  construction. `End(M)` acts on `Ext^1(M, tau M)`; the chosen class is the
  first RREF row of the socle, deterministic and documented as not
  canonical. A projective input is `AlmostSplitOutcome::Projective`, an
  outcome rather than an error. Two witness routes: `ArDualityWitness`
  stores the radical basis, action traces, socle RREF, dimension equalities,
  and the non-split witness; `almost_split_via_catalog` stores factorization
  data for `im(Hom(X, E) -> Hom(X, M)) = rad(X, M)` and the dual left check
  against every entry of an exhaustive catalog. Both `verify` from stored
  data plus the live modules, and the two routes must validate the same
  sequence. Internal cross-check failures are `DefectKind` values, never
  silent (`almost_split`).
- The category radical: `rad(X, Y)` between certified indecomposables,
  exact with no catalog. `IndecomposableCatalog` wraps the two complete
  enumerations (Nakayama, zero-ideal Dynkin); a plain module list never
  becomes a catalog. `radical_square_through_catalog` and
  `irreducible_quotient` are catalog-exact (`arquiver`).
- `ar_quiver`: the valued AR quiver on the catalog domains. Vertices carry
  the module, residue degree, and projectivity and injectivity flags;
  arrows carry `dim_Fp Irr(X, Y)` and its dimensions over both residue
  fields, and `ArrowValuation` never reports a bare multiplicity where the
  residue degrees make one ambiguous. The quiver is complete for its
  domain; no budget cuts it short (`arquiver`).
- The AR acceptance matrix (`tests/acceptance_ar.rs`), split into two
  honest tiers: Ext spaces, product laws, extension round trips, stable
  Hom, and AR-duality almost-split sequences on the full non-monomial
  matrix; AR quivers, catalog witnesses, the middle-term cross-check
  against arrow values, and valuations where an exhaustive catalog exists.
  Hand-derived terms pin `k[x]/(x^3)`, linear A_3, the commutative square,
  and preprojective A_3.
- A mutation corpus for the AR layer (`tests/mutation_ar.rs`): every
  checking constructor and witness verifier reachable from the public API
  rejects tampered input. Witness fields no public constructor can set are
  mutated field by field in the in-module unit tests of `ext.rs`,
  `sequence.rs`, `almost_split.rs`, and `arquiver.rs`, which the corpus
  file lists by name per design bullet.
- Determinism gates for the AR layer (`tests/determinism_ar.rs`):
  recomputed Ext bases are byte-identical, two fresh processes agree on a
  fingerprint of Ext bases, chosen AR classes, and AR-quiver renderings,
  and golden normalized renderings under `tests/golden-ar/` are compared
  byte for byte.
- QPA oracle schema v6: schema v5 unchanged plus Auslander-Reiten fields
  per fixture, produced by a real GAP+QPA run. The fields run over a fixed
  designated module list, the simples, then the indecomposable
  projectives, then the indecomposable injectives, and they hold
  almost-split sequences with Krull-Schmidt middle terms, irreducible
  morphisms with valuations, Ext algebra generator counts and product
  ranks, Yoneda product ranks between simples, stable Hom dimensions,
  tau-rigidity, and tau periods. Oracle fields stay basis-independent
  invariants; the internal duality consistency checks stay out of the
  schema.
- Python: `Module.ext_space` with `ExtSpace` and `ExtClass` (arithmetic,
  Yoneda `then`, `representative`, `extension` in degree 1),
  `ShortExactSequence` with `split_status` and `verify`,
  `Module.almost_split` returning a verifiable `AlmostSplitSequence` or
  `AlmostSplitOutcome.PROJECTIVE`, `Module.category_radical`, and
  `Algebra.ar_quiver` with valued arrows and a `plain_multiplicity` that
  raises `ValuedArrowError` instead of guessing. New exception types follow
  the taxonomy: `NotIndecomposableError`, `IncompatibleSpacesError`,
  `ValuedArrowError`, and `UnsupportedDomainError` subclass `ValueError`;
  `DefectError` subclasses `RuntimeError` and reports a library bug, never
  bad input.

### Changed

- Python: `TruncationError` is re-parented under the new
  `BudgetExhaustedError(RuntimeError)` base, so future operation-specific
  budget errors share it. `TruncationError` remains a `RuntimeError`, so
  every existing `except` clause keeps working; this is the only change to
  the existing Python surface.

## [0.3.0] - 2026-08-06

General admissible ideals, end to end. Every operation the crate offers now
works over a general relation ideal, not only a monomial one. Every algebra is
built by completion into a reduced Groebner basis and independent verification
of the emitted certificate.

### Added

- `Relation` and `Presentation`: uniform relations, each a k-combination of
  paths of length >= 2 that share one source and one target. Input is
  validated and normalized; non-uniform input is rejected, not decomposed
  (`relation`).
- The sealed admissible order `deglex-arrowid-v1`: length first, then
  lexicographic by arrow id. There are no user-supplied comparators (`order`).
- The completion engine: Bergman-style completion with full remainder
  division, overlap and inclusion compositions, self-overlaps included, and
  interreduction to the unique reduced Groebner basis. Budgets are checked
  inside the reduction and ambiguity loops; an exhausted budget returns
  `Outcome::Truncated` with diagnostics and no certificate (`completion`).
- The certificate: the reduced Groebner basis, a two-sided expansion of every
  basis element in the input relations, a zero-remainder reduction trace for
  every input relation, the complete overlap and inclusion ambiguity inventory
  with reduction traces, the normal words, the normal-word automaton (states
  and sparse transitions in canonical order), and a finiteness section that is
  either `{"finite": true}` or an `infinite` object carrying a
  `(prefix, cycle)` witness. Encoding is canonical and decoding is strict,
  with container nesting bounded by `MAX_JSON_DEPTH` (`certificate`).
- The independent verifier. It reads certificate bytes and shares no
  completion, ambiguity-enumeration, automaton, or reduction code with the
  engine. It re-enumerates every ambiguity itself. It rebuilds the
  normal-word automaton itself and requires the certificate's automaton to
  match it exactly. It decides finiteness by acyclicity, and the finiteness
  claim must match that decision; an infinite claim needs a fully replayed
  witness, and the verifier reports the certificate's own verified witness.
  The ambiguity and normal-word lists are compared in lockstep against lazy
  enumerations, so verifier memory stays bounded by the certificate and
  automaton sizes, and a declared vertex count must be covered by automaton
  states before the quiver is allocated. It produces `VerifiedCompletion`,
  which has no public constructor elsewhere (`verify`).
- Completion budgets as work units: `max_steps` counts each reduction step
  and each emitted normal word, checked before the word is allocated, so a
  huge finite normal-word language truncates honestly (`completion`).
- Limits propagation: `Algebra` stores its effective `CompletionLimits`
  (`completion_limits()`), and `opposite` recompletes with the stored limits,
  so tau, injective envelopes, coresolutions, and injective dimensions
  inherit them. `Algebra::from_monomial` takes explicit limits;
  `monomial_completion_limits` derives limits that are always adequate for a
  monomial presentation, and the named monomial constructors use them, so
  `truncated_poly(65, field)` completes. `Algebra::from_verified` keeps the
  default limits by policy (certificate bytes never carry or select
  downstream budgets); `Algebra::from_verified_with_limits` preserves budgets
  across a reload (`algebra`).
- Golden certificates: four committed certificate byte references under
  `crates/auslander/tests/golden-certificates/`, generated by this library as
  determinism canaries and compared byte for byte by
  `tests/golden_cert.rs` on every test run.
- `Algebra`: the runtime algebra type. It owns its prime field, holds the
  reduced Groebner basis and the normal-word basis, and exists only after
  verification passes. `Algebra::new` runs completion and verifies the bytes;
  `Algebra::from_verified` rebuilds from a verified certificate;
  `Algebra::from_monomial` routes monomial input through the same pipeline.
  `nf_word` gives the normal form of any path, `mul_basis` the product of two
  basis elements, and `radical_power_component` a radical power by row-space
  iteration rather than by word length (`algebra`).
- `MonomialPresentation`: the field-free combinatorics of a monomial ideal
  (forbidden words, the standard-path automaton, the exact finiteness
  decision, dimension, Cartan data), kept as an input and analysis type
  (`algebra`).
- `commutative_square`, the algebra of the square quiver with `ab - cd`
  (`algebra`).
- General relations downstream. Modules, morphisms, resolutions and
  coresolutions, Ext, duality, `ElementMatrix`, `EndoAlgebra`, radical and
  socle series, `decompose`, `krull_schmidt`, `is_isomorphic`, and both `tau`
  routes all run over a general quotient.
  `crates/auslander/tests/acceptance_nonmonomial.rs` exercises them over the
  commutative square, the preprojective algebra of A_3, and the inhomogeneous
  `kQ/(ab - cde)`.
- Certificate determinism gates: identical input and limits produce identical
  bytes in one process and across two fresh processes.
- A tamper corpus for the verifier: modified coefficients, non-monic and
  non-reduced bases, wrong origin expansions, dropped trace steps, forged
  contexts, missing, extra, duplicated, misplaced and out-of-order
  ambiguities, wrong normal-word lists, false automaton edges, missing and
  reordered automaton states, duplicate and out-of-order transitions, false
  finiteness claims in both directions, and forged infinite-dimension
  witnesses (bad prefix, bad cycle, empty cycle, non-returning cycle). Each
  is rejected with its own error.
- QPA oracle schema v5: an explicit prime field per fixture,
  coefficient-bearing relations, the admissible-order identifier,
  decomposition multiplicities, fixture family identifiers, presentation
  identity separate from ideal identity, GAP and QPA version provenance, and
  typed outcomes. New fixture families: the commutative square, the
  preprojective algebra of A_3, a self-overlap, an inclusion ambiguity, an
  inhomogeneous presentation, redundant and permuted presentations of one
  ideal, and a characteristic-sensitive family.
- Python: `Algebra.from_relations` for general relations with per-run
  completion budgets, `algebra.certificate_json()` and
  `Algebra.from_certificate` for the dump, verify, and reload workflow,
  `algebra.field`, and `TruncationError` carrying the completion diagnostics.
  `Algebra.from_certificate` takes the same optional budget keywords as
  `from_relations`, used only as the rebuilt algebra's downstream limits, and
  `algebra.completion_limits` reports the effective (or, for a field-free
  monomial algebra, derived) limits as a dict. Derived completions map an
  exhausted budget to `TruncationError` and every other build failure to
  `RuntimeError`, because their input is a verified algebra, not user input.

### Changed

- `MonomialAlgebra` is removed. Monomial input goes through
  `MonomialPresentation` plus `Algebra::from_monomial`, or through a named
  constructor. In Python, `MonomialAlgebra` stays as an alias of `Algebra`.
- The named constructors take a field and build a runtime algebra:
  `linear_an`, `kronecker`, `dual_numbers`, `truncated_poly`,
  `linear_nakayama`, `cyclic_nakayama`, `radical_square_zero_cycle`, and
  `an_with_relations`. All but `dual_numbers` also have a `_presentation` form
  that stops at the field-free `MonomialPresentation`.
- `Module::new`, `Module::simple`, `Module::projective`, `Module::injective`,
  `ElementMatrix::new`, `global_dimension`, and `dynkin_indecomposables` no
  longer take a field argument. The field comes from the algebra.
- `Algebra::right_mul` and `Algebra::left_mul` return a sparse coefficient row
  `&[(BasisIdx, Fp)]` instead of `Option<BasisIdx>`. A product of two basis
  elements is a combination of normal words in general. Over a monomial ideal
  the row has at most one entry.
- `Algebra::relations` replaces `forbidden` and returns the reduced Groebner
  basis as `Relation` values.
- `opposite`, `injective_envelope`, `coresolve`, and `injective_dimension`
  return `Result<_, AlgebraBuildError>`. The opposite algebra reverses every
  relation word and then runs the pipeline again, so building it can fail.
- `HomError::DifferentFields` and `ExtError::DifferentFields` are removed. The
  field comes from the algebra, so `DifferentAlgebras` covers both cases.
- `path_index` returning `Ok(None)` means "not a normal word", not "zero". A
  non-normal path equals its normal form, which `nf_word` computes. The two
  notions still agree over a monomial ideal.

### Fixed

- `ElementMatrix::transpose_over` assumed that the reversal of a normal word
  is normal on the opposite side, and indexed the reversed word directly. The
  assumption holds for a monomial ideal and fails for a general one: on the
  square quiver with arrow ids `a = 0`, `d = 1`, `c = 2`, `b = 3` and the
  relation `ab - cd`, the normal word `ab` reverses to the Groebner leading
  word of the opposite side, and the old code would have panicked there. The
  transpose now expands every reversed word to its normal form on the other
  side, and a unit test pins that case. `transpose_over` carries the
  transpose-dual route of `tau`, so the assumption sat under one of the two
  routes the translate cross-checks.

## [0.2.0] - 2026-08-05

Decomposition, isomorphism, duality, and the Auslander-Reiten translate. Each
returns a machine-checkable witness or an explicit statement that no witness
was found.

### Added

- Opposite algebras, the k-dual `D`, and the Nakayama functor
  `ν = D ∘ Hom(−, A)`. `ElementMatrix` holds matrices over the algebra rather
  than over the field (`opposite`).
- `injective_envelope`, `coresolve`, and `injective_dimension`. A minimal
  injective coresolution is the k-dual of a minimal projective resolution over
  `A^op` and carries the same `ResolutionEnd` and `Bounded` status
  (`injective`).
- `EndoAlgebra`: `End(M)` as a structure-constant algebra with an exact
  Jacobson radical over `F_p` in every characteristic. The computation uses the
  Friedl-Rónyai chain and never trusts the trace form in small characteristic
  (`endo`).
- `decompose` and `krull_schmidt`: verified splittings. Each summand carries a
  `Certificate`, either `Indecomposable` or an honest `Undetermined`
  (`decompose`).
- `is_isomorphic`: an isomorphism verified by a checked two-sided inverse, or a
  proof of non-isomorphism as one of five `Obstruction` kinds (`iso`).
- `tau`: the Auslander-Reiten translate, computed two ways on every call and
  cross-checked: by the Nakayama kernel, and by transpose-then-dual over
  `A^op`. The routes share the minimal presentation and the element-matrix
  encoding and are independent downstream of it. A certified disagreement is
  `TauError::RoutesDisagree`; an undecided cross-check is
  `TauError::AgreementUnknown` (`ar`).
- `nakayama_indecomposables`: every indecomposable of a Nakayama algebra, each
  with its certificate (`enumerate`).
- Exact Dynkin and Euclidean recognition, the generalized Cartan matrix,
  positive roots, and `dynkin_indecomposables`, which constructs every
  indecomposable of a hereditary Dynkin path algebra through BGP reflection
  functors. Preconditions are typed errors (`dynkin`).
- QPA oracle schema v4: `tau`, `tau` of the injectives, and QPA-verified
  injective dimensions of the simples. The document reader is strict and
  rejects malformed input rather than skipping fields. Under `QPA_ORACLE=1`
  the comparison against live GAP output is byte for byte.
- Python bindings for the new decision surface: `decompose`, `krull_schmidt`,
  `is_isomorphic`, `tau`, injective envelopes, coresolutions and dimensions,
  projective covers, and the Dynkin and Nakayama enumerators, with `Resolution`
  exposing terms, maps, and augmentation, dual in shape to
  `InjectiveCoresolution`. The certificate, obstruction, and resolution-status
  types are exposed, not flattened. The lower-level machinery (`EndoAlgebra`,
  opposite algebras, the k-dual, `ElementMatrix`) stays Rust-only.

### Fixed

- `dynkin_quiver` and `euclidean_quiver` truncated vertex counts past the
  `u32` indexing of `Quiver` and silently built a small wrong quiver
  (`EuclideanType::A(2^32)` became a one-vertex loop). Both now return `None`
  when the diagram cannot be represented; the Python functions raise
  `ValueError`. The abstract counts stay mathematical: `num_vertices` and
  `indecomposable_count` answer over `usize`.
- `decompose` could not split a direct sum of isomorphic copies of a module
  over a large field. The idempotent search produced only central idempotents.
  Central idempotents separate Wedderburn blocks, so they cannot split
  `End(P^n) = M_n(k[x]/(x^d))`. The random Fitting fallback almost never drew a
  non-unit: a uniform element of `M_n(F_q)` is invertible with probability
  `1 - O(1/q)`. Non-units are now constructed rather than sampled, by splitting
  the minimal polynomial of a drawn element into coprime factors with
  Berlekamp's algorithm. A base-field root does not suffice. When the residue
  field is a proper extension `F_{p^d}`, as for `End(W ⊕ W)` with
  `End(W) = F_{p^d}`, a drawn element has a base-field eigenvalue with
  probability `O(p^(1-d))`; the two irreducible factors that do split it can
  share a degree. The suite missed the defect because the decomposition
  tests ran only over F_2 and F_5.

## [0.1.0] - 2026-07-24

Initial release.

### Added

- Monomial bound quiver algebras kQ/I over checked prime fields, with
  finite-dimensionality certified at construction.
- Validated right modules; hom bases, kernels, cokernels; radical and socle
  series.
- Minimal projective resolutions and exact Ext in every degree, with typed
  partiality (`Bounded`, `ResolutionEnd`).
- QPA differential oracle with committed truth
  (`crates/auslander/tests/qpa-oracle/`).
- Python bindings (abi3, CPython >= 3.10) in `crates/auslander-py`.
