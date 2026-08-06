# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
  fresh recomputation. The release gates split by level:
  representative-level coboundary invariance of the product lift and
  splicing agreement through the realized extension are in-module unit
  gates in `ext.rs`; the class-level unit, bilinearity, and associativity
  laws run in `tests/acceptance_ar.rs` on every basis tuple within the
  acceptance degree bound (`ext`).
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
  per fixture, produced by a real GAP+QPA run over a fixed designated
  module list (simples, indecomposable projectives, indecomposable
  injectives): almost-split sequences with Krull-Schmidt middle terms,
  irreducible morphisms with valuations, Ext algebra generator counts and
  product ranks, Yoneda product ranks between simples, stable Hom
  dimensions, tau-rigidity, and tau periods. Oracle fields stay
  basis-independent invariants; the internal duality consistency checks
  stay out of the schema.
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
- The independent verifier. It reads certificate bytes, shares no completion,
  ambiguity-enumeration, automaton, or reduction code with the engine,
  re-enumerates every ambiguity itself, rebuilds the normal-word automaton
  itself and requires the certificate's automaton to match it exactly, and
  decides finiteness by acyclicity. The finiteness claim must match that
  decision; an infinite claim needs a fully replayed witness, and the
  verifier reports the certificate's own verified witness. The ambiguity and
  normal-word lists are compared in lockstep against lazy enumerations, so
  verifier memory stays bounded by the certificate and automaton sizes, and a
  declared vertex count must be covered by automaton states before the quiver
  is allocated. It produces `VerifiedCompletion`, which has no public
  constructor elsewhere (`verify`).
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
  Berlekamp's algorithm. A base-field root does not suffice: when the residue
  field is a proper extension `F_{p^d}`, as for `End(W ⊕ W)` with
  `End(W) = F_{p^d}`, a drawn element has a base-field eigenvalue with
  probability `O(p^(1-d))`, and the two irreducible factors that do split it
  can share a degree. The suite missed the defect because the decomposition
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
