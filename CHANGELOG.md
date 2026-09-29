# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.10.0] - 2026-09-29

Version 0.10 adds certified derived classification. `classify_derived`
partitions a finite family of algebras over one prime field. Two members
share a class only through a replayable derived equivalence, and two classes
are separated only by a recomputed invariant. Every other pair is typed
`Unresolved`. The contract is
[`docs/derived-classification.md`](docs/derived-classification.md).

The committed atlas `derived-atlas-f2-n3.json` classifies the 88 connected
gentle algebras with at most 3 vertices over `F_2` into 40 classes with no
unresolved pair. With silting walks of 64 vertices,
`derived-atlas-f2-n4.json` classifies the 982 with at most 4 vertices into
143 classes with one unresolved pair. The 894 with exactly 4 vertices form
103 classes: 791 merges, 5252 separated class pairs, and one unresolved
pair of genus 2 whose complete gentle invariants agree.

### Added

- `DerivedInvariants` computes checked derived invariants of one algebra:
  the vertex count, the Cartan determinant, the invariant factors of `C`,
  `C + C^T`, and `C - C^T`, the pencil `det(xC + C^T)`, the
  Avella-Alaminos-Geiss function, the winding class, and bounded Hochschild
  dimensions. A limit gives a typed stop, and a presentation that is not
  gentle gives `NotApplicable`. Neither reading separates.
- `DerivedInequivalenceWitness` stores two algebras and one invariant with
  different values. `verify()` rebuilds both algebras and recomputes both
  values.
- `GentlePresentation` recognizes gentle presentations with loops, cycles,
  and multiple arrows, and computes permitted threads, the AAG function, and
  the genus. `connected_gentle_algebras(n, field)` enumerates one
  presentation per isomorphism class of connected gentle bound quiver, keyed
  by `GentleKey`.
- `GentlePresentation::complete_invariant` adds the winding class of the
  surface model to the AAG function: `planar` in genus 0, a gcd in genus 1,
  and `odd`, `even`, or an Arf value in higher genus. Two connected gentle
  algebras are derived equivalent exactly when their values are equal
  (Amiot, Plamondon, and Schroll, Theorem 5.4).
  [`docs/gentle-derived-invariant.md`](docs/gentle-derived-invariant.md)
  records the construction.
- `AlgebraIsomorphism` stores a vertex bijection and one arrow image per
  arrow. Its verifier checks five facts and needs no search.
- `classify_derived(family, limits, control)` computes the invariants,
  separates the members, and walks tilting mutations inside each group. A
  merge stores the mutation recipe, the `DerivedEquivalencePath` to the
  recovered target, and the isomorphism onto the matched member. An
  unresolved pair lists every walk that could have merged it, with its
  discovery stop.
- `CertifiedSiltingComplex` and `DiscoveryLimits::through_silting`. A walk
  can pass through silting complexes that are not tilting. Members 470 and
  724 of `connected_gentle_algebras(4, F_2)` stay open under a tilting walk
  and merge under a silting walk.
- `derived-atlas-v1` stores a classification as a portable artifact.
  `verify_derived_atlas_artifact` rebuilds every member, recomputes every
  reading and separation, and replays every merge. It runs no discovery.
- `auslander classify gentle --vertices N` classifies the connected gentle
  algebras with at most `N` vertices, prints one row per family, and with
  `--output` writes the verified atlas. `auslander inspect` and
  `auslander verify` print atlas summaries. Every command takes `--help`.
- `artifact::verify_artifact` reads the header of any portable value and
  runs the verifier of its kind. `auslander verify` and the browser page use
  it.
- The `auslander-wasm` crate compiles that verifier to WebAssembly with no
  imports. The static page in `web/` replays one artifact in the browser.
  `web/parity.mjs` checks it against `auslander verify` on the same bytes in
  CI. See [`docs/browser-verifier.md`](docs/browser-verifier.md).
- Python exposes `derived_invariants()`, `gentle()`, `complete_invariant()`,
  `connected_gentle_algebras`, `classify_derived` with `explain()`, and atlas
  export and replay through `to_artifact()`, `export()`, and
  `verify_derived_atlas`. Notebook display shows the class table,
  `to_latex` writes it as a LaTeX table, and `presentation_text` writes a
  member. The derived classification tour notebook runs these steps.

### Changed

- Every ceiling and work counter of a portable format is `u64` in the
  format and in the Rust type. A 32-bit verifier now reads default budgets.
  Portable bytes do not change.
- Tilting mutation reduces each cone to a checked minimal complex and uses
  minimal approximations modulo radical-factoring maps. The
  derived-equivalence schema is now `auslander-derived-v2`, and a v1
  artifact is rejected as obsolete.
- Discovery identifies vertices by summand shapes and a checked
  isomorphism, and checks cancellation before each work unit inside a
  mutation.
- A summand endomorphism ring is certified local through a checked residue
  map `End_K(T_i) → k`.
- Every artifact kind reads and writes through one shared portable JSON
  layer. Committed artifacts serialize to the same bytes.
- `ArtifactVerifyLimits` has four completion ceilings. A declared
  completion limit above its ceiling stops replay with `DeclaredLimit`.
  `ArtifactVerificationOutcome::Cut` is now `Stopped`.
- Walk vertices are `CertifiedSiltingComplex` values.
  `ThickGenerationWitness::Mutation::parent`,
  `IncompleteEquivalenceGraph::vertices()`, and `TiltingComplexKey::new`
  change type. `TiltingMutationOutcome` adds `Silting`.
- `DiscoveryLimits::max_work_units`, `DiscoveryStop::WorkLimit`, and the
  Python keyword `EquivalenceDiscoveryLimits(max_work_units=...)` are
  removed. `max_directed_mutations` bounds the same count.
- `GentleError::EmptyQuiver` no longer mentions trees.
- `auslander verify` prints the summary lines of `auslander inspect` after
  its first line. A usage error or an unreadable file exits with status 2.

### Limits

- A merge needs a certified tilting path. Equal complete gentle invariants
  imply derived equivalence by Amiot, Plamondon, and Schroll, but they never
  merge two classes.
- Matching uses gentle keys and equal certificates. A recovered target that
  matches neither is not compared by a general isomorphism search.
- The invariants of an algebra that is not gentle are necessary conditions
  only. An unresolved pair of such algebras can be derived equivalent or
  not.
- The flagship study covers connected gentle algebras over `F_2`. Extension
  fields and characteristic zero remain outside this release.
- An atlas walk record is a claim about discovery. Replay checks it against
  the merges but does not rerun the walk.
- The intersection pairing behind the winding class is derived in the
  construction note, not quoted from a paper. Its rank and antisymmetry
  checks run on every call.

## [0.9.0] - 2026-09-18

Version 0.9 adds reusable catalog computations and checked gentle-tree
classification. The [validation record](docs/release-v09-validation.md) states the checks.
The [migration guide](docs/migration-v09.md) covers breaking Python calls and
saved sessions.

### Added

- `CatalogAtlas` caches ordered Ext dimensions over a complete catalog and
  shares each source resolution across its target rows. Checked bilinear
  scores evaluate direct sums without materializing them.
- Fixed-dimension queries enumerate catalog multiplicity vectors. Complete
  results cover every solution of the dimension equation. Row and search
  limits return a typed Cut with its exact retained prefix.
- `catalog-atlas-v1` artifacts store the algebra certificate, field, catalog
  order, dimensions, degree bound, limits, status, and rows. Replay checks
  complete coverage or the recorded Cut prefix and recomputes generic Ext
  cells. Omitted and duplicate rows fail verification.
- Gentle-tree recognition checks the reduced monomial quadratic relations,
  gentle continuation conditions, and connected underlying simple tree.
  Enumeration retains one string from each inverse pair. Catalog consumers
  accept the resulting complete catalog.
- Catalog coordinates map supplied modules to multiplicities with checked
  isomorphisms. Undecided decomposition or matching remains typed Unknown;
  matching budgets return Cut.
- Python exposes catalogs, cached Ext queries, higher orthogonality, and
  portable atlas replay. The executed notebook and research example use a
  gentle tree over two prime fields and compare catalog queries with a raw
  census. Whole-workflow benchmarks include setup and verification costs.

### Changed

- Python module constructors take the vertex or module data first and an
  optional field last. Named algebra constructors accept a field, and
  `algebra.over(field)` binds a field while retaining the cached algebra.
- `auslander-session-v2` stores the field of each algebra and module recipe.
  Loading rejects v1 documents. Reusing a name with a different recipe fails.
- Explanations distinguish computation status from verification state.
  Replay verification preserves a Cut status. Portable dispatch validates
  the schema and kind before choosing a verifier.

### Limits

- Complete catalogs cover Nakayama, zero-ideal Dynkin, and gentle-tree
  algebras. General string algebras and bands remain outside this release.
- Atlas results cover the stored degree interval. Ext dimensions do not
  determine Yoneda products or imply vanishing in higher degrees.
- Replay shares library algorithms. GAP/QPA comparisons provide independent
  evidence for the tested fixtures. Named work ceilings do not bound every
  intermediate matrix allocation or wall-clock duration.

## [0.8.0] - 2026-09-10

Version 0.8 adds certified discovery, bounded research streams, and
theorem-backed compiled computations. The release contract is
[`docs/research-design.md`](docs/research-design.md).
Breaking Python changes are listed in
[`docs/migration-to-computation-workflows.md`](docs/migration-to-computation-workflows.md).

### Added

- `auslander-computation-v1` stores finite module censuses and homological
  self-pair streams as canonical JSON. A checkpoint records its exact prefix,
  work, cut reason, and fingerprint. A fresh process must replay the prefix
  before it can resume.
- `HomologicalSelfPairCheckpointStream` computes complete source chunks under
  separate live-source, pair, Ext-cell, source, and work ceilings. Python
  atomically replaces the checkpoint after each committed chunk.
- `CompiledModuleFamily` checks fixed-pattern specializations against compiled
  relation layouts. Its Hom plan reuses fixed equations without reusing an
  unproved row reduction across fibers.
- `InterfaceFamilyHomPlan` reduces a fixed-interior family to its interface
  equations. `InterfaceFamilyHereditaryPlan` also computes exact `Ext^1` ranks
  for finite-dimensional path algebras and returns zero above degree one.
- For each checked degree, `HomotopyBlockCache` retains the `(n - 1)^2`
  unchanged ordered Hom blocks after one tilting mutation. It rebuilds the
  changed row and column, and rechecks every endpoint before reuse.
- `auslander-theorem-v1` stores one finite self-Ext vanishing locus over a
  replay-verified complete checkpoint. Its verifier rebuilds the census,
  replays every stored row, and recomputes the locus through `ExtSpace::new`.
  That constructor is the crate's generic Ext path. The locus check can stop
  at the first mismatch.
- Python and `auslander theorem` build, inspect, write, and replay-verify
  self-Ext locus artifacts. Parser, checkpoint, representative, degree, and
  Ext-space ceilings remain caller owned.
- The `self_ext_workflow` example and its commutative-square artifacts cover the
  starter domain of dimension `[1,1,1,1]` over `F_2` and the flagship domain
  of dimension `[2,1,1,2]`. The starter has 16 raw tuples, 10 classes, and
  representative 9 vanishing in degrees 1 through 3. The flagship has 256 raw
  tuples, 58 accepted modules, and 12 representatives. Degree 1 vanishes at
  `[5,10,11]`. Degrees 1 through 3 vanish at `[5,10]`. Representative 11 has
  Ext dimensions `[5,0,1,0]` and is isomorphic to `P_0 + S_0 + S_3`. A finite
  hand count of accepted modules is `58 = 7^2 + 9`. Both are checked finite
  computations, not a classification theorem.
- The 2026-09-09 family record reports square specialization at dimensions 2,
  4, and 8 as 214.4 / 225.4, 326.2 / 345.6, and 883.4 / 945.8 ns/op
  (compiled / generic). Square Hom reports 2137.8 / 2144.6, 10523.6 / 9754.3,
  and 78268.8 / 73998.3 ns/op. A16 interface Hom modules report 49692.3 /
  96228.3, 101180.5 / 90068.1, and 286284.8 / 89865.2 ns/op at widths 2, 4,
  and 8. Compilation is not a universal speedup. The raw record is
  [`docs/compiled-family-performance.md`](docs/compiled-family-performance.md).

### Changed

- Homological stream payloads use `homological-self-pair-stream-v2` and record
  committed chunk sizes. Readers reject the old kind. Verify the embedded
  census, recompute its stream, and rebuild any enclosing theorem artifact.
- Release workflows configure non-publish `workflow_dispatch` rehearsal and
  hosted ARM and macOS architecture checks. Those jobs are GitHub-hosted
  runner configuration. They are not a local execution record.
- Python exposes one algebra class and one module dimension-vector property.
  Replace `MonomialAlgebra` with `Algebra`, and replace `module.dim_vector`
  with `module.dims`.
- Handwritten target-presentation modules moved from `src/target/` to
  `src/target_parts/`. Cargo build directories can now be removed by name
  without matching source files. The public `auslander::target` path is
  unchanged.
- Large implementation, test, oracle, and benchmark files are split by
  responsibility. Direct cyclomatic complexity 11 and above is rejected.

### Limits

- A raw census is exponential in its arrow-matrix coordinates. Completion
  proves coverage of that finite domain only.
- A self-Ext locus artifact covers one field, one dimension vector, and one
  positive degree interval. It is not a classification of the module category.
- Higher orthogonality is catalog-relative over an exhaustive
  `IndecomposableCatalog`. It is not a global d-cluster-tilting result.
- The hereditary interface formula requires a zero relation ideal. Other
  algebras use generic resolutions.
- FNV-1a fingerprints identify canonical bytes and detect changes. They are
  not cryptographic signatures.

## [0.7.0] - 2026-08-30

This release adds one checked workflow for homological and derived
computations. It starts from a bound quiver presentation, builds modules and
complexes, computes witnessed results, and exports deterministic receipts.

### Added

- `present_target` recovers `End_A(T)^op` as a deterministic bound quiver
  algebra. `TargetPresentationOutcome` separates a verified presentation, a
  non-split boundary, and a resource cut. Every cut retains the source,
  effective limits, and first rejected reservation. The non-split branch is
  unreachable for certified tilting modules over the supported prime fields.
- `VerifiedTargetPresentation` stores the primitive idempotents, arrow images,
  normal-word coordinate map, inverse map, completion certificate, and exact
  work counts. Its verifier rebuilds the target and checks every basis
  product. A mutation corpus changes each certificate block in turn.
- `ExtAlgebraOutcome` computes exact self-Ext grades and Yoneda tensors through
  one degree bound. A finite resolution gives `Complete`. A nonzero next
  syzygy gives `Cut`, with all stored grades and products still exact.
- `BoundedComplex`, `ChainMap`, `ChainHomotopy`, and `HomotopyHom` use integer
  homological degrees. They provide checked shifts, direct sums, cones, chain
  homotopies, and deterministic Hom quotients modulo null-homotopy.
- `StrictTransport` realizes `Hom_A(T, -)` on bounded `add(T)` complexes and
  its inverse on bounded projective target complexes. Both directions carry
  checked term models and chain round trips.
- `DerivedEquivalenceCertificate` checks the bounded projective resolution of
  `T`, its graded homotopy self-Hom groups, the degree-zero endomorphism
  algebra, the generation complex, and strict transport.
- `ProjectiveComplex` records a canonical projective decomposition at every
  term. `QuasiIsomorphism` accepts a chain map only after its mapping cone is
  exact. `replace_perfect` returns a checked projective replacement or a typed
  cut with the exact completed prefix.
- `derived_hom` computes finite-support
  `Hom_D(X, Y[q]) = Hom_K(P, Y[q])` from a checked source replacement. It
  stores quotient bases, representatives, products, exact work, and typed
  cuts. `DerivedTransport` extends classical transport to ordinary bounded
  complexes through checked replacements.
- `CertifiedTiltingComplex` checks exceptional projective-complex summands,
  all possible nonzero shifted Hom spaces, and a recursive generation witness.
  Left and right mutation use checked homotopy-category approximations and
  cones.
- `discover_equivalences` walks mutations in deterministic breadth-first
  order. An incomplete graph keeps verified vertices, edges, blockers, storage
  counts, and its typed stop reason. It makes no closure claim.
- `present_complex_target` recovers and verifies `End_K(T)^op`.
  `DerivedEquivalenceEdge` and `DerivedEquivalencePath` store checked Rickard
  edges, formal inverses, and compositions.
- `auslander-derived-v1` stores completion certificates, a mutation recipe,
  limits, target work, and a canonical fingerprint. The standalone Rust
  command inspects, verifies, canonicalizes, and fingerprints local artifacts.
- `syzygy` and `cosyzygy` return their maps and projective or injective
  witnesses. `StableHomSpace` stores a deterministic Hom basis, the subspace
  that factors through projectives, and quotient representatives.
- `HomologicalBatch` shares resolutions and coresolutions across ordered Ext,
  stable Hom, and translate queries. Its result records exact work and the
  stored resolutions used by later calls.
- Python accepts dense module maps or canonical sparse entries. It exposes
  module and morphism maps, stable Hom witnesses, syzygies, homological
  batches, target outcomes, derived Hom, transport, discovery, and artifact
  verification.
- `auslander compute` and `python -m auslander compute` accept the strict
  `auslander-compute-v1` JSON schema. Named modules feed algebra summaries,
  Hom, stable Hom, Ext tables, translates, resolutions, decompositions, and
  shared batches. Results use the reconstructible
  `auslander-compute-result-v1` schema. The command accepts a file or standard
  input, and `auslander --version` reports the installed version.
- The Python wheel includes a checked text parser, named sessions, recipe
  persistence, an IPython or standard Python shell, bounded notebook displays,
  DOT, NetworkX, LaTeX and Sage adapters, `py.typed`, and type stubs.
- Acceptance fixtures cover F_2 and F_5. Fresh-process tests cover Rust values,
  Python renderings, compute receipts, graph keys, and artifact bytes. CI gates
  exact work counts and direct cyclomatic complexity.

### Changed

- The classical tilting example remains available as `classical_tilting`; `v07`
  runs the complete workbench path.
- Production modules and tests were split at direct cyclomatic complexity 11.
  Touched functions stay at 10 or below. Shared construction, parsing,
  verification, and transport stages now use named helpers.
- The Python package version, Rust crates, artifact metadata, documentation,
  examples, and determinism labels now use 0.7.0.

### Limits

- Ordinary target quivers require split residue fields. Every certified
  tilting summand in the current prime-field domain is split. The typed
  `Unsupported` boundary remains, but species are not constructed.
- Strict transport requires an `add(T)` witness for each source term or a
  projective witness for each target term. It does not replace arbitrary
  bounded complex automatically. `DerivedTransport` performs replacement only
  on its supported classical route.
- Tilting-complex classification requires a one-dimensional diagonal
  endomorphism quotient for each summand. A broader local ring returns
  `EndomorphismLocality` as an open obligation.
- Nonclassical edges do not construct inverse tilting complexes or transport
  arbitrary complexes. Their certificates cover the stated Rickard edge.
- Artifacts store a mutation recipe, not expanded witness matrices or composed
  paths. Verification replays the checked mutation and target routines.
- The FNV-1a fingerprint is a deterministic identifier, not a cryptographic
  signature.
- Python exposes summaries and artifacts for tilting-complex discovery.
  Direct construction of arbitrary tilting-complex witnesses remains
  Rust-only.
- QPA oracle schema v9 checks earlier fixtures and classical tilting targets.
  It does not compare the new canonical tilting-complex bases.
- The release does not construct unbounded derived categories, non-split
  species, extension fields, characteristic-zero algebras, or `A-infinity`
  models.

Earlier releases are available in the [v0.6 and v0.5 additions archive](docs/changelog/v0.6-v0.5-added.md),
the [v0.5 continuation and v0.4 archive](docs/changelog/v0.5-continuation-v0.4.md), and the
[v0.3 through v0.1 archive](docs/changelog/v0.3-v0.1.md).
