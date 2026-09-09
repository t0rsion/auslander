# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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

- The two unreleased local development lines now form one public v0.7. The
  classical tilting example remains available as `classical_tilting`; `v07`
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
