# Roadmap

Releases ship when their gates hold. A gate is a checkable condition: a
test suite, a certificate, an oracle comparison. This file does not
promise dates.

## Public v0.9: reusable catalogs

The [release checklist](docs/releasing.md) defines the current gates.
Catalog Ext tables share source resolutions. Fixed-dimension queries enumerate
catalog multiplicities and retain typed cuts. Portable artifacts replay the
catalog, full enumeration or cut prefix, and generic Ext cells.

The release adds checked gentle-tree catalogs, Python catalog and higher
orthogonality APIs, per-algebra session fields, and explicit verification
states. The teaching notebook and research example execute the same public
API. Whole-workflow benchmarks report setup and replay costs alongside query
costs.

General string-algebra catalogs, bands, characteristic zero, and extension
fields remain outside this release. The sections below record the preceding
subsystems and their original scope.

## Certified general bound quiver algebras

One theme: every operation the crate offers works over a general
admissible ideal, not only a monomial one. The enabling machinery is a
noncommutative completion engine inside this crate. The release is the
capability, not the engine.

### Substrate

- One runtime algebra type, `Algebra`, which owns its prime field. Dimension
  and structure constants of a non-monomial quotient depend on the field, so
  a field-free runtime algebra is no longer sound.
- `MonomialPresentation` stays field-free and carries the field-independent
  combinatorics: forbidden-word analysis, dimension, Cartan data for monomial
  ideals. It is an input and analysis type, not a runtime algebra.
- `MonomialAlgebra` is removed. A migration guide covers the rename. Monomial
  input runs through the same completion pipeline; completion adds no new
  relations there, and the certificate is small.
- Multiplication returns algebra elements (coefficient vectors over the
  normal-word basis), never "one path or zero".

### Completion engine

- Plain Bergman-style completion: a fixed degree-lexicographic order over a
  fixed arrow order, full remainder division, overlap and inclusion
  compositions. No F5-style optimization in this release.
- Deterministic: identical ordered input and configuration produce identical
  certificate bytes, verified across separate processes and operating
  systems.
- Resource limits are enforced inside reduction and ambiguity processing.
  Exhaustion returns a typed `Truncated` outcome that carries progress
  diagnostics and unlocks nothing.

### Certification

- Completion emits a serializable, versioned certificate: the completed
  basis, two-sided transformation identities for every basis element (output
  contained in the input ideal), zero-remainder division traces for every
  input relation (input ideal contained in the output), the full overlap and
  inclusion ambiguity inventory with reduction traces in strict order
  descent, the normal-word automaton, and the finiteness witness.
- An independent verifier checks the certificate from untrusted bytes. It
  shares no completion, ambiguity enumeration, or reduction code with the
  engine. It re-enumerates every ambiguity itself.
- `Algebra` is constructible only from a `VerifiedCompletion` produced by
  the verifier. There is no unchecked constructor. Even the engine's own
  output passes the verifier first.
- Infinite dimension is a typed construction error that carries the complete
  certificate and a cyclic normal-word witness. No infinite-dimensional
  algebra value exists.
- A tamper corpus (modified coefficients, missing ambiguities, wrong
  contexts, non-descending reductions, false automaton edges, false
  finiteness claims) must be rejected by the verifier.

### Downstream acceptance

Every existing high-level operation is tested over at least one genuinely
non-monomial quotient: opposite algebra and duality, `ElementMatrix`,
`EndoAlgebra`, projectives and injectives, resolutions and coresolutions,
Ext dimensions, radical and socle series, `decompose` and `krull_schmidt`,
`is_isomorphic`, and both `tau` routes. The full preceding suite must pass
unchanged through the new substrate.

The enumerators keep their existing domains. Dynkin enumeration stays on the
zero ideal; Nakayama enumeration keeps its preconditions. Widening them is
outside this scope.

### Oracle

QPA oracle schema v5, one schema bump: an explicit prime field per fixture,
coefficient-bearing relations, an admissible-order identifier, decomposition
multiplicities, fixture family identifiers, presentation identity separate
from ideal identity, GAP and QPA version provenance, and typed outcomes.
Fixtures include the commutative square, preprojective A_3, crafted
self-overlap and inclusion ambiguities, an admissible inhomogeneous
presentation, redundant and permuted presentations of one ideal, and a
characteristic-sensitive family. Groebner certificates stay out of the QPA
schema; golden certificate artifacts are committed beside it.

### Python

The bindings expose the same decision surface over non-monomial quotients:
general-relation construction, decomposition, isomorphism, tau, resolutions
and coresolutions, Ext dimensions. `EndoAlgebra` and `ElementMatrix` stay
Rust-only. The release ships one non-monomial example in both languages, a
migration guide, and a capability matrix.

### Outside this scope

Ext representatives and Yoneda products, the category radical, almost-split
sequences, AR component exploration, chain complexes and Hochschild
cohomology, tilting and tau-tilting, module Groebner resolution backends,
user-defined orders, one-sided Groebner bases, infinite-dimensional
quotients, string and gentle enumeration, characteristic zero.

## Witnessed Auslander-Reiten layer

One theme: the homological layer moves from dimensions to objects with
checkable witnesses. Ext classes, actual extensions, the distinguished AR
class, almost-split sequences, irreducible morphisms, valued AR quivers.
The binding specification is `docs/witnessed-ar-layer.md`.

- `HomSpace` with subspaces, quotients, deterministic complements, and
  coordinates; `IndecomposableModule` tied to its End-locality proof.
- `ExtSpace` and `ExtClass` with recheckable representative data; Yoneda
  products through stored chain lifts, composed with `then`.
- Checked `ShortExactSequence`; construction from an Ext^1 class; class
  recovery; split witnesses; non-split dual-vector inconsistency
  witnesses.
- Stable Hom, the AR socle construction, and `AlmostSplitSequence`
  constructible only through an explicit witness: the AR-duality route or
  the exhaustive-catalog factorization route.
- Category radical, typed exhaustive catalogs (Nakayama and zero-ideal
  Dynkin only), catalog-exact rad^2, and valued AR quivers that state
  dimensions over both residue fields instead of overclaiming plain
  multiplicities.
- Gates: product laws tested exhaustively on bounded fixture degrees; a
  mutation corpus rejecting tampered witnesses; fresh-process determinism
  with golden AR-quiver snapshots; QPA oracle schema v6 frozen only after
  a capability spike; the acceptance matrix split between the general
  tier and the catalog tier.

## Support tau-tilting

One theme: enumeration stops being a list and becomes a certificate.
Candidate verification is general; a completeness claim requires a closed
mutation graph. The binding specification is `docs/support-tau-tilting.md`.

- `TauRigidModule` and `TauRigidityOutcome`, witnessed both ways. A vanishing
  claim stores no witness data, because it has none to store: private
  construction is the proof token and verification recomputes.
- `SupportTauTiltingPair` and `AlmostCompletePair`. The projective part is
  forced, not searched: with `r` summands and support size `s`, a pair exists
  exactly when `r = s`, and then `P` is the support complement.
- Minimal left add-approximations with minimality witnesses, and
  multiplicities counted over the residue division ring `End(N_i)/rad`, not
  over the base field.
- Left mutation with `MutationWitness`, and `FacWitness` for a slot with no
  left mutation.
- The closed mutation graph. `ClosedSupportTauTiltingGraph` exists only past
  `ClosureWitness::verify()`; a failure is a defect, not an outcome. A
  truncated walk is typed `Incomplete` and unlocks nothing.
- Completeness rests on AIR Theorem 2.18 and Theorem 2.35(b), over an
  arbitrary field. It needs neither an algebraically closed base field nor
  residue division rings equal to the base field, and it needs neither
  connectivity nor n-regularity.
- Gates: budgets charged by size and not by call, so a tau-tilting infinite
  walk truncates; hand-derived pair counts for the semisimple cube, A_2, A_3,
  D_4 and truncated Kronecker; a QPA oracle at schema v7; fresh-process
  determinism.

## Checked higher homology

One theme: every higher homological claim factors through a checked finite
complex. The binding specification is `docs/checked-higher-homology.md`.

- `CheckedComplex` validates display-order endpoints and zero composites.
  Exactness returns `ExactComplex` or the first `NonExactWitness`, with exact
  homology dimensions at every vertex.
- Relative normalized bar Hochschild cohomology under four explicit ceilings.
  A cut stores only degrees whose outgoing differential, square check, and
  quotient bases finished.
- Classical tilting at any finite projective dimension reached by the caller's
  bound. Success stores the exact complex `A -> T^0 -> ... -> T^n` and one
  `add(T)` witness per generated term. A positive self-extension and a bounded
  construction blocker remain distinct outcomes.
- One private verification context per top-level closure recheck. It memoizes
  certified primitive computations on exact nominal operands and never
  memoizes a witness verdict.
- Rust and Python expose the same outcomes. GAP with QPA schema v8 checks the
  designated projective-dimension-one and projective-dimension-two tilting
  candidates.
- Gates: independent full-bar, center, and derivation checks; fresh-process
  bases and cut diagnostics; F2 and F5 tilting fixtures; a live QPA run; and a
  production code count below the preceding baseline.

## Certified derived-equivalence workbench

One workflow: build, replace, discover, transport, export, and verify. A
classical tilting certificate reaches its split target first. Ordinary bounded
complexes and tilting-complex mutation build on that checked foundation. The
binding specification is `docs/derived-equivalence-workbench.md`.

- Recover `End_A(T)^op` as a deterministic bound quiver presentation when
  every tilting summand has residue degree one. A non-split target is a typed
  unsupported outcome.
- Verify the target through a separate algebra-isomorphism checker. The
  checker recomputes the split, arrow corners, relation images, normal-word
  images, and every basis product.
- Build bounded graded self-Ext algebras from the existing Ext classes and
  product witnesses. A cut keeps exact degrees and never treats an absent
  degree as zero.
- Add bounded homological complexes, chain maps, shifts, direct sums, cones,
  homotopies, and Hom modulo null-homotopy.
- Certify the Rickard tilting-complex conditions. Strict transport realizes
  the equivalence between bounded `add(T)` complexes and bounded projective
  target complexes, with checked round trips.
- Gates: target and derived-certificate mutation corpora, fresh-process
  determinism, F2 and F5 fixtures, a live QPA comparison where QPA exposes the
  needed invariants, Python parity, and a fixed target-work ceiling.

- Replace an ordinary bounded complex by a checked bounded projective model.
  A quasi-isomorphism exists only after its mapping cone passes exactness.
- Compute derived Hom from stored projective models. Extend the classical strict
  equivalence through checked projective and `add(T)` replacements.
- Certify exceptional tilting complexes through finite shifted Hom checks and
  a recursive mutation witness back to the regular generator.
- Mutate tilting complexes through checked homotopy-category approximations.
  A budgeted graph retains complete edges but claims closure only with a
  separate closure witness.
- Recover and verify `End_K(T)^op`, then form checked paths of forward and
  formal inverse derived-equivalence edges.
- Export canonical `auslander-derived-v1` mutation-recipe artifacts. A
  standalone verifier that runs no graph discovery replays the recipe from
  the original algebra certificate.
- Ship a command-line verifier and a Python workbench with a session, text
  input, canonical JSON computation, stable-category batches, sparse module
  data, rich displays, type stubs, persistence, and optional adapters.
- Gates: mutation corpora, fresh-process artifacts and renderings,
  F2 and F5 fixtures, the live schema-v9 QPA regression, exact work
  ceilings, package tests, and the full workbench release matrix.

## Later

Non-split species, extension fields, characteristic zero, dg target algebras,
and `A-infinity` minimal models remain separate releases. Each needs the same
witness discipline before it enters a release.

## sylvester

`sylvester` is a separate crate and stays one. This crate never depends on
it: the commutative engine and the noncommutative engine solve different
problems, and the projects share testing and certification lessons only.

Its own track: the repaired tree stays frozen while certified algebra work is built. A
certification sprint (per-run two-sided transformation identities,
zero-remainder input certificates, a public certificate verifier, the two
recorded resource-exhaustion defects) happens only alongside a real
manuscript effort, and publication happens only with the paper. Without
that commitment it remains an unpublished archive.
