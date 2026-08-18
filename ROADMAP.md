# Roadmap

Releases ship when their gates hold, not when a calendar says so. A gate is
a checkable condition: a test suite, a certificate, an oracle comparison.
This file states the gates. It does not promise dates.

## v0.3: certified general bound quiver algebras

One theme, end to end: every operation the crate offers works over a general
admissible ideal, not only a monomial one. The enabling machinery is a new
noncommutative completion engine inside this crate, but the release is the
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
`is_isomorphic`, and both `tau` routes. The full v0.2 suite must pass
unchanged through the new substrate.

The enumerators keep their existing domains. Dynkin enumeration stays on the
zero ideal; Nakayama enumeration keeps its preconditions. Widening them is
not a v0.3 goal.

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
Rust-only. The release ships one end-to-end non-monomial example in both
languages, a migration guide, and a capability matrix.

### Cut from v0.3

Ext representatives and Yoneda products, the category radical, almost-split
sequences, AR component exploration, chain complexes and Hochschild
cohomology, tilting and tau-tilting, module Groebner resolution backends,
user-defined orders, one-sided Groebner bases, infinite-dimensional
quotients, string and gentle enumeration, characteristic zero.

## v0.4: the Auslander-Reiten layer, witnessed

One theme, end to end: the homological layer moves from dimensions to
objects with checkable witnesses. Ext classes, actual extensions, the
distinguished AR class, almost-split sequences, irreducible morphisms,
valued AR quivers. The binding specification is `docs/v0.4-design.md`.

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
  a capability spike; the acceptance matrix split honestly between the
  general tier and the catalog tier.

## v0.5: support tau-tilting, witnessed

One theme, end to end: enumeration stops being a list and becomes a
certificate. Candidate verification is general; a completeness claim requires
a closed mutation graph. The binding specification is `docs/v0.5-design.md`.

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

## v0.6 and later

- v0.6: checked chain complexes and bar Hochschild cohomology with a real
  budget model. Classical tilting returns there, since the generation axiom
  for `n` above one needs a checked exact complex `0 -> A -> T^0 -> ... ->
  T^n -> 0`.
- Later: derived equivalence certificates, Ext algebras, A-infinity
  minimal models, each only with the same witness discipline.

## sylvester

`sylvester` is a separate crate and stays one. This crate never depends on
it: the commutative engine and the noncommutative engine solve different
problems, and the projects share testing and certification lessons only.

Its own track: the repaired tree stays frozen while v0.3 is built. A
certification sprint (per-run two-sided transformation identities,
zero-remainder input certificates, a public certificate verifier, the two
recorded resource-exhaustion defects) happens only alongside a real
manuscript effort, and publication happens only with the paper. Without
that commitment it remains an unpublished archive.
