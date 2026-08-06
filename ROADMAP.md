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
  descent, the irreducible-word automaton, and the finiteness witness.
- An independent verifier checks the certificate from untrusted bytes. It
  shares no completion, critical-pair enumeration, or reduction code with
  the engine. It re-enumerates every ambiguity itself.
- `Algebra` is constructible only from a `VerifiedCompletion` produced by
  the verifier. There is no unchecked constructor. Even the engine's own
  output passes the verifier first.
- Infinite dimension is a typed construction error that carries the complete
  certificate and a cyclic irreducible-word witness. No infinite-dimensional
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
Fixtures include the commutative diamond, preprojective A3, crafted
self-overlap and inclusion ambiguities, an admissible inhomogeneous
presentation, redundant and permuted presentations of one ideal, and a
characteristic-sensitive family. Gröbner certificates stay out of the QPA
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
cohomology, tilting and tau-tilting, module Gröbner resolution backends,
user-defined orders, one-sided Gröbner bases, infinite-dimensional
quotients, string and gentle enumeration, characteristic zero.

## v0.4 and later

- Ext representatives and Yoneda products; non-split extension construction.
- Category radical, irreducible morphisms, almost-split sequences with
  checkable criteria.
- Chain complexes and bar Hochschild cohomology.
- Tilting and tau-tilting after that.

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
