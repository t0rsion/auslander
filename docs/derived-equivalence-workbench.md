# Certified derived-equivalence workbench

This document fixes the certified derived-equivalence workbench. A deviation
needs a documented reason and a design update in the same change.

The workbench combines the classical and complex-tilting layers in one workflow.
The classical layer recovers and verifies the target of a tilting module. Its
strict transport accepts bounded `add(T)` complexes on the source and bounded
projective complexes on the target. The workbench adds checked replacement of
ordinary bounded inputs, tilting-complex mutation, portable equivalence
artifacts, stable-category batches, and canonical JSON computation. The
[classical tilting contract](classical-tilting-workbench.md) records the first
layer in detail.

The release has one workflow:

```text
build -> replace -> discover -> transport -> export -> verify
```

Every step returns a complete checked value, a typed cut, or a typed
rejection. No partial search result claims completeness.

## 1. Scope

In scope:

- Checked bounded complexes whose terms are projective modules.
- A bounded projective replacement built through projective objects in the
  category of bounded complexes.
- A quasi-isomorphism verified through the exact mapping cone.
- Derived Hom between inputs with a checked bounded projective source.
- Automatic use of the classical strict transport after the needed replacement
  and thick-generation steps verify.
- Tilting complexes in `K^b(proj A)`, with explicit self-orthogonality and
  thick-generation data.
- Left and right mutation through checked minimal approximations and mapping
  cones.
- A budgeted graph of certified tilting-complex mutations.
- Recovery and verification of `End_K(T)^op` for a split basic tilting
  complex.
- Composition and inversion of checked derived-equivalence edges.
- Canonical portable artifacts and a verifier that runs no discovery search.
- A local command-line program for inspection and verification.
- A Python package with a session, text presentation parser, shell, strict
  compute schema, type stubs, rich displays, persistence, and optional adapters.
- Cooperative cancellation and pollable progress for new workbench searches.
- Rust and Python parity for replacement, derived Hom, automatic classical
  transport, bounded discovery, and artifact verification outcomes and cuts.

Out of scope: unbounded derived categories, non-split species, extension
fields, characteristic zero, dg target algebras, minimal `A-infinity` models,
Python construction of arbitrary tilting-complex witnesses, and a completeness
claim for an unrestricted mutation graph. A bounded input whose replacement
does not finish stays a cut. It is not called non-perfect.

## 2. Mathematical domain

All modules remain finite-dimensional right modules over one verified
finite-dimensional basic algebra `A` over `F_p`. Complexes use homological
degrees and differentials

```text
d_n: X_n -> X_(n - 1).
```

The perfect category is `K^b(proj A)`. A bounded projective complex is already
a perfect model. An ordinary bounded complex enters this category only after
`PerfectReplacement` stores a bounded projective complex and a verified
quasi-isomorphism.

A tilting complex `T` satisfies:

```text
Hom_K(T, T[q]) = 0 for every q != 0,
thick(T) = K^b(proj A).
```

Only finitely many shifts can have a nonzero chain map between two bounded
complexes. Self-orthogonality therefore has a finite exact check.

The mutation construction follows Aihara and Iyama. The derived-equivalence
criterion follows Rickard. The implementation uses explicit approximations,
cones, and generation witnesses. It does not use either theorem as an
unchecked Boolean shortcut.

## 3. Projective complex witnesses

`ProjectiveComplex` stores:

- one checked `BoundedComplex`;
- one verified decomposition of each term into the canonical projectives
  `P_i = e_i A`;
- the matching inclusions and projections.

`ProjectiveComplex::new` rejects the first term without such a decomposition.
`verify()` recomputes every split and the bounded complex. A zero term has the
empty decomposition and is projective.

`ProjectiveComplex` supports shifts, direct sums, chain maps, homotopies, and
cones. Each result rebuilds its term decompositions. No constructor trusts
projectivity from a dimension vector.

## 4. Quasi-isomorphisms

`QuasiIsomorphism` stores one chain map and the exactness certificate of its
mapping cone. Its constructor computes the cone and accepts only an
`ExactComplex` conversion of that cone.

For a map

```text
q: P -> X,
```

exactness of `Cone(q)` proves that `q` is a quasi-isomorphism. `verify()`
rebuilds the cone and its homology dimensions. It does not trust a stored list
of zero dimensions.

`PerfectReplacement` stores `X`, a `ProjectiveComplex` `P`, and a
`QuasiIsomorphism` from `P` to `X`. It checks nominal source endpoints and the
target after explicit zero padding before the cone test.

Two replacements of one input may use different projective models. Derived
Hom compares their outputs through checked comparison maps. Pointer identity
is not used as a mathematical uniqueness claim.

## 5. Automatic perfect replacement

`replace_perfect(X, limits, control)` first accepts `X` itself when every term
is projective. Otherwise it builds a projective resolution in the abelian
category of bounded complexes.

Fix the input interval `[l, u]`. For each degree `n`, let `P_n -> X_n` be the
canonical projective cover. For `n > l`, the disk complex `D^n(P_n)` has
`P_n` in degrees `n` and `n - 1`, with identity differential. At the lowest
degree, use the sphere complex `S^l(P_l)`. The sum

```text
Q(X) = S^l(P_l) (+) (+)_(n > l) D^n(P_n)
```

is a projective object in the abelian category of complexes supported on
`[l, u]`. The maps from its summands give a degreewise surjective chain map
`Q(X) -> X`. The kernel remains on `[l, u]`.

Take its kernel as a bounded complex and repeat. This gives an exact sequence
in the complex category:

```text
... -> Q_2 -> Q_1 -> Q_0 -> X -> 0.
```

If one kernel is zero, totalize the finite double complex. For horizontal
resolution degree `r` and internal homological degree `n`, its term contributes
to total degree `n + r`. The horizontal differential carries sign `(-1)^n`.
The total differential is rebuilt and checked before a value exists.

The augmentation `Tot(Q) -> X` is checked as a chain map. Its cone must be
exact before `PerfectReplacement` is returned.

`ReplacementLimits` bounds:

```text
max_resolution_steps
max_complex_terms
max_total_dimension
max_matrix_entries
max_work_units
```

Every reservation uses checked arithmetic. `ReplacementOutcome` is:

- `Replaced(PerfectReplacement)`.
- `Cut(ReplacementCut)`.
- `Cancelled(ReplacementCancellation)`.

A cut stores the exact complex-resolution prefix, the first nonzero kernel,
the effective limits, and the first rejected reservation. It exposes no
projective replacement. A cancellation stores the same checked prefix and the
last completed stage. Neither outcome says that the input is not perfect.

The first acceptance fixtures include one-term modules of projective
dimensions zero, one, and two, a two-term complex, an exact complex with
nonprojective terms, and an infinite-resolution cut.

## 6. Derived Hom

`DerivedHom::compute(X, Y, limits, control)` replaces `X` by `P` and computes

```text
Hom_D(X, Y[q]) = Hom_K(P, Y[q]).
```

The finite support gives an exact degree interval. Each degree stores the
existing deterministic `HomotopyHomQuotient`. `DerivedHomClass` stores its
degree, coordinates, and representative chain map from `P`.

Composition first replaces the middle object through the stored comparison
data. The resulting chain maps compose in the existing left-to-right order.
Products return checked coordinates in the requested output space.

`DerivedHomOutcome` separates a complete value, a replacement cut, a work
cut, and cancellation. An absent degree outside the finite support is exact
zero. A degree omitted by a cut is not zero.

For modules in degree zero, acceptance tests compare the derived Hom
dimensions and products against `ExtSpace` and `ExtClass` through every degree
whose replacement completes.

## 7. Automatic equivalence transport

`DerivedTransport` extends `StrictTransport`. It keeps the strict path
as its fast path.

On the target side, an ordinary bounded complex first receives a bounded
projective replacement. The existing strict inverse then applies to that
projective model.

On the source side, the classical generation construction is rerun for each
projective term. Minimal left `add(T)` approximations give a finite exact
coresolution and a checked quasi-isomorphism to an `add(T)` complex.

A projective source complex is rebuilt through its brutal filtration. Each
new term attaches by its stored differential. The implementation solves the
strict chain-map comparison equation between the two `add(T)` models, then
takes its mapping cone. A homotopy-only comparison does not become a complex
differential.

An ordinary source complex therefore follows:

```text
X <- projective model P -> add(T) model U -> strict forward image.
```

Each comparison is stored. The first two arrows are checked
quasi-isomorphisms through exact cones. The final arrow uses the classical strict
transport.

`DerivedForwardTransport` and `DerivedReverseTransport` store the original
input, projective replacement, strict intermediate model, and output.
Verification rebuilds each stage. Acceptance tests compare the homology of a
forward and reverse round trip. This release does not store a general natural
unit, counit, or triangle-identity certificate for ordinary inputs.

The names `derived_hom` and `derived_tensor` describe the two directions of
the classical tilting equivalence. `derived_tensor` is the checked inverse
transport through projective target models. It is not a general tensor product
for arbitrary bimodules.

## 8. Tilting complexes

`TiltingComplexCandidate` stores an ordered list of nonzero
`ProjectiveComplex` summands over one algebra. Their direct sum is the candidate
`T`.

The release classifier has an exceptional domain. Each summand must have a
one-dimensional degree-zero endomorphism quotient. This proves locality over
the base field. A broader local endomorphism ring returns the typed
`EndomorphismLocality` blocker. It is not rejected as nonlocal.

Distinct summands must have no checked degree-zero homotopy isomorphism.
An open isomorphism gate blocks classification.

`TiltingComplexResult` is:

- `Tilting(CertifiedTiltingComplex)`.
- `NotTilting(TiltingComplexRejection)`.
- `Undetermined(TiltingComplexBlocker)`.

A nonzero class in `Hom_K(T, T[q])` for `q != 0` is a rejection and stores its
representative chain map. A failed generation search is undetermined unless a
separate invariant proves that generation is impossible.

`CertifiedTiltingComplex` stores every zero shifted Hom quotient, every
degree-zero endomorphism quotient, and one thick-generation witness.
`verify()` recomputes each part.

## 9. Thick-generation witnesses

`ThickGenerationWitness` has two exact forms:

- `Regular`, for the ordered canonical projectives in degree zero.
- `Mutation`, which stores a certified parent and one checked approximation
  cone.

The recursive mutation form proves that the parent and child generate the
same thick subcategory. A chain must end at `Regular`. The verifier rebuilds
each approximation and cone, then checks the child summand list.

This release does not accept an arbitrary user-supplied thick-expression
directed acyclic graph. Classical tilting generation stays in its existing
exact-complex certificate. Automatic classical transport uses that
certificate directly.

## 10. Tilting mutation

Let `T = X (+) U`, where `X` is one stored indecomposable summand. A left
mutation uses a minimal left `add(U)` approximation

```text
f: X -> E
```

in the homotopy category. Its candidate replacement is `Cone(f)`. A right
mutation uses the dual construction.

`ComplexApproximationWitness` stores the direction, replaced summand, ordered
summand indices, and assembled chain map. The verifier recomputes every
degree-zero homotopy Hom basis. One copy of each basis representative forms
the universal evaluation or coevaluation map. In the exceptional domain this
is the fixed minimal approximation.

The replacement is the checked cone, shifted by `-1` for right mutation. The
new ordered list must pass the same exceptional basicness, shifted Hom, and
generation checks.

Every silting mutation candidate is checked for tilting self-orthogonality.
If the negative shifts do not vanish, the result is a typed
`SiltingOnly` outcome. It is not inserted in the tilting graph.

## 11. Equivalence discovery

`discover_equivalences(A, limits, control)` starts at the regular projective
generator. It walks verified left and right tilting mutations in breadth-first
order. A vertex key contains canonical complex data and does not use an
address.

`DiscoveryLimits` bounds vertices, directed mutations, total complex terms,
matrix entries, per-vertex Hom spaces, and work units. No wall-clock limit
changes a mathematical outcome.

Discovery always returns `IncompleteEquivalenceGraph`. The stop reason is an
exhausted bounded frontier, a named resource limit, or cancellation. The
value exposes certified vertices, checked mutation edges, and complete blocked
attempts. It has no `equivalence_class()` accessor and makes no closure claim.

Target recovery is a separate operation on any stored certified vertex.
Fresh-process tests pin vertex keys, mutation order, target presentations, and
artifacts.

## 12. Tilting-complex target algebras

For a certified split basic tilting complex `T`, form

```text
E = End_K(T).
```

The deterministic basis comes from degree-zero homotopy Hom complements.
Composition uses representative chain maps followed by reduction to quotient
coordinates. The existing target recovery algorithm then applies to `E^op`.

`VerifiedComplexTargetPresentation` stores the complex summands, homotopy
endomorphism algebra, primitive idempotents, arrow classes, relations,
normal-word maps, inverse maps, completion certificate, and work counts.

Its verifier rebuilds the homotopy Hom spaces and every basis product. The
generic coordinate-target verifier independently checks the relation images,
completion certificate, inverse coordinate map, unit, and every opposite
product. A resource limit remains `Cut`.

The exceptional classifier fixes each diagonal residue field to the base
field. Complex target recovery therefore has no separate non-split outcome.

## 13. Equivalence edges and composition

`DerivedEquivalenceEdge` stores the certified tilting complex and its verified
target. Rickard's criterion supplies the equivalence claim after those
certificates pass.

`DerivedEquivalencePath` stores ordered forward or formal inverse uses of
edges. Two paths compose only when the middle completion certificates are
equal. `inverse()` reverses the order and each direction. Verification rechecks
every edge and middle algebra.

This path type is a theorem-backed certificate. It does not construct the
inverse tilting complex over the target, and it does not transport arbitrary
complexes along a nonclassical edge. Explicit automatic transport in this
release is the classical `DerivedTransport` from section 7.

## 14. Portable artifacts

`DerivedArtifact` has schema identifier `auslander-derived-v1`. Its canonical
JSON stores integers and arrays only. Field elements use canonical integers in
`0..p`.

The artifact stores:

- the source completion certificate;
- the ordered left or right mutation recipe from the regular generator;
- the target completion certificate;
- effective tilting and target limits;
- exact target-recovery work counts;
- one canonical fingerprint over every preceding field.

It stores no memory addresses, elapsed times, cache state, or Python names.
The recipe is the compressed witness. Expanded module, morphism, and
coordinate matrices are rebuilt during verification and are not duplicated in
the envelope. One artifact represents one edge, not a composed path.

`to_canonical_json()` is byte-exact. `from_json()` uses explicit container,
integer, string, and byte limits before allocation. Duplicate keys, unknown
keys, floats, escapes outside the accepted subset, and trailing content are
rejected.

## 15. Independent artifact verifier

`verify_derived_artifact(text, limits, control)` is standalone from the
producer. It parses untrusted bytes and returns `VerifiedDerivedArtifact` only
after every mathematical check passes.

The verifier shares checked arithmetic and construction routines with the
library. It runs no breadth-first discovery and trusts no stored tilting or
target verdict. It does replay each prescribed mutation and rerun target
recovery because the artifact stores a recipe instead of expanded matrices.
The coordinate-target verifier then checks the rebuilt target data.

It performs these steps:

1. Verify and rebuild the source algebra from its completion certificate.
2. Start from the regular projective generator.
3. Replay each prescribed left or right mutation.
4. Recheck the final tilting complex and its recursive generation witness.
5. Recover the target and verify its completion and coordinate algebra map.
6. Compare the target certificate and exact work counts byte for byte.
7. Recompute the canonical fingerprint.

A verifier cut is typed and unlocks no verified artifact. A parser rejection
names the JSON path and the violated limit or schema rule.

The mutation corpus resigns changes to the source certificate, mutation
recipe, target certificate, declared limits, and work counts. It also changes
the fingerprint without resigning. Every changed artifact fails.

The fingerprint is FNV-1a, 64 bit. It detects accidental changes and fixes a
canonical identifier. It is not a cryptographic signature or authentication
mechanism.

## 16. Command-line program

The Rust package ships an `auslander` binary with these commands:

```text
auslander inspect ARTIFACT
auslander verify ARTIFACT
auslander canonicalize ARTIFACT
auslander fingerprint ARTIFACT
```

`inspect` parses and prints declared metadata without asserting validity.
`verify` runs the independent verifier. `canonicalize` succeeds only after
verification and writes canonical JSON to standard output. `fingerprint`
prints the verified fingerprint.

All diagnostics go to standard error. Machine-readable output goes to
standard output. Exit status is zero only for a complete verified result.
No command reads the network.

The PyPI console entry uses the same program name for `repl` and `compute`.
The Rust artifact binary and the Python workbench are separate installation
targets. A machine-readable research request uses the Python package.

## 17. Python package layout

The wheel becomes a Python package:

```text
auslander/
    __init__.py
    __main__.py
    _core.abi3.so
    _core.pyi
    compute.py
    py.typed
    session.py
    display.py
    parser.py
```

`auslander.__init__` re-exports the supported `_core` surface and defines
`__version__`. Existing `import auslander` code keeps working.

The extension stays the source of every mathematical value. Pure Python code
parses text, manages names, formats checked values, and calls public extension
methods. It does not duplicate algebra or verification logic.

## 18. Session and text input

`Session` owns one default field, a name table, input recipes, completed
artifacts, and display settings. It does not replace nominal identity inside
the core. Reusing a session name returns the stored algebra value.

The text presentation language accepts:

```text
field 5
vertices 0 1 2
arrows a:0->1 b:1->2
relations a*b = 0
```

Coefficients are signed base-ten integers. Path multiplication follows the
crate's left-to-right convention. Every parsed value enters the existing
checked Python constructor. The parser does not normalize bad paths into zero.

`Session.save(path)` writes input recipes, names, display settings, and
canonical verified artifacts. `Session.load(path)` rebuilds each live value
through checked constructors. It never deserializes a Python object graph.

## 19. Interactive shell and display

`python -m auslander` and `auslander repl` start the same shell. If IPython is
installed, the command uses it. Otherwise it uses Python's standard interactive
console.

The shell preloads:

```text
session, F, algebra, module, show, explain, verify_file
```

`show(value)` returns a deterministic text rendering outside a notebook. In a
notebook it also provides bounded HTML or SVG for:

- quivers and algebra dimensions;
- module dimension vectors and arrow matrices;
- bounded complexes and resolutions;
- support tau-tilting and equivalence graphs;
- perfect replacements, derived Hom dimensions, automatic transport results,
  and verified artifact metadata.

Every rendering has an output-size limit. A cut prints the omitted count. No
renderer triggers a mathematical computation.

`explain(value)` reports the exact variant, completed obligations, first
unfinished obligation, effective limits, and next useful action. It does not
parse exception text.

## 20. Python types and adapters

The wheel ships `py.typed` and stubs for the workbench entry points and
outcomes. Older extension classes retain the broad `_CoreValue` fallback
where their full historical surface is not enumerated. Stubs do not replace
runtime tests.

Optional adapters have no required dependency:

- graph values expose `to_networkx()` and `to_dot()`.
- `to_latex()` returns a string and does not import a renderer.
- `matrix_from_sage()` and `matrix_to_sage()` live in the optional
  `auslander.sage` module.

Sage is an adapter, not the runtime object model. Every imported Sage matrix
is copied into canonical field elements and passes the checked constructor.

## 21. Research computation interface

`Module.syzygy` and `Module.cosyzygy` return the requested module with the
cover or envelope prefix that produced it. Degree zero returns the source and
needs no prefix. Each positive-degree result has a `verify()` method.

`StableHomSpace` stores a basis of maps through projectives and a deterministic
quotient basis. It exposes both dimensions, both bases, reduction modulo the
projective-factor subspace, and reconstruction from quotient coordinates.

`HomologicalBatch` takes one ordered module catalog, one maximum Ext degree,
and selected source-target pairs. The all-pairs constructor expands the full
square in row-major order. The batch shares one resolution per selected source
and one projective cover per selected target. Its work record counts
resolutions, target covers, Hom spaces, projective-factor spaces, and Ext
tables. Pair and Ext-cell limits reject the request before partial results can
look complete.

`Algebra.module_sparse` accepts one list of `(row, column, value)` triples per
arrow. It checks shapes, bounds, duplicate coordinates, and the relations.
`Module.maps` and `Module.sparse_maps` return reconstructible arrow data.
`Morphism.maps` and `Morphism.sparse_maps` do the same for vertex maps.

The Python command

```text
auslander compute REQUEST.json
```

accepts schema `auslander-compute-v1`. A request contains exactly `schema`,
`algebra`, `modules`, and `operations`. The algebra comes from checked text or
a verified completion certificate. With no path or with `-`, the command reads
standard input. `auslander --version` prints the installed package version. A
module uses dense `maps` or canonical
`sparse_maps`. Supported operations are `algebra_summary`, `hom`, `hom_dim`,
`stable_hom`, `stable_hom_dim`, `ext_table`, `tau`, `resolve`, `decompose`, and
`homological_batch`.

The result uses schema `auslander-compute-result-v1` and canonical JSON. Module
records contain dimensions and arrow matrices. Morphism records contain vertex
matrices. Decomposition records contain inclusions, projections, and split
idempotents. A resolution records `finite` or `cut`; a cut names its exact step
and projective-dimension lower bound. Duplicate fields, unknown fields, unknown
operations, nonfinite JSON constants, and unknown module names are rejected.

## 22. Progress and cancellation

`CancellationToken` is an atomic flag shared with one computation. Bounded
workbench loops check it before every charged work unit and before a large
allocation.

`ProgressSnapshot` contains a stage tag and deterministic completed and
reserved work counts. It contains no elapsed time. Python can poll it from
another thread while the computation releases the GIL.

Cancellation returns a typed cancellation value with the last completed
certificate stage. It is not budget exhaustion and does not claim that a
larger limit would help.

Existing algorithms gain cancellation only where their loops can preserve a
checked prefix. A call without `control` behaves exactly as before.

## 23. Acceptance fixtures

The release includes `F_2` and `F_5` fixtures for:

- identity replacement of a projective complex and automatic replacement of a
  projective-dimension-two module;
- a two-term ordinary complex;
- a periodic-resolution cut and cancellation before the first cover;
- derived Hom against direct Ext computations;
- automatic transport through the classical projective-dimension-two equivalence;
- the regular tilting complex;
- genuine left and right tilting-complex mutations that are not modules in one
  degree;
- target recovery from a multi-degree tilting complex;
- a two-edge formal composition and inverse;
- artifact round trips for left and right recipes;
- artifact mutations across every stored claim family;
- command-line verification in a fresh process;
- dense and sparse compute requests, batch work counts, and fresh-process JSON;
- session save and checked reload;
- fresh-process text, HTML, SVG, DOT, and LaTeX agreement.

Every pinned mathematical number has a derivation in its fixture. A fixture is
not accepted because it matches this library on a second call.

## 24. Determinism, performance, and size

Fresh processes must produce identical replacement complexes, derived Hom
bases, tilting keys, mutation order, target presentations, artifacts,
fingerprints, renderings, and compute results.

Performance records separate exact work counts from elapsed samples. CI gates
work counts for fixed replacement, derived Hom, mutation discovery, target
recovery, and artifact verification. It does not gate wall-clock time.
The measured release record is
[`derived-workbench-performance.md`](derived-workbench-performance.md).

The production code scanner fixes its ceiling after the final deletion
and duplicate-logic pass. Tests and generated stubs cannot offset Rust
production code. The production code-line test enforces the current ceiling
for `crates/auslander/src`.

## 25. Oracle boundary

The workbench keeps QPA oracle schema v9 unchanged. The live run still checks the
classical tilting targets and every earlier oracle fixture. The new
tilting-complex basis and mutation data have no stable QPA serialization in
this release, so they use direct mathematical cross-checks and fresh-process
tests instead.

The committed expected document still comes only from a live QPA run. It is
never generated from this library.

## 26. Release gates

The release requires:

1. The full Rust suite on 1.92 and the MSRV.
2. Strict clippy, formatting, and rustdoc.
3. The full Python suite from a release wheel and a fresh source distribution.
4. The live GAP with QPA differential run.
5. Independent mutation corpora for replacements, tilting data, targets, and
   artifacts.
6. Fresh-process determinism for every new canonical value.
7. Exact work ceilings and a recorded performance run.
8. The final deletion and duplicate-logic pass.
9. Direct cyclomatic complexity at most 10 for every Rust and Python callable.
10. The repository prose gate.
11. Extracted Rust package tests on the MSRV.
12. Command-line tests on Linux, macOS, and Windows CI shells.
13. One Rust example and one Python session that run the complete release path.

## 27. Implementation order

The archived implementation sequence is in
[workbench implementation order](derived-workbench-implementation-order.md).
