# Algebra and homological computations

[Package README](../README.md) | [Python workbench](workbench.md) | [Checkpoints and theorem artifacts](checkpoints.md) | [Compute requests](compute.md) | [Representation theory](representation-theory.md)

## Algebra objects and certificates

The surface is algebra-owned: `PrimeField`, `Quiver`, and `Algebra`,
plus named constructors such as `linear_an`, `kronecker`, `dual_numbers`, and
`linear_nakayama`. Modules come only through `algebra.module(...)`, `simple`,
`projective`, and `injective`. The lower-level machinery behind the decision
APIs (endomorphism algebras with their exact radicals, opposite algebras, the
k-dual, element matrices) stays Rust-only.

Two kinds of algebra share the class. `Algebra(quiver, forbidden)` and the
named constructors build a monomial algebra from forbidden words: lists of
arrow ids, each of length >= 2 and composable left to right. A monomial
presentation is field-independent. By default, a monomial constructor returns
a field-free algebra. Pass `field=F` at construction or call `algebra.over(F)`
to bind it. Field-sensitive operations on a field-free algebra require a field;
a bound algebra may omit it. Each field gets one verified runtime algebra,
built on first use and cached.

`Algebra.from_relations(quiver, relations, field)` builds a general-relation
algebra. `relations` is a list of relations, each a list of
`(coefficient, path)` terms, where a path is a list of arrow ids and
coefficients are integers reduced mod p. The terms of one relation must share
one source and one target (uniformity), and a coefficient that reduces to
zero is rejected, not dropped. A general ideal is not field-independent: its
dimension and structure constants depend on the field. The algebra is
therefore bound to the one field it was verified over, `algebra.field` names
that field (`None` for a field-free monomial algebra), and any other field raises
`ValueError`.

Construction runs noncommutative completion and then typed verification of
the emitted certificate. An `Algebra` exists only after that verification
accepts a completion certificate, so `dim` and the Cartan matrix are exact.
Rejected input raises `ValueError`: a malformed relation, or an
infinite-dimensional quotient whose message carries a cyclic word witness.
An exhausted completion budget raises `TruncationError`, which carries
`basis_len`, `pending_ambiguities`, `steps_used`, and `reason` as attributes.
The keywords `max_basis`, `max_word_len`, `max_steps`, `max_origin_terms`,
and `max_ambiguities` of `from_relations` set the budgets, one per value
`reason` can take. `TruncationError` subclasses `BudgetExhaustedError`, the
base of every budget exhaustion, which itself subclasses `RuntimeError`. The
class stays a `RuntimeError`, so existing `except` clauses keep working.

Certificates: `algebra.certificate_json(field=None)` returns the canonical JSON
text of the verified completion certificate, and
`Algebra.from_certificate(json, *, field=None)` verifies untrusted bytes from
scratch and rebuilds the algebra from the verified data alone. Tampered bytes
raise `ValueError` with the verifier's message. A field-free monomial algebra
needs `field=F` for either operation; a bound algebra may omit it. The
reloaded algebra is always field-bound. Certificate bytes never carry budgets:
`from_certificate` takes the same optional budget keywords as `from_relations`
to set the rebuilt algebra's downstream limits, and
`algebra.completion_limits` reports the effective limits as a dict.

## Commutative square example

The commutative square with the relation ab - cd has dimension 9 over every
prime:

```python
import auslander

F = auslander.PrimeField(5)
# a: 0 -> 1, b: 1 -> 3, c: 0 -> 2, d: 2 -> 3
Q = auslander.Quiver(4, [(0, 1), (1, 3), (0, 2), (2, 3)])
A = auslander.Algebra.from_relations(Q, [[(1, [0, 1]), (-1, [2, 3])]], F)
assert A.dim == 9

# Minimal projective resolution 0 -> P_3 -> P_1 + P_2 -> P_0 -> S_0 -> 0.
res = A.simple(0).resolve(5)
assert res.terms_dims == [[1, 1, 1, 1], [0, 1, 1, 2], [0, 0, 0, 1]]
assert res.pd(5).exact == 2

# Decompose P_0 + S_1 + S_1, built block diagonally.
M = A.module([1, 3, 1, 1], [[[1, 0, 0]], [[1], [0], [0]], [[1]], [[1]]])
classes = {tuple(rep.dims): mult for rep, mult in M.krull_schmidt().classes}
assert classes == {(1, 1, 1, 1): 1, (0, 1, 0, 0): 2}

# The AR translate of a non-projective simple.
assert A.simple(1).tau().dims == [0, 0, 1, 1]

# Dump, verify, reload.
B = auslander.Algebra.from_certificate(A.certificate_json())
assert B.dim == 9
```

## Morphisms and invariants

Morphisms: `M.hom(N)` returns a basis of the hom space `Hom_A(M, N)` as a list
of `Morphism` objects. It is a basis, not every morphism; arbitrary morphisms
are its linear combinations. `M.morphism(N, maps)` builds one checked morphism
from integer matrices and validates every commuting square. A `Morphism`
exposes `source` and `target`, its two modules; `maps`, its vertex matrices as
canonical integers in `0..p` in the same list-of-rows shapes `algebra.module`
accepts; `map_at(v)`, the matrix at one vertex, where `maps` rebuilds all of
them; `is_zero`; `is_isomorphism()`; and `then(other)`, the composite "first
self, then other". Composition needs the target of `self` to be the source
object of `other` and raises `ValueError` otherwise.

Homological invariants (`hom_dim`, `ext_dim`, `ext_table`, `resolve`, `pd`,
`global_dimension`) report partial results explicitly. A `Resolution` exposes
`terms`, `maps`, and `augmentation` (the projective cover `P_0 -> M`, also
available directly as `M.projective_cover()`), in the shape dual to
`InjectiveCoresolution`. It carries an immutable `ResolutionStatus` whose
`kind` is `ResolutionKind.FINITE` (with `at` set to `None`) or
`ResolutionKind.CUT` (with `at` the number of computed differentials, the next
syzygy nonzero). Dimensions that may exceed a bound come back as `Bounded`
with exactly one of `exact` and `at_least` set. There is no "None means
infinite" anywhere. The typed results that compare by value hash by value too,
so `ResolutionStatus`, `Bounded`, `DynkinType`, `EuclideanType`,
`ResolutionKind`, `DiagramFamily`, and `AlmostSplitOutcome` all work as dict
keys and set elements.

Checked complexes: `CheckedComplex(terms, maps)` stores a nonempty finite
complex in display order. Construction checks each nominal endpoint and each
consecutive composite. `homology_dimensions(index)` returns the exact
dimension vector at one term. `exactness()` returns an `ExactComplex`, or a
`NonExactWitness` with the first nonzero homology dimension vector. Both
outcomes have `verify()`.

## Hochschild cohomology

Hochschild cohomology:
`algebra.hochschild_cohomology(max_degree, limits, field=None)` runs the
relative normalized bar construction. A field-free monomial algebra needs
`field=F`; a bound algebra may omit it. `BarLimits` requires four independent
ceilings:
tensor tuples at one degree, cochain dimension at one degree, retained matrix
entries plus scratch, and cumulative deterministic work. A finished request
returns `HochschildCohomology`. Its `degree(n)` returns a
`HochschildDegree` with deterministic cocycle, coboundary, and complement
bases. `class_from_coordinates` builds a `HochschildClass`, and `evaluate`
takes a vertex integer in degree zero or a list of normal-word basis indices
in positive degree.

A resource cut returns `IncompleteHochschildCohomology`, not an exception.
It exposes only `completed_degrees`, `reason`, `diagnostics`, and `verify()`.
It has no `degree` or `requested_degree` accessor. The diagnostics record the
first rejected reservation, including `stage`, `used`, `proposed`, and
`ceiling`. Raising that ceiling can expose a later limit.

## Classical tilting and derived transport

Classical tilting:
`ClassicalTiltingModule.classify(module, TiltingLimits(pd, generation))`
returns `ClassicalTiltingResult`. Exactly one of `tilting`, `rejection`, and
`blocker` is set. `is_tilting` is `True`, `False`, or `None` in that order.
A positive self-extension is the only negative outcome. A projective-dimension
cut or blocked bounded generation route leaves the question open and keeps its
checked blocker. A successful certificate exposes its complete resolution,
zero positive self-Ext spaces, exact generation complex, and `add(T)`
witnesses.

The path over `A = kA_3/(ab)` and `k[x]/(x^3)`:

```python
F = auslander.PrimeField(5)
A = auslander.Algebra.an_with_relations(3, [(0, 2)]).over(F)
S0 = A.simple(0)
resolution = S0.resolve(2)
exact = auslander.CheckedComplex(
    [resolution.terms[2], resolution.terms[1], resolution.terms[0], S0],
    [resolution.maps[1], resolution.maps[0], resolution.augmentation],
).exactness()
assert isinstance(exact, auslander.ExactComplex)
assert exact.verify()

bar_limits = auslander.BarLimits(10_000, 100_000, 10_000_000, 1_000_000_000)
X3 = auslander.Algebra.truncated_poly(3).over(F)
HH = X3.hochschild_cohomology(2, bar_limits)
assert HH.dimensions == [3, 2, 2]
assert HH.verify()

# D(A) = I_0 + I_1 + I_2 in block-diagonal bases.
DA = A.module([2, 2, 1], [[[0, 0], [1, 0]], [[0], [1]]])
answer = auslander.ClassicalTiltingModule.classify(
    DA, auslander.TiltingLimits(4, 5)
)
assert answer.is_tilting is True
assert answer.tilting.projective_dimension == 2
assert [term.dims for term in answer.tilting.generation_complex.complex.terms] == [
    [1, 2, 2],
    [1, 3, 2],
    [1, 1, 0],
    [1, 0, 0],
]
assert answer.verify()
```

Target algebras and derived transport:
`tilting.target_presentation(TargetLimits())` recovers `End_A(T)^op`.
A complete run returns `TargetPresentation`. A resource cut returns
`IncompleteTargetPresentation`, with the first rejected reservation. The
`UnsupportedTarget` outcome states the non-split boundary. It is unreachable
for a certified tilting module over the supported prime fields.

`module.ext_algebra(bound)` returns `ExtAlgebra` when the resolution ends,
or `IncompleteExtAlgebra` when the next syzygy is nonzero. Both store exact
grades and Yoneda product tensors through the bound.

`BoundedComplex`, `ChainMap`, `ChainHomotopy`, and `HomotopyHom` provide
integer homological degrees, shifts, direct sums, cones, and Hom modulo
null-homotopy. `DerivedEquivalenceCertificate` checks the tilting resolution,
graded self-Hom vanishing, the degree-zero target identification, generation,
and strict transport.

This projective-dimension-two example transports a nontrivial two-term
complex. Each source term carries an `add(T)` witness. The inverse accepts
only checked projective target terms.

```python
F = auslander.PrimeField(5)
A = auslander.Algebra.an_with_relations(3, [(0, 2)]).over(F)
DA = A.module([2, 2, 1], [[[0, 0], [1, 0]], [[0], [1]]])
tilting = auslander.ClassicalTiltingModule.classify(
    DA, auslander.TiltingLimits(4, 8)
).tilting
target = tilting.target_presentation(auslander.TargetLimits())
certificate = auslander.DerivedEquivalenceCertificate(tilting, target)
assert certificate.verify()

differential = next(
    map_
    for map_ in DA.hom(DA)
    if not map_.is_zero and not map_.is_isomorphism()
)
complex_ = auslander.BoundedComplex(0, [DA, DA], [differential])
witnesses = [tilting.add_closure_witness(term) for term in complex_.terms]
source = auslander.AddTComplex(complex_, witnesses)
transported = certificate.transport.forward(source)

source_dims = [
    complex_.hom(complex_, degree).quotient().dim for degree in range(-2, 3)
]
target_dims = [
    transported.complex.hom(transported.complex, degree).quotient().dim
    for degree in range(-2, 3)
]
assert source_dims == target_dims == [0, 3, 6, 3, 0]
assert certificate.transport.source_round_trip(source).verify()
assert certificate.transport.target_round_trip(transported).verify()
```
