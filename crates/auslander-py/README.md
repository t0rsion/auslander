# auslander-py

Python bindings for the `auslander` crate: finite-dimensional basic algebras
kQ/I over a checked prime field, where I is an admissible ideal given by
forbidden words or by general relations, and finite-dimensional right
modules. Paths compose left to right; arrow matrices act on row vectors.

The surface is small and algebra-owned: `PrimeField`, `Quiver`, and `Algebra`,
plus named constructors such as `linear_an`, `kronecker`, `dual_numbers`, and
`linear_nakayama`. `MonomialAlgebra` is an alias of the same class, kept from
v0.2. Modules come only through `algebra.module(...)`, `simple`, `projective`,
and `injective`. The lower-level machinery behind the decision APIs
(endomorphism algebras with their exact radicals, opposite algebras, the
k-dual, element matrices) stays Rust-only. Python sees its results through
the methods below.

Two kinds of algebra share the class. `Algebra(quiver, forbidden)` and the
named constructors build a monomial algebra from forbidden words: lists of
arrow ids, each of length >= 2 and composable left to right. A monomial
presentation is field-independent, so one object serves every prime. A field
enters only when building modules, and each field gets one verified runtime
algebra, built on first use and cached.

`Algebra.from_relations(quiver, relations, field)` builds a general-relation
algebra. `relations` is a list of relations, each a list of
`(coefficient, path)` terms, where a path is a list of arrow ids and
coefficients are integers reduced mod p. The terms of one relation must share
one source and one target (uniformity), and a coefficient that reduces to
zero is rejected, not dropped. A general ideal is not field-independent: its
dimension and structure constants depend on the field. The algebra is
therefore bound to the one field it was verified over, `algebra.field` names
that field (`None` for a monomial algebra), and any other field raises
`ValueError`.

Construction runs noncommutative completion and then verifies the emitted
certificate independently before the algebra exists, so `dim` and the Cartan
matrix are exact. Rejected input raises `ValueError`: a malformed relation,
or an infinite-dimensional quotient whose message carries a cyclic word
witness. An exhausted completion budget raises `TruncationError`, which
carries `basis_len`, `pending_ambiguities`, `steps_used`, and `reason` as
attributes. The keywords `max_basis`, `max_word_len`, `max_steps`,
`max_origin_terms`, and `max_ambiguities` of `from_relations` set the budgets,
one per value `reason` can take. Since v0.4 `TruncationError` subclasses
`BudgetExhaustedError`, the base of every budget exhaustion, which itself
subclasses `RuntimeError`. The class stays a `RuntimeError`, so existing
`except` clauses keep working.

Certificates: `algebra.certificate_json()` returns the canonical JSON bytes
of the verified completion certificate, and
`Algebra.from_certificate(json)` verifies untrusted bytes from scratch and
rebuilds the algebra from the verified data alone. Tampered bytes raise
`ValueError` with the verifier's message. A monomial algebra is field-free
and a certificate is not, so a monomial algebra must pass the `field`
argument; the reloaded algebra is always field-bound. Certificate bytes
never carry budgets: `from_certificate` takes the same optional budget
keywords as `from_relations` to set the rebuilt algebra's downstream
limits, and `algebra.completion_limits` reports the effective limits as a
dict.

An end-to-end non-monomial example, the commutative square with the relation
ab - cd (dim 9 over every prime; mirrored by `test_readme_example` in
`tests/test_v03.py`):

```python
import auslander

F = auslander.PrimeField(5)
# a: 0 -> 1, b: 1 -> 3, c: 0 -> 2, d: 2 -> 3
Q = auslander.Quiver(4, [(0, 1), (1, 3), (0, 2), (2, 3)])
A = auslander.Algebra.from_relations(Q, [[(1, [0, 1]), (-1, [2, 3])]], F)
assert A.dim == 9

# Minimal projective resolution 0 -> P_3 -> P_1 + P_2 -> P_0 -> S_0 -> 0.
res = A.simple(F, 0).resolve(5)
assert res.terms_dims == [[1, 1, 1, 1], [0, 1, 1, 2], [0, 0, 0, 1]]
assert res.pd(5).exact == 2

# Decompose P_0 + S_1 + S_1, built block diagonally.
M = A.module(F, [1, 3, 1, 1], [[[1, 0, 0]], [[1], [0], [0]], [[1]], [[1]]])
classes = {tuple(rep.dims): mult for rep, mult in M.krull_schmidt().classes}
assert classes == {(1, 1, 1, 1): 1, (0, 1, 0, 0): 2}

# The AR translate of a non-projective simple.
assert A.simple(F, 1).tau().dims == [0, 0, 1, 1]

# Dump, verify, reload.
B = auslander.Algebra.from_certificate(A.certificate_json())
assert B.dim == 9
```

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

Isomorphism and decomposition: `M.is_isomorphic(N)` returns a frozen
`IsoResult`. Its `isomorphic` is `True` (with a `witness` Morphism verified
to have a two-sided inverse), `False` (with a proof-shaped `obstruction`
string and a stable `obstruction_kind` tag), or `None` (undetermined, with a
`reason` string). Unknown is never conflated with No.

`M.decompose()` returns a `Decomposition`, and `len(decomposition)` is its
summand count. Its `summands` are ordinary
`Module` objects over the same algebra object, together with `inclusions` and
`projections` Morphisms (the split identities were verified at construction)
and per-summand `certificates`. Each certificate is a frozen `Certificate` of
kind `"indecomposable"` (exact: the endomorphism algebra is local) or
`"undetermined"` (nothing claimed; `attempts` counts the exhausted split
attempts). `M.krull_schmidt()` returns a frozen `KrullSchmidtResult` with
exactly one of `classes` (a list of `(representative Module, multiplicity)`
pairs, unique as a multiset by Krull-Schmidt) and `reason` set.

The module-level `nakayama_indecomposables(algebra, field)` lists every
indecomposable of a Nakayama algebra as `(Module, Certificate)` pairs. These
are the uniserial quotients `P_i / rad^l P_i`, so the count is `dim_k A`, the
sum of the Kupisch series, and every certificate is `"indecomposable"`. A
non-Nakayama quiver raises `ValueError`.

The AR translate: `M.tau()` returns τM as a `Module`, and a projective M gives
the zero module. It never returns `None`: the zero module is the answer, and it
carries its algebra and its dimension vector. `tau` always runs two independent
routes (Nakayama kernel and transpose-then-dual) and cross-checks them. A
certified disagreement raises `DefectError`, a `RuntimeError` subclass and a
library-bug signal distinct from the `ValueError` used for input errors. A
cross-check the isomorphism test could not decide either way raises
`TauAgreementUnknown`, a limit of that test rather than evidence that the
routes differ.

Injectives: `M.injective_envelope()` returns the pair `(I(M), M -> I(M))`.
`M.coresolve(steps)` returns a minimal `InjectiveCoresolution` with `terms`,
`maps`, `coaugmentation`, and the same `ResolutionStatus` a projective
resolution reports. `M.injective_dimension(bound)` returns a `Bounded` whose
`AtLeast(bound + 1)` is a genuine lower bound, because the coresolution is
minimal.

Ext spaces: `M.ext_space(N, k)` returns an `ExtSpace` with the data
`ext_dim` throws away. It has `dim` (equal to `M.ext_dim(N, k)`), `source`,
`target`, `degree`, a `basis()` of `ExtClass` objects, `zero_class()`,
`class_from_coordinates(coords)`, and `identity_class()` on a degree-0
self-space, which is the Yoneda unit. Degree 0 is not special-cased:
`Ext^0(M, N)` is `Hom(M, N)`.

An `ExtClass` exposes `source`, `target`, `degree`, `coordinates` (over the
space's basis), `is_zero`, `representative()` (a cocycle `P_k -> N` as a
`Morphism`), `+`, unary `-`, multiplication by an integer scalar on either
side, `then(other)`, and `extension()` in degree 1. `then` is the Yoneda
product `Ext^m(M, N) x Ext^n(N, L) -> Ext^{m+n}(M, L)`, in the endpoint order
of morphism composition. Classes combine and compare only inside one space,
which means the same source object, the same target object, and equal
degrees. Incompatible operands raise `IncompatibleSpacesError`, a
`ValueError` subclass. Comparison raises it too rather than answering
`False`, which would claim the two classes differ.

Extensions: `ExtClass.extension()` returns the `ShortExactSequence`
`0 -> target -> middle -> source -> 0` realizing a degree-1 class, and the
zero class gives the split sequence. The sequence exposes `sub`, `middle`,
`quotient`, `inclusion`, `projection`, and `ext1_class()`, which recovers the
class in a freshly built `Ext^1(quotient, sub)`; the round trip returns the
coordinates it started from. Exactness was checked per vertex at
construction, so holding the object is proof. `is_split` decides splitting by
solving the retraction system, and `split_status` carries the proof either
way: a `SplitWitness` with `retraction` and `section`, or a
`NonSplitWitness` whose `dual` vector proves the retraction system unsolvable
by multiplication alone. `verify()` rechecks exactness and the witness.

Almost-split sequences: `M.almost_split()` returns an `AlmostSplitSequence`
`0 -> start -> middle -> end -> 0` with `start` the AR translate of `end = M`,
or the member `AlmostSplitOutcome.PROJECTIVE` when M is projective. That
member is an outcome, not a failure and not `None`; the returned object is the
member itself, so `is` decides the case. The module first passes the
indecomposability gate. The zero module, a decomposable module, and a module
the gate could not decide raise `NotIndecomposableError`, a `ValueError`
subclass carrying `kind` ("zero", "decomposable", or "undetermined"),
`summands`, and `attempts`.

The sequence exposes `inclusion`, `projection`, `ext1_class()` (the chosen AR
class, deterministic and not canonical), `witness_route`, `verify()`, and
`verification_summary()`. `witness_route` is `"ar_duality"` for every sequence
this package builds; the catalog route stays Rust-only. `verify()` rechecks
every gate against freshly recomputed data. `verification_summary()` reports
the gates one by one as a dict with the keys `action_traces`,
`socle_membership`, `duality_dimensions`, `socle_dimension`, `non_split`, and
`sequence_exact`. A failed internal cross-check raises `DefectError`, a
`RuntimeError` subclass: it reports a bug in this library, never bad input.

The module category and its AR quiver: `M.category_radical(N)` returns the
radical `rad(M, N)` as an object with `dim` and a `basis()` of `Morphism`
objects. Both endpoints must pass the indecomposability gate, so both can
raise `NotIndecomposableError`.

`algebra.ar_quiver(field)` builds the valued Auslander-Reiten quiver, and
`len(quiver)` is its vertex count. `vertices()` gives `ArVertex` objects with
`id`, `module`, `residue_degree`, `projective`, and `injective`. `arrows()`
gives `ArArrow` objects with `source`, `target`, `base_field_dim`,
`dim_over_source_residue`, `dim_over_target_residue`, and `representatives()`.
`plain_multiplicity` is the arrow multiplicity of an unvalued AR quiver. It
raises `ValuedArrowError` when a residue degree exceeds 1, where the three
dimensions differ and no single integer is the multiplicity. The quiver is
complete for its domain: it comes from a classification theorem (Nakayama or
Gabriel) and no budget cuts it short, so there is no partial AR quiver. Any
other algebra raises `UnsupportedDomainError` naming both failed routes. A
monomial presentation is field-free, so it needs the `field` argument; a
general-relation algebra carries its own. Both calls validate their endpoints
before running, so a failed hom or hom-space computation inside them is a
defect and raises `DefectError`, not `ValueError`.

An end-to-end AR example over k[x]/(x^3) (mirrored by `test_readme_ar_example`
in `tests/test_v04.py`):

```python
import auslander

F = auslander.PrimeField(5)
A = auslander.Algebra.truncated_poly(3)
S = A.simple(F, 0)
assert S.ext_space(S, 1).dim == 1

# The almost-split sequence 0 -> S -> P/rad^2 -> S -> 0.
sequence = S.almost_split()
print(sequence.start.dims, sequence.middle.dims, sequence.end.dims)
assert sequence.middle.dims == [2]
assert sequence.witness_route == "ar_duality"
assert sequence.verify()
assert all(sequence.verification_summary().values())

# Three indecomposables, four arrows, every arrow plain.
quiver = A.ar_quiver(F)
assert len(quiver.vertices()) == 3
assert [a.plain_multiplicity for a in quiver.arrows()] == [1, 1, 1, 1]
```

Dynkin and Euclidean diagrams: `dynkin_type(quiver)` and
`euclidean_type(quiver)` recognize the underlying graph and return a frozen
`DynkinType` or `EuclideanType`, or `None` when the graph is not of that
shape. That `None` is a definite answer about the graph, not partiality. Both
types are built as `DynkinType(DiagramFamily.A, 3)` or
`EuclideanType(DiagramFamily.E6)`, and both reject out-of-range parameters at
construction, so `num_vertices` and `indecomposable_count` (Dynkin only) are
total. `dynkin_quiver` and `euclidean_quiver` materialize the diagram as a
`Quiver`, which indexes its vertices by u32; a diagram beyond that limit
raises `ValueError`. `generalized_cartan_matrix(quiver)` and
`positive_roots(quiver)` are the integer data of the graph.

`dynkin_indecomposables(algebra, field)` lists every indecomposable of a
hereditary path algebra of Dynkin type as `(Module, Certificate)` pairs, one
per positive root, built by reflection functors rather than enumerated over
the field. A proper quotient of kQ raises `NonzeroIdealError` (attribute
`forbidden_words`); any other non-Dynkin case raises `NotDynkinError`
(attribute `euclidean`, the `EuclideanType` when the graph has one). Both
subclass `DynkinError`, itself a `ValueError`, so the rejected precondition is
the exception class rather than a message to parse.

Tau-rigidity: `M.tau_rigidity()` returns a `TauRigidity`, witnessed either
way. `is_tau_rigid` `True` comes with `vanishing`, a `TauRigidModule` holding
`summands`, `translates` (the zero module where the summand is projective), and
`vanishing_pairs`, the ordered summand positions whose `Hom(X_i, tau X_j)` was
checked zero. A vanishing claim has no element to exhibit, so nothing beyond
those positions is stored. `False` comes with `morphism`, one nonzero
`X_i -> tau X_j`, and `summand_pair`, the positions it runs between. Neither
branch raises, because each is an answer rather than a failure. The decision
runs summandwise, which is exact by additivity of tau and Hom. `verify()`
recomputes every translate through the certified double route and rebuilds
every Hom space.

Support tau-tilting pairs: `SupportTauTiltingPair.classify(algebra, modules,
vertices, field=None)` classifies the candidate `(M, P)`, where M is the direct
sum of `modules` and P is the projective support `vertices`. The four
conditions are: the two parts share an algebra and are basic; `Hom(P, M) = 0`;
M is tau-rigid; and `|M| + |P| = n`. `is_pair` `True` sets `module_summands`,
`projective_support`, `is_tau_tilting`, and `summand_count`. `False` sets
`rejection`, a `PairRejection` with `condition()` (1 to 4) and `kind`.
Condition 3 also carries `witness`, the nonzero morphism `X_i -> tau X_j`.
Condition 2 carries `hom_from_projective`, the vertex and `dim M_v` that
refute the proposed `P_v`, and condition 4 carries `summand_counts`. A failed
condition is an answer, so it never raises.
`AlmostCompletePair.classify` is the same against `|M| + |P| = n - 1`.
`verify()` recomputes every condition of a pair against the live parts. On a
rejection it rebuilds the Hom space of condition 3's morphism and rechecks
condition 4's counts; conditions 1 and 2 store nothing to recheck and report
`True`.

Mutation: `pair.mutate_at(slot)` returns a `Mutation` or a `FacWitness`. A
`Mutation` has `slot`, `target` (the pair it lands on), `shape`
(`"moves_to_projective"` with `exchanged_vertex`, or `"replaced_by_module"`
with `multiplicity`), and `verify()`. A `FacWitness` proves that `X_j` lies in
`Fac(M/X_j)`, so the slot admits no left mutation at all; it carries `module`,
`summand`, the `maps` `U -> X_j` whose images were summed, `image_dims`, and
`verify()`. The family is not claimed to span `Hom(U, X_j)`, which is stronger
than the definition of `Fac`. That is a statement about the slot, not a
failure.

The mutation graph: `algebra.support_tau_tilting_graph(field=None,
limits=None)` walks the support tau-tilting quiver from `(A, 0)` under left
mutation and returns one of two classes.

A walk whose frontier empties returns a `ClosedSupportTauTiltingGraph` with
`pairs()`, `mutations()`, `histogram()` (pair counts by `|M|`), `work_units()`,
`verify()`, and `len()`. Every slot of every vertex carries a verified left
mutation landing inside the vertex set or a certified `FacWitness`, and a
finite set with that property is every basic support tau-tilting pair up to
isomorphism of pairs (Adachi, Iyama, and Reiten, Theorem 2.35(b) applied to a
finite left-closed set). The walk runs that recheck itself before the object
exists, so `pairs()` never reads a list the certificate rejects; `verify()`
reruns it, and a walk whose recheck fails raises instead of returning a
graph.

A walk that runs out of budget or hits a step it cannot certify returns an
`IncompleteSupportTauTiltingGraph` with `vertices_found`,
`verified_mutations`, `reason` (`"budget_exhausted"` or
`"certification_blocked"`), `diagnostics`, `work_units()`, and
`verify_parts()`. It has no `pairs()` accessor at all. Neither stop raises:
both are values on that class. A truncated set is a biased sample, not a nearly
complete list. Over the Kronecker algebra the walk descends the preprojective
ray and reaches no preinjective vertex.

`MutationGraphLimits(*, max_vertices=None, max_directed_mutations=None,
max_work_units=None, max_matrix_entries=None)` sets the budgets, each omitted
keyword keeping its default. There is no wall-clock limit: a time limit would
make the outcome depend on the machine, and the walk is deterministic across
processes and platforms. Work units are charged by call and by module size,
never by time, and a closed graph never reports more of them than
`max_work_units` allows. `max_matrix_entries` gates one Hom system per slot,
the `Fac` test, and not the largest system the walk allocates.

Catalog enumeration: `algebra.enumerate_over_catalog(field=None)` lists every
support tau-tilting pair from the definition, over an exhaustive catalog of the
indecomposables. It returns a `CatalogEnumeration` with `pairs()`,
`provenance`, `catalog_len`, `nodes_visited`, `histogram()`, `verify()`, and
`len()`. Completeness comes from the catalog's classification theorem and from
nothing else, so the route runs on catalog domains only: Gabriel's theorem for
a path algebra of Dynkin type, the Nakayama classification for a Nakayama
algebra. Any other algebra raises `UnsupportedDomainError`. The route is
independent of the mutation-graph certificate, using no mutation, no
approximation, and no theorem about the support tau-tilting quiver, so agreement
between the two lists is evidence rather than a restatement.

Blocked certification: `CertificationBlockedError`, a `RuntimeError` subclass,
reports a step the crate could not certify, which is an undetermined split, an
undetermined indecomposability gate, or an undecided isomorphism test inside
the tau cross-check. It is not budget exhaustion and raising a limit does not
help. A mutation walk reports the same condition as a value instead.

An end-to-end example over linearly oriented A_2 (mirrored by
`test_a_two_support_tau_tilting_quiver_is_the_pentagon` in
`tests/test_tilting.py`):

```python
import auslander

F = auslander.PrimeField(5)
A = auslander.Algebra.linear_an(2)

graph = A.support_tau_tilting_graph(F)
assert isinstance(graph, auslander.ClosedSupportTauTiltingGraph)
assert len(graph) == 5  # the pentagon
assert graph.histogram() == [1, 2, 2]
assert graph.verify()

# The independent catalog route agrees.
assert len(A.enumerate_over_catalog(F)) == 5

# A budget stops the tau-tilting infinite Kronecker algebra, and the result
# has no pairs() accessor to misread as a complete list.
limits = auslander.MutationGraphLimits(max_vertices=6)
partial = auslander.Algebra.kronecker(2).support_tau_tilting_graph(F, limits=limits)
assert partial.reason == "budget_exhausted"
assert not hasattr(partial, "pairs")
assert partial.diagnostics.limit == "max_vertices"
```

Threads and interrupts: every computation that can run long releases the GIL
while it runs, so other Python threads keep running instead of freezing until
the call returns. A Ctrl-C during such a call still takes effect only when the
call returns, because the library has no cancellation point inside a
computation. Two threads may build the same algebra over one field at the same
time; one result is kept and the other dropped, so a field keeps one runtime
algebra and modules from both threads still interact.

## Building

Requires Rust (MSRV 1.88; development is pinned to Rust 1.92 via
`rust-toolchain.toml`), Python >= 3.10, and [maturin](https://www.maturin.rs/):

```sh
cd crates/auslander-py

# Development install into the active virtualenv:
maturin develop --release

# Or build a wheel (abi3, works on any CPython >= 3.10):
maturin build --release
pip install target/wheels/auslander-*.whl
```

## Testing

```sh
python -m pytest tests
```
