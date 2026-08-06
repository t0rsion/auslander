# auslander-py

Python bindings for the `auslander` crate: finite-dimensional basic algebras
kQ/I over a checked prime field, where I is an admissible ideal given by
forbidden words or by general relations, and finite-dimensional right
modules. Paths compose left to right; arrow matrices act on row vectors.

The surface is small and algebra-owned: `PrimeField`, `Quiver`, `Algebra`
(plus named constructors such as `linear_an`, `kronecker`, `dual_numbers`,
`linear_nakayama`; `MonomialAlgebra` is an alias of the same class, kept from
v0.2), and modules built only through `algebra.module(...)` / `simple` /
`projective` / `injective`. The lower-level machinery behind the decision
APIs (endomorphism algebras with their exact radicals, opposite algebras, the
k-dual, element matrices) stays Rust-only; Python sees its results through
the methods below.

Two kinds of algebra share the class. `Algebra(quiver, forbidden)` and the
named constructors build a monomial algebra from forbidden words: lists of
arrow ids, each of length >= 2 and composable left to right. A monomial
presentation is field-independent, so one object serves every prime; a field
enters only when building modules, and each field gets one verified runtime
algebra, built on first use and cached.
`Algebra.from_relations(quiver, relations, field)` builds a general-relation
algebra: `relations` is a list of relations, each a list of
`(coefficient, path)` terms, where a path is a list of arrow ids and
coefficients are integers reduced mod p. The terms of one relation must share
one source and one target (uniformity), and a coefficient that reduces to
zero is rejected, not dropped. A general ideal is not field-independent: its
dimension and structure constants depend on the field, so the algebra is
bound to the one field it was verified over, `algebra.field` names it (`None`
for a monomial algebra), and any other field raises `ValueError`.

Construction runs noncommutative completion and then verifies the emitted
certificate independently before the algebra exists, so `dim` and the Cartan
matrix are exact. Rejected input raises `ValueError`: a malformed relation,
or an infinite-dimensional quotient whose message carries a cyclic word
witness. An exhausted completion budget raises `TruncationError`, a
`RuntimeError` carrying `basis_len`, `pending_ambiguities`, `steps_used` and
`reason` as attributes; the keywords `max_basis`, `max_word_len` and
`max_steps` of `from_relations` set the budgets.

Certificates: `algebra.certificate_json()` returns the canonical JSON bytes
of the verified completion certificate, and
`Algebra.from_certificate(json)` verifies untrusted bytes from scratch and
rebuilds the algebra from the verified data alone; tampered bytes raise
`ValueError` with the verifier's message. A monomial algebra is field-free
and a certificate is not, so a monomial algebra requires the `field`
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
of `Morphism` objects (a basis, not every morphism; arbitrary morphisms are
linear combinations of it), and `M.morphism(N, maps)` builds one checked
morphism from integer matrices, validating every commuting square. A
`Morphism` exposes `maps` (its vertex matrices as canonical integers in
`0..p`, in the same list-of-rows shapes `algebra.module` accepts) and
`is_isomorphism()`.

Homological invariants (`hom_dim`, `ext_dim`, `ext_table`, `resolve`, `pd`,
`global_dimension`) report partial results explicitly. A `Resolution` exposes
`terms`, `maps` and `augmentation` (the projective cover `P_0 -> M`, also
available directly as `M.projective_cover()`), in the shape dual to
`InjectiveCoresolution`. It carries an immutable `ResolutionStatus` whose
`kind` is `ResolutionKind.FINITE` (with `at` `None`) or `ResolutionKind.CUT`
(with `at` the number of computed differentials, the next syzygy nonzero).
Dimensions that may exceed a bound come back as `Bounded` with exactly one of
`exact` / `at_least` set. There is no "None means infinite" anywhere.

Isomorphism and decomposition: `M.is_isomorphic(N)` returns a frozen
`IsoResult` whose `isomorphic` is `True` (with a `witness` Morphism verified
to have a two-sided inverse), `False` (with a proof-shaped `obstruction`
string and a stable `obstruction_kind` tag), or `None` (undetermined, with a
`reason` string); Unknown is never conflated with No. `M.decompose()` returns
a `Decomposition` whose `summands` are ordinary `Module` objects over the
same algebra object, together with `inclusions` / `projections` Morphisms
(the split identities were verified at construction) and per-summand
`certificates`, each a frozen `Certificate` of kind `"indecomposable"`
(exact: the endomorphism algebra is local) or `"undetermined"` (nothing
claimed; `attempts` counts the exhausted split attempts).
`M.krull_schmidt()` returns a frozen `KrullSchmidtResult` with exactly one of
`classes` (a list of `(representative Module, multiplicity)` pairs, unique as
a multiset by Krull-Schmidt) and `reason` set. The module-level
`nakayama_indecomposables(algebra, field)` lists every indecomposable of a
Nakayama algebra as `(Module, Certificate)` pairs (the uniserial quotients
`P_i / rad^l P_i`, so the count is `dim_k A`, the sum of the Kupisch series;
every certificate is `"indecomposable"`) and raises `ValueError` on a
non-Nakayama quiver.

The AR translate: `M.tau()` returns τM as a `Module`, or `None` when τM = 0,
which happens exactly when M is projective. That `None` is a definite
mathematical answer (the translate is the zero module), not a partiality
convention. The "no None" rule above bans `None` as a stand-in for *unknown
or infinite*; this `None` encodes a proven zero, so no separate `TauZero`
sentinel exists. `tau` always runs two independent routes (Nakayama kernel
and transpose-then-dual) and cross-checks them. A certified disagreement
raises `RuntimeError`, a library-bug signal distinct from the `ValueError`
used for input errors. A cross-check the isomorphism test could not decide
either way raises `TauAgreementUnknown`, a limit of that test rather than
evidence that the routes differ.

Injectives: `M.injective_envelope()` returns the pair `(I(M), M -> I(M))`,
`M.coresolve(steps)` a minimal `InjectiveCoresolution` with `terms`, `maps`,
`coaugmentation` and the same `ResolutionStatus` a projective resolution
reports, and `M.injective_dimension(bound)` a `Bounded` whose
`AtLeast(bound + 1)` is a genuine lower bound because the coresolution is
minimal.

Dynkin and Euclidean diagrams: `dynkin_type(quiver)` and
`euclidean_type(quiver)` recognize the underlying graph and return a frozen
`DynkinType` / `EuclideanType`, or `None` when the graph is not of that shape
(a definite answer about the graph, not partiality). Both are built as
`DynkinType(DiagramFamily.A, 3)`, `EuclideanType(DiagramFamily.E6)`, and
reject out-of-range parameters at construction, so `num_vertices` and
`indecomposable_count` (Dynkin only) are total. `dynkin_quiver` /
`euclidean_quiver` materialize the diagram as a `Quiver`, which indexes its
vertices by u32; a diagram beyond that limit raises `ValueError`.
`generalized_cartan_matrix(quiver)` and `positive_roots(quiver)`
are the integer data of the graph. `dynkin_indecomposables(algebra, field)`
lists every indecomposable of a hereditary path algebra of Dynkin type as
`(Module, Certificate)` pairs, one per positive root, built by reflection
functors rather than enumerated over the field; it raises
`NonzeroIdealError` (attribute `forbidden_words`) when the algebra is a proper
quotient of kQ and `NotDynkinError` (attribute `euclidean`, the
`EuclideanType` when the graph has one) otherwise. Both subclass
`DynkinError`, itself a `ValueError`, so the rejected precondition is the
exception class rather than a message to parse.

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
