# auslander-py

Python bindings for the `auslander` crate: finite-dimensional basic algebras
kQ/I over a checked prime field, where I is an admissible monomial ideal, and
finite-dimensional right modules. Paths compose left to right; arrow matrices
act on row vectors.

The surface is small and algebra-owned: `PrimeField`, `Quiver`,
`MonomialAlgebra` (plus named constructors such as `linear_an`, `kronecker`,
`dual_numbers`, `linear_nakayama`), and modules built only through
`algebra.module(...)` / `simple` / `projective` / `injective`. The lower-level
machinery behind the decision APIs (endomorphism algebras with their exact
radicals, opposite algebras, the k-dual, element matrices) stays Rust-only;
Python sees its results through the methods below.

Morphisms: `M.hom(N)` returns a basis of the hom space `Hom_A(M, N)` as a list
of `Morphism` objects (a basis, not every morphism; arbitrary morphisms are
linear combinations of it), and `M.morphism(N, maps)` builds one checked
morphism from integer matrices, validating every commuting square. A
`Morphism` exposes `maps` (its vertex matrices as canonical integers in
`0..p`, in the same list-of-rows shapes `algebra.module` accepts) and
`is_isomorphism()`.

Homological invariants (`hom_dim`, `ext_dim`, `ext_table`, `resolve`, `pd`,
`global_dimension`) report partial results explicitly: a `Resolution` exposes
`terms`, `maps` and `augmentation` (the projective cover `P_0 -> M`, also
available directly as `M.projective_cover()`), dual in shape to
`InjectiveCoresolution`, and carries an immutable `ResolutionStatus` whose
`kind` is `ResolutionKind.FINITE` (with `at` `None`) or `ResolutionKind.CUT`
(with `at` the number of computed differentials, the next syzygy being
nonzero). Dimensions that may exceed a bound come back as `Bounded` with
exactly one of `exact` / `at_least` set. There is no "None means infinite"
anywhere.

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
a multiset by Krull–Schmidt) and `reason` set. The module-level
`nakayama_indecomposables(algebra, field)` lists every indecomposable of a
Nakayama algebra as `(Module, Certificate)` pairs (the uniserial quotients
`P_i / rad^l P_i`, so the count is `dim_k A`, the sum of the Kupisch series;
every certificate is `"indecomposable"`) and raises `ValueError` on a
non-Nakayama quiver.

The AR translate: `M.tau()` returns τM as a `Module`, or `None` when τM = 0,
which happens exactly when M is projective. That `None` is a definite
mathematical answer (the translate is the zero module), not a partiality
convention. A dedicated `TauZero` sentinel was considered and rejected: the
"no None" rule above bans `None` as a stand-in for *unknown or infinite*, and
this `None` encodes a proven zero. `tau` always runs two independent routes
(Nakayama kernel and transpose-then-dual) and cross-checks them. A certified
disagreement raises `RuntimeError`, a library-bug signal deliberately
distinct from the `ValueError` used for input errors. A cross-check the
isomorphism test could not decide either way raises `TauAgreementUnknown`, a
limit of that test rather than evidence that the routes differ.

Injectives: `M.injective_envelope()` returns the pair `(I(M), M -> I(M))`,
`M.coresolve(steps)` a minimal `InjectiveCoresolution` with `terms`, `maps`,
`coaugmentation` and the same `ResolutionStatus` a projective resolution
reports, and `M.injective_dimension(bound)` a `Bounded` whose
`AtLeast(bound + 1)` is a genuine lower bound because the coresolution is
minimal.

Dynkin and Euclidean diagrams: `dynkin_type(quiver)` and
`euclidean_type(quiver)` recognise the underlying graph, returning a frozen
`DynkinType` / `EuclideanType` or `None` when the graph is not of that shape
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
python -m pytest tests/test_smoke.py
```
