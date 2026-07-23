# auslander-py

Python bindings for the `auslander` crate: finite-dimensional basic algebras
kQ/I over a checked prime field, where I is an admissible monomial ideal, and
finite-dimensional right modules. Paths compose left to right; arrow matrices
act on row vectors.

The surface is small and algebra-owned: `PrimeField`, `Quiver`,
`MonomialAlgebra` (plus named constructors such as `linear_an`, `kronecker`,
`dual_numbers`, `linear_nakayama`), and modules built only through
`algebra.module(...)` / `simple` / `projective` / `injective`.

Morphisms: `M.hom(N)` returns a basis of the hom space `Hom_A(M, N)` as a list
of `Morphism` objects (a basis, not every morphism; arbitrary morphisms are
linear combinations of it), and `M.morphism(N, maps)` builds one checked
morphism from integer matrices, validating every commuting square. A
`Morphism` exposes `maps` (its vertex matrices as canonical integers in
`0..p`, in the same list-of-rows shapes `algebra.module` accepts) and
`is_isomorphism()`.

Homological invariants (`hom_dim`, `ext_dim`, `ext_table`, `resolve`, `pd`,
`global_dimension`) report partial results explicitly: a `Resolution` carries
an immutable `ResolutionStatus` whose `kind` is `ResolutionKind.FINITE` (with
`at` `None`) or `ResolutionKind.CUT` (with `at` the number of computed
differentials, the next syzygy being nonzero), and dimensions that may exceed
a bound come back as `Bounded` with exactly one of `exact` / `at_least` set.
There is no "None means infinite" anywhere.

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
