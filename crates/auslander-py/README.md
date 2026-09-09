# auslander-py

Python bindings for the `auslander` crate: finite-dimensional basic algebras
kQ/I over a checked prime field, where I is an admissible ideal given by
forbidden words or by general relations, and finite-dimensional right
modules. Paths compose left to right; arrow matrices act on row vectors.

## Guides

- [Python workbench](docs/workbench.md)
- [Checkpoints and theorem artifacts](docs/checkpoints.md)
- [Compute requests](docs/compute.md)
- [Algebra and homological computations](docs/algebra.md)
- [Representation theory](docs/representation-theory.md)

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
