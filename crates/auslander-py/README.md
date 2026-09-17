# auslander-py

Python bindings for the `auslander` crate: finite-dimensional basic algebras
kQ/I over a checked prime field, where I is an admissible ideal given by
forbidden words or by general relations, and finite-dimensional right
modules. The v0.9 catalog API builds complete indecomposable catalogs, caches
ordered Ext tables, enumerates multiplicities, and replays typed artifacts.
Paths compose left to right; arrow matrices act on row vectors.

## Guides

- [Python workbench](docs/workbench.md)
- [Checkpoints and theorem artifacts](docs/checkpoints.md)
- [Compute requests](docs/compute.md)
- [Algebra and homological computations](docs/algebra.md)
- [Representation theory](docs/representation-theory.md)
- [Catalog atlas workflow](docs/catalog-workflow.md)
- [v0.9 migration](https://github.com/t0rsion/auslander/blob/main/docs/migration-v09.md)

## Quick start

With a field-bound gentle-tree algebra, `catalog.atlas` fixes the complete
catalog and its inclusive Ext degree bound:

```python
import auslander

field = auslander.PrimeField(5)
quiver = auslander.Quiver(4, [(0, 1), (1, 2), (3, 2)])
algebra = auslander.Algebra(quiver, [[0, 1]], field)
catalog = algebra.catalog()
atlas = catalog.atlas(max_degree=3)
result = atlas.enumerate([1, 1, 1, 1])
assert catalog.provenance == "gentle_tree"
assert result.status == "complete"
assert len(result) == 6

artifact = atlas.export([1, 1, 1, 1])
replayed = auslander.verify_catalog_atlas_artifact(artifact.canonical_json)
assert replayed.verification == "replayed"
```

The [catalog workflow notebook](examples/catalog_workflow.ipynb) displays the
catalog decomposition, ordered Ext cells, materialized modules, artifact
replay, and a degree-two obstruction.

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
