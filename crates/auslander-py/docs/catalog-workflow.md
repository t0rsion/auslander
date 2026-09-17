# Catalog atlas workflow

This example builds a complete gentle-tree catalog, enumerates one dimension
vector, materializes each decomposition, and replays a portable atlas artifact.
The code lives in [`examples/catalog_workflow.py`](../examples/catalog_workflow.py).
The executed notebook is
[`examples/catalog_workflow.ipynb`](../examples/catalog_workflow.ipynb).

## The algebra and finite scope

The presentation is

```text
field p
vertices 0 1 2 3
arrows a:0->1 b:1->2 c:3->2
relations a*b = 0
```

The example substitutes `p = 2` and `p = 5`. `parse_presentation(...).build()`
returns a field-bound `Algebra`. The relation is checked when the algebra is
built.

The catalog route recognizes the gentle tree:

```python
algebra = build_algebra(5)
catalog = auslander.catalog(algebra)
assert catalog.provenance == "gentle_tree"
assert len(catalog) == 8
```

`catalog.entries[i]` is the certified indecomposable at stable index `i`.
The eight entries are the four simples, the three edge strings, and the
string along `b` followed by the inverse of `c`.

The atlas fixes this finite scope:

```python
TARGET_DIMENSIONS = [1, 1, 1, 1]
DEGREE_BOUND = 3
atlas = catalog.atlas(DEGREE_BOUND)
```

`TARGET_DIMENSIONS` is the requested total dimension vector. The bound is
inclusive, so each Ext row contains degrees zero through three. The example
makes no claim about another field, dimension vector, or degree.

## Cached Ext table and multiplicity decomposition

`CatalogAtlas` stores one ordered row for each catalog pair. The source index
comes first:

```python
row = atlas.ext_table.row(source=0, target=0)
assert row.source == 0
assert row.target == 0
assert len(row.dimensions) == DEGREE_BOUND + 1
```

The atlas uses the same catalog order for multiplicities. The finite search
returns every nonnegative vector whose direct sum has the target dimensions:

```python
enumeration = atlas.enumerate(TARGET_DIMENSIONS)
assert enumeration.status == "complete"
assert enumeration.verification == "computed"

for multiplicities in enumeration.solutions:
    module = atlas.materialize(multiplicities)
    scores = atlas.self_ext_scores(multiplicities)
    assert module.dims == TARGET_DIMENSIONS
    print(multiplicities, scores)
```

For this example, the six multiplicity rows and cached self-Ext scores are:

| multiplicities in catalog order | `Ext^0` | `Ext^1` | `Ext^2` | `Ext^3` |
| --- | ---: | ---: | ---: | ---: |
| `[0, 1, 0, 0, 0, 0, 1, 0]` | 2 | 0 | 0 | 0 |
| `[0, 1, 0, 0, 0, 1, 0, 1]` | 3 | 1 | 0 | 0 |
| `[1, 0, 0, 0, 1, 0, 0, 0]` | 2 | 0 | 0 | 0 |
| `[1, 0, 0, 1, 0, 0, 0, 1]` | 3 | 1 | 0 | 0 |
| `[1, 0, 1, 0, 0, 0, 1, 0]` | 3 | 2 | 1 | 0 |
| `[1, 0, 1, 0, 0, 1, 0, 1]` | 4 | 3 | 1 | 0 |

`atlas.self_ext_scores` contracts the cached Ext rows with the multiplicity
vector. `atlas.materialize` builds the corresponding direct sum and checks its
resource limit.

## Atlas artifact export and replay

`CatalogAtlas.export` stores the catalog certificate, Ext rows, multiplicity
rows, operation counts, limits, and typed enumeration status:

```python
artifact = atlas.export(TARGET_DIMENSIONS)
text = artifact.canonical_json
parsed = auslander.CatalogAtlasArtifact(text)
assert parsed.status == "complete"
assert parsed.verification == "unverified"
replayed = auslander.verify_catalog_atlas_artifact(text)
assert replayed.status == "complete"
assert replayed.verification == "replayed"
```

The verifier rebuilds the certified algebra and catalog, recomputes the atlas,
checks the optimized and generic Ext tables, then checks every multiplicity
row. The fingerprint detects accidental changes before replay. The report
records the field, provenance, degree bound, status, verification state, and
rows.

## Cut status remains cut after replay

A checked multiplicity limit stores an exact prefix. It does not imply that the
prefix is complete:

```python
limits = auslander.MultiplicityLimits(max_solutions=1)
cut = atlas.enumerate(TARGET_DIMENSIONS, limits)
assert cut.status == "cut"
assert cut.verification == "computed"

cut_artifact = atlas.export(TARGET_DIMENSIONS, limits)
cut_replayed = auslander.verify_catalog_atlas_artifact(cut_artifact.canonical_json)
assert cut_replayed.status == "cut"
assert cut_replayed.verification == "replayed"
```

Replay validates the recorded limit, coverage, search count, rows, and typed
reason.

## Raw census comparison

The script also runs the raw matrix census through the high-level workflow
API. It retains assignments so the output includes an isomorphism witness:

```python
definition = auslander.define(
    PRESENTATION.format(field=5),
    TARGET_DIMENSIONS,
    last_degree=DEGREE_BOUND,
)
result = auslander.compute(
    definition,
    census_limits=auslander.CensusLimits(
        retention="all_assignments",
        max_assignments=256,
    ),
)
verified = auslander.verify(result)
```

The raw census is an independent comparison of thin arrow matrices. Its six
self-Ext rows agree with the six atlas decompositions after the rows are
matched by their modules. The census does not build the catalog artifact.

## The degree-two obstruction

The module `M = S_0 \\oplus S_2` has dimension vector `[1, 0, 1, 0]`:

```python
module = algebra.module([1, 0, 1, 0], [[[]], [], []])
assert module.ext_table(module, DEGREE_BOUND) == [2, 0, 1, 0]
```

The nonzero degree-two entry comes from the ordered relation between vertices
zero and two. A degree-one-only check misses this obstruction.

## Running the example

With the package installed, run:

```sh
python examples/catalog_workflow.py /tmp/catalog-workflow
```

The command writes one canonical atlas artifact and one Markdown report per
field. The notebook test executes the same workflow with the current package.
