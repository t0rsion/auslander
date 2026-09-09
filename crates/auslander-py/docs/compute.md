# Compute requests

[Package README](../README.md) | [Python workbench](workbench.md) | [Checkpoints and theorem artifacts](checkpoints.md) | [Algebra and homological computations](algebra.md) | [Representation theory](representation-theory.md)

## Canonical compute requests

`auslander compute REQUEST.json` reads an `auslander-compute-v1` request and
writes one canonical JSON result. With no path or with `-`, the command reads
standard input. The result schema is `auslander-compute-result-v1`.
`auslander --version` prints the installed package version.

## Checked A2 batch example

Save the following request as `request.json`, then run it:

```sh
auslander compute request.json
```

The request has exactly four fields:

```json
{
  "schema": "auslander-compute-v1",
  "algebra": {"presentation": "field 5\nvertices 0 1\narrows a:0->1\n"},
  "modules": {
    "S0": {"dims": [1, 0], "maps": [[[]]]},
    "S1": {"dims": [0, 1], "maps": [[]]}
  },
  "operations": [
    {"op": "algebra_summary"},
    {"op": "hom", "source": "S0", "target": "S1"},
    {"op": "hom_dim", "source": "S0", "target": "S1"},
    {"op": "stable_hom", "source": "S0", "target": "S1"},
    {"op": "stable_hom_dim", "source": "S0", "target": "S1"},
    {"op": "ext_table", "source": "S0", "target": "S1", "max_degree": 2},
    {"op": "tau", "module": "S0"},
    {"op": "resolve", "module": "S0", "steps": 2},
    {"op": "decompose", "module": "S0"}
  ]
}
```

`algebra` contains exactly one `presentation` string or `certificate` string.
The presentation uses the text language shown above. A certificate is checked
by `Algebra.from_certificate`. A module contains `dims` and exactly one map
field. `maps` contains dense arrow matrices. `sparse_maps` contains
`[row, column, value]` triples for `Algebra.module_sparse`.

Supported operations are `algebra_summary`, `hom`, `hom_dim`, `stable_hom`,
`stable_hom_dim`, `ext_table`, `tau`, `resolve`, `decompose`, and
`homological_batch`. `ext_table` takes `max_degree`. `resolve` takes `steps`.
`hom` returns a full basis of vertex maps. `stable_hom` returns quotient and
projective-factor bases of vertex maps. `homological_batch` takes an ordered
`modules` name array, `max_degree`, and exactly one `pairs` array or
`all_pairs: true`. Pair endpoints can be names or indexes into that array.
It accepts optional `max_pairs` and `max_ext_cells` limits. The batch result
contains pair names, pair indexes, exact dimensions, work counts, and stored
resolution records. Unknown fields, operations, and names are rejected before
computation. Resolution results encode `finite` or `cut` status explicitly. A
cut includes its differential count and never means an infinite result.

Every module record contains `dims`, `total_dim`, and dense canonical `maps`.
Morphism records contain dense canonical vertex maps. Decomposition records include
inclusions, projections, and the split idempotents `projection.then(inclusion)`.

`hom` results contain `source`, `target`, `dimension`, and `basis`.
`stable_hom` results use the same fields and add
`projective_factor_dimension` and `projective_factor_basis`; `basis` is the
quotient basis. A batch `pairs` entry contains `source`, `target`, both indexes,
`hom_dim`, `stable_hom_dim`, and `ext_dimensions`. Batch `work` contains the
exact counts `resolutions`, `target_covers`, `hom_spaces`,
`projective_factor_spaces`, and `ext_tables`.

`ComputationControl` provides deterministic progress and cooperative
cancellation. Pass one as `control=control` to replacement, derived Hom,
automatic transport, discovery, or artifact verification. These calls release
the GIL, so another Python thread can poll or cancel them.

`show(value)` returns bounded text and notebook HTML. Quivers also receive SVG.
`to_dot`, `to_networkx`, and `to_latex` copy stored data without starting a
mathematical computation. `auslander.sage` contains copying matrix adapters.
