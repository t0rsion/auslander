# v0.9 migration

The Python v0.9.0 surface uses vertex-first module constructors and explicit
field binding. Field-first calls from earlier releases have no compatibility
shim.

## Update Rust catalog matches

Exhaustive matches on `CatalogProvenance` need a `GentleTree` arm.
`ArQuiverError::UnsupportedDomain` now carries a `gentle` rejection alongside
`dynkin` and `nakayama`. Bind that field to report it, or add `..` when the
match does not inspect every route. `SupportTauError` adds
`Catalog(CatalogError)` for a rejected automatic catalog selection.

`IndecomposableCatalog::complete` selects Dynkin, Nakayama, then gentle tree.
Call a route constructor directly when the classification provenance must
stay fixed. `ar_quiver_from_catalog(&catalog)` reuses an existing catalog.

## Bind an algebra to a field

Named monomial constructors and `Algebra(quiver, forbidden)` accept an optional
`field`. Without it, they return a field-free algebra. Pass `field=F` when
constructing it, or call `algebra.over(F)`. A field-free algebra needs a field
for field-sensitive operations. A bound algebra may omit the field.

```python
F = auslander.PrimeField(5)
A = auslander.Algebra.linear_an(2).over(F)
S = A.simple(0)
```

`Algebra.from_relations(quiver, relations, field)` remains field-bound at
construction. `Algebra.from_certificate(text, *, field=None)` accepts an
optional field check, and `certificate_json(field=None)` follows the same rule:
a field-free algebra needs `field=F`, while a bound algebra may omit it.

## Update constructor calls

Move the vertex or module data before the optional field and use a keyword for
an unbound algebra.

| Earlier call | v0.9 call |
| --- | --- |
| `A.simple(F, vertex)` | `A.simple(vertex, field=F)` |
| `A.projective(F, vertex)` | `A.projective(vertex, field=F)` |
| `A.injective(F, vertex)` | `A.injective(vertex, field=F)` |
| `A.module(F, dims, maps)` | `A.module(dims, maps, field=F)` |
| `A.module_sparse(F, dims, maps)` | `A.module_sparse(dims, maps, field=F)` |
| `A.hochschild_cohomology(F, max_degree, limits)` | `A.hochschild_cohomology(max_degree, limits, field=F)` |

For repeated operations, bind once and omit the field:

```python
A = auslander.Algebra.truncated_poly(3).over(F)
S = A.simple(0)
P = A.projective(0)
M = A.module([1], [[[0]]])
HH = A.hochschild_cohomology(2, limits)
```

The `Session.module` method keeps its separate signature:
`session.module(name, algebra_name, dims, maps)`. It takes the field recorded
for the named session algebra. It does not use the `Algebra.module` signature.

## Recreate saved sessions

`Session.save()` now writes schema `auslander-session-v2`. The document stores
the session field, named algebra and module recipes, canonical artifacts, and
display settings. Each algebra recipe stores its presentation field. Each
module recipe stores the field selected from its named algebra.

```python
session = auslander.Session(2)
session.algebra("A2", presentation_f2)
session.algebra("A5", presentation_f5)
session.module("M2", "A2", [1, 1], [[[4]]])
session.module("M5", "A5", [1, 1], [[[4]]])
session.save("auslander-session.json")
```

The loader rebuilds every recipe through checked constructors and preserves the
field of each algebra. It rejects schema `auslander-session-v1` and documents
with missing or unknown top-level fields. Recreate an older session from its
presentations and module data.

Adding a presentation does not change the session's default field. A field-free
algebra added with `bind()` takes a snapshot of that default. Live bindings
have no saved recipe. If a module depends on one, `save()` rejects the missing
algebra recipe before replacing the destination. Use `session.algebra(...)`
for algebras that must survive a reload.

`verify_file` and `verify_file_text` dispatch portable values by schema and
kind. They accept workflow definitions, census checkpoints, homological
checkpoints, theorem artifacts, catalog atlas artifacts, and derived artifacts.
An unknown portable schema raises `ValueError`.

## Use a complete catalog

`A.catalog()` selects a supported classification route. Its entries can be
reused by `catalog.atlas(max_degree)`, `catalog.ar_quiver()`, higher
orthogonality, and coordinate matching. Unsupported algebras report the failed
domain checks.

Atlas artifacts use kind `catalog-atlas-v1` in the
`auslander-computation-v1` container. Existing census and theorem artifacts
keep their distinct kinds. See the [artifact contract](catalog-artifacts.md)
and the [executed workflow](../crates/auslander-py/docs/catalog-workflow.md).

## Read computation and verification separately

Workflow values expose two independent axes:

| Property | Meaning | Current values |
| --- | --- | --- |
| `status` | Computation progress or outcome | `active`, `cut`, or `complete` for workflow stages |
| `verification` | Replay state of the stored value | `computed`, `unverified`, or `replayed` |

An in-memory `WorkflowResult` reports `verification == "computed"`. A
`VerifiedWorkflowResult` reports `"replayed"`. `inspect(path)` parses a saved
checkpoint without replay and reports `"unverified"`; `verify(path)` replays
it. A cut can therefore have `status == "cut"` and
`verification == "replayed"`.

`auslander.explain(value)` exposes both properties on its `Explanation` result:
`explanation.status` describes the typed outcome, and
`explanation.verification` describes the replay state. Replay state does not
change a cut into a complete result.
