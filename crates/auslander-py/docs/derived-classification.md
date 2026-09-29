# Derived classification

[Package README](../README.md) | [Python workbench](workbench.md) | [Algebra and homological computations](algebra.md) | [Representation theory](representation-theory.md)

`classify_derived` partitions a finite family of algebras over one prime
field up to derived equivalence. Two members share a class only through a
replayable derived equivalence. Two classes are separated only by a derived
invariant whose two finished values differ. A pair of classes that neither
side settles is listed in `unresolved`. The
[classification contract](../../../docs/derived-classification.md) fixes the
mathematics. The [tour notebook](../examples/derived_classification_tour.ipynb)
runs the main steps on the gentle algebras with 3 vertices.

## Read the invariants of one algebra

`Algebra(quiver, relations, field=F)` takes monomial relations as lists of
arrow indices. Paths compose left to right, so `[0, 1]` is arrow 0 followed
by arrow 1. Modules are right modules. `Algebra.derived_invariants()`
computes every kind in `DERIVED_INVARIANT_KINDS`, in that order:

```python
import auslander as au

F = au.PrimeField(2)
A = au.Algebra(au.Quiver(3, [(0, 1), (1, 2)]), [[0, 1]], field=F)
invariants = A.derived_invariants()
print(invariants)
assert invariants["cartan_determinant"].value == 1
assert invariants["aag_function"].value == [(4, 2)]
```

The printed table has one row per kind:

```text
DerivedInvariants: 3 vertices, dim 5, field F_2, Hochschild degrees 0..2
  kind                   status    value
  vertex_count           finished  3
  cartan_determinant     finished  1
  cartan_factors         finished  [1, 1, 1]
  symmetric_factors      finished  [1, 1, 4]
  skew_factors           finished  [1, 1, 0]
  cartan_pencil          finished  x^3 + x^2 + x + 1
  aag_function           finished  [(4, 2)]
  winding_class          finished  planar
  hochschild_dimensions  finished  [1, 0, 0]
  center_dimension       finished  1
  a finished value that differs separates two algebras; equal values never merge them
```

Each `InvariantReading` has a `status`:

| `status` | Meaning | Fields |
| --- | --- | --- |
| `finished` | The exact value. | `value` |
| `stopped` | A limit or cancellation stopped the computation. | `stop`, `reason`, `bar_diagnostics` |
| `not_applicable` | The presentation is not gentle, so `aag_function` and `winding_class` have no value. | `reason` |

`stop` is `overflow`, `bar_cut`, or `cancelled`. A `not_applicable` reading
is not a stop: larger limits give the same reading.

A bar cut after `HH^0` keeps the finished degrees. The reading of
`hochschild_dimensions` is then `finished` with fewer than
`hochschild_degree + 1` entries, and the table marks it, as in
`[1, 7], bar cut at HH^2`. Two such prefixes differ only at a degree
present in both.

Every invariant is a necessary condition for derived equivalence. Equal
values never merge two classes.

`InvariantLimits(hochschild_degree=2, bar=None)` bounds the Hochschild
computation. With `bar=None`, the ceilings are
`BarLimits(10000, 100000, 10000000, 1000000000)`.

## Compare two algebras

`first_difference` names the first kind whose two readings both finished
and differ. `DerivedInequivalenceWitness` stores that difference, and
`verify()` recomputes both values from scratch:

```python
kronecker = au.Algebra.kronecker(2, F).derived_invariants()
a2 = au.Algebra.linear_an(2).derived_invariants(field=F)
assert kronecker.first_difference(a2) == "symmetric_factors"

witness = au.DerivedInequivalenceWitness(kronecker, a2)
assert (witness.left_value, witness.right_value) == ([2, 0], [1, 3])
assert witness.verify()
```

When no finished value differs, `first_difference` returns `None` and the
witness constructor raises `ValueError`. Both records need the same field
and the same `InvariantLimits`.

## Recognize a gentle presentation

`Algebra.gentle()` recognizes the stored presentation. Loops, parallel
arrows, and cycles are allowed:

```python
presentation = A.gentle()
assert presentation.aag_function == [(4, 2)]
assert presentation.genus == 0
assert presentation.key.algebra(F).gentle().key == presentation.key
```

`aag_function` is the Avella-Alaminos-Geiss function as sorted pairs
`(n, m)`. `genus` is `(n - M - b + 2) / 2`, with `M` permitted threads and
`b` pairs. `key` is a `GentleKey`: two presentations have equal keys exactly
when they are isomorphic as bound quivers.

`complete_invariant()` returns a `GentleDerivedInvariant` with
`aag_function`, `genus`, and `winding_class`. The winding class is
`planar`, `gcd k`, `odd`, `even`, or `arf a`. Two connected gentle algebras
over one field are derived equivalent exactly when these values are equal
(Amiot, Plamondon, and Schroll, arXiv:1904.02555, Theorem 5.4):

```python
invariant = presentation.complete_invariant()
assert (invariant.genus, invariant.winding_class) == (0, "planar")
```

When recognition fails, `gentle()` raises `NotGentleError`, a `ValueError`
whose `kind` names the failed condition. The failure proves nothing about the
algebra: an isomorphic presentation can be gentle.

`AlgebraIsomorphism.from_gentle(source, target)` builds the isomorphism of
two gentle presentations with equal keys. `verify()` checks it from its
vertex map and arrow images alone.

## Classify a family

`connected_gentle_algebras(n, field)` returns one algebra per isomorphism
class of connected gentle bound quiver with `n` vertices. Pass the list to
`classify_derived`:

```python
family = au.connected_gentle_algebras(3, field=F)
result = au.classify_derived(family)
assert result.verify()
print(result.status, len(result.classes), len(result.unresolved))
```

The committed record
`crates/auslander/artifacts/research/derived-classification-f2-n3.json`
reports 77 members, 30 classes, 47 merges, 435 separations, and 0
unresolved pairs for `n = 3` over `F_2`, so the status is `complete`. The
default limits are the limits of that record.

The result has these parts:

| Accessor | Content |
| --- | --- |
| `classes` | `DerivedClass` values, ordered by `representative`. The `merges` of a class form a spanning tree of its `members`. |
| `separations` | One `ClassSeparation` per separated pair of classes, with a `DerivedInequivalenceWitness`. |
| `unresolved` | One `UnresolvedPair` per unresolved pair, with the indices of the walks that could have merged it. |
| `walks` | One `MutationWalk` per walked member, with its discovery `stop`. |
| `status` | `complete` exactly when `unresolved` is empty, and `incomplete` otherwise. |

`verify()` replays every merge recipe, checks every isomorphism, and
recomputes every witness. It runs no discovery. A limit or a cancellation
never turns an unresolved pair into a merge or a separation.

## Identify a member

A member index is a position in the family list. `presentation_text`
writes a member in the `parse_presentation` language, with arrow `i` named
`a{i}`. `show(algebra)` prints the same lines. The text rebuilds an algebra
with the same completion certificate:

```python
member = family[44]
text = au.presentation_text(member)
print(text)
rebuilt = au.parse_presentation(text).build()
assert rebuilt.certificate_json() == member.certificate_json()
```

```text
field 2
vertices 0 1 2
arrows a0: 0 -> 1 a1: 1 -> 0 a2: 0 -> 2 a3: 2 -> 1
relations a0*a1 = 0; a1*a2 = 0
```

`connected_gentle_keys(n)[i]` is the `GentleKey` of member `i` of
`connected_gentle_algebras(n, field)`.

## Read a merge

A `DerivedMerge` starts at the regular complex of member `source`. Each
recipe step `(direction, summand)` is a left or right mutation at one
indecomposable summand. The last complex `T` is tilting, and the recovered
target `End(T)^op` maps onto member `member` through `isomorphism`.
`show(merge)` writes the recipe, the vertex map, and each arrow image in the
arrows `a{i}` of the matched member:

```python
merge = result.classes[result.class_of(44)].merges[0]
print(au.show(merge))
```

```text
DerivedMerge: member 44 to member 62
  recipe from the regular complex of member 44: left mutation at summand 1
  recovered target End(T)^op: dim 10, isomorphic to member 62
  vertex map: 0 -> 1, 1 -> 2, 2 -> 0
  arrow 0 -> a1
  arrow 1 -> a3
  arrow 2 -> a2
  arrow 3 -> a0
```

## Find out why a pair is open

`explain()` returns an `Explanation`. For a complete result, `completed`
says that every pair of classes is separated. For an incomplete result,
`details` has one line per unresolved pair, and `next_action` names the
limits to raise. This run stores one tilting complex per walk, so it cannot
certify the one merge of the `n = 2` family:

```python
tight = au.ClassificationLimits(
    discovery=au.EquivalenceDiscoveryLimits(
        max_vertices=1,
        max_directed_mutations=4,
        max_total_terms=32,
        max_matrix_entries=2048,
    ),
)
open_result = au.classify_derived(au.connected_gentle_algebras(2, field=F), limits=tight)
explanation = open_result.explain()
print(explanation.next_action)
for line in explanation.details:
    print(line)
```

The explanation reads:

```text
raise discovery.max_vertices above 1 or walk through silting complexes with through_silting=True
classes 0 and 3 (members [0] and [3]): their complete gentle invariants agree, which implies a derived equivalence by Amiot, Plamondon, and Schroll that no merge certifies yet; walks from members [0, 3]: 2 stopped on vertex_limit 1; next: raise discovery.max_vertices above 1 or walk through silting complexes with through_silting=True
```

`print(explanation)` writes the same fields as labeled lines.

When the complete gentle invariants of a pair agree, the pair is derived
equivalent, and only a merge can settle it. Then `next_action` also
suggests a walk through silting complexes, unless the run already used one.
Otherwise it suggests a larger `invariants.hochschild_degree`. A larger
limit extends the search. It does not promise a merge or a separation. When
every walk from both classes exhausted its frontier, a larger discovery
limit changes nothing.

## Set limits

`ClassificationLimits(invariants=None, discovery=None, target=None)` holds
three limits. With `discovery=None`, each walk stores at most 8 tilting
complexes. Every walk gets the whole discovery budget, so the cost grows
with the family size times that budget:

```python
limits = au.ClassificationLimits(
    invariants=au.InvariantLimits(hochschild_degree=3),
    discovery=au.EquivalenceDiscoveryLimits(
        max_vertices=16,
        max_directed_mutations=64,
        max_total_terms=512,
        max_matrix_entries=32768,
    ),
)
wider = au.classify_derived(au.connected_gentle_algebras(2, field=F), limits=limits)
assert wider.verify()
```

`EquivalenceDiscoveryLimits()` with no arguments stores up to 1024
tilting complexes per walk. Set every ceiling when you raise one.

## Walk through silting complexes

With `through_silting=True`, each walk also stores silting complexes that
are not tilting and mutates them further. They count toward `max_vertices`.
Targets come from tilting vertices only, so every merge still ends at a
tilting complex. Members 470 and 724 of `connected_gentle_algebras(4, F)`
share every invariant. A tilting walk leaves the pair open, and a silting
walk merges it:

```python
pair = [
    au.Algebra(au.Quiver(4, [(0, 1), (0, 2), (3, 1), (2, 3), (2, 3)]), [[1, 4], [4, 2]], field=F),
    au.Algebra(au.Quiver(4, [(0, 1), (1, 2), (0, 1), (2, 3), (2, 3)]), [[0, 1], [1, 4]], field=F),
]
walk = au.EquivalenceDiscoveryLimits(
    max_vertices=32,
    max_directed_mutations=128,
    max_total_terms=1024,
    max_matrix_entries=65536,
)
tilting = au.classify_derived(pair, limits=au.ClassificationLimits(discovery=walk))
assert tilting.status == "incomplete"
silting = au.ClassificationLimits(discovery=walk, through_silting=True)
merged = au.classify_derived(pair, limits=silting)
assert merged.status == "complete" and merged.verify()
```

`ClassificationLimits(through_silting=...)`, when given, replaces the flag
of `discovery`. The atlas stores the flag. Without it, the verifier rejects
a recipe that passes through a silting complex that is not tilting.

## Cancel a run

`classify_derived` releases the GIL. Another thread can cancel it through a
`ComputationControl`:

```python
import threading

control = au.ComputationControl()
threading.Timer(0.05, control.cancel).start()
partial = au.classify_derived(family, control=control)
assert partial.verify()
```

Cancellation stops the current walk and each later walk before its first
mutation. The invariants of a member stop with `cancelled` when the
cancellation comes before their bar computation. Every pair those walks
could have merged stays unresolved, and `explain()` says to rerun without
cancellation.

## Export and replay an atlas

`to_artifact()` returns the portable `derived-atlas-v1` form of a result as
a `DerivedAtlasArtifact`. `export(path)` writes its canonical JSON with an
atomic replace and returns the path. `verify_derived_atlas` replays the
file:

```python
import pathlib
import tempfile

atlas = result.to_artifact()
path = result.export(pathlib.Path(tempfile.mkdtemp()) / "atlas.json")
replayed = au.verify_derived_atlas(path)
assert replayed.verification == "replayed"
assert replayed.fingerprint == atlas.fingerprint
assert [c.members for c in replayed.classes] == [c.members for c in result.classes]
```

`verify_derived_atlas(source, control=None)` takes the atlas text or a
path. A `str` that starts with `{` is the text. It rebuilds every member
from its certificate, recomputes every reading, rebuilds every separation
witness, and replays every merge recipe. It runs no discovery, so the stop
of each walk is the recorded stop, not a checked one. `explain()` on a
replayed result says `recorded walks (not replayed)`. The verifier limits
are the Rust defaults of `DerivedAtlasVerifyLimits`; Python does not expose
them.

| Outcome | Meaning |
| --- | --- |
| `DerivedClassification` | Every stored claim replayed. `verification` is `replayed`, and `fingerprint` is the fingerprint of the atlas. |
| `IncompleteArtifactVerification` | Cancellation or a verifier ceiling stopped the replay. `kind` is `cancelled`, `declared_limit`, or `work_limit`. |
| `ValueError` | The atlas is malformed or not canonical, or a claim does not replay. The message names the claim. |

A computed result reports `verification == "computed"` and has no
fingerprint. When cancellation stopped a reading, `to_artifact()` raises
`ValueError`: the verifier recomputes every reading and cannot reproduce a
cancelled one.

`DerivedAtlasArtifact(text)` parses an atlas without replay, and its
`verify(control=None)` replays it. The generic readers accept the kind
`derived_atlas`. `verify_file(path)` and `verify(path)` replay the atlas,
`inspect(path)` reports its counts without replay, `checkpoint(atlas, path)`
writes it, and `Session.add_artifact` stores it. A `limits` argument does
not apply to an atlas and raises `TypeError`.

`crates/auslander/artifacts/research/derived-atlas-f2-n3.json` is the
committed atlas of the connected gentle algebras with at most 3 vertices
over `F_2`. The static page in `web/` replays the same file in the browser,
without Python. See the [browser verifier](../../../docs/browser-verifier.md).

## Display in a notebook

In Jupyter, a `DerivedClassification` shows a summary, a class table, a
collapsible table of separations, and the unresolved pairs. Each class row
lists the representative, the members, the merge count, and the
determinant, AAG function, winding class, and Hochschild dimensions of the
representative. `repr()` prints the same class table as text.
`DerivedInvariants` shows its table the same way.

`show(result, max_items=200)` bounds the output. The class and separation
tables share `max_items` rows and count the rows they omit. The text form
also stops at `max_chars` characters.

## Export a LaTeX table

`to_latex(result)` returns a `tabular` with one row per class. Each row
lists every member, then the determinant, AAG function, winding class, and
Hochschild dimensions of the representative. Comment lines above the table
carry the summary, the atlas fingerprint of a replayed result, and each
unresolved pair:

```python
table = au.to_latex(replayed)
assert "% derived-atlas-v1 fingerprint " + replayed.fingerprint in table
assert table.count(r" \\") == len(replayed.classes) + 1
```

The table has no member presentations. Cite a member through
`presentation_text` or its `GentleKey`.

## Not covered

- A merge needs a certified tilting path. Equal complete gentle invariants
  imply derived equivalence by Amiot, Plamondon, and Schroll, but they never
  merge two classes on their own.
- The invariants of an algebra that is not gentle are necessary conditions
  only. An unresolved pair of such algebras can be derived equivalent or not.
- Every member must live over one prime field. Members over different
  fields raise `ValueError`. `Algebra.over(field)` binds a field-free
  presentation to a field.
