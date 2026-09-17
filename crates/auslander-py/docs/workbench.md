# Python workbench

[Package README](../README.md) | [Checkpoints and theorem artifacts](checkpoints.md) | [Compute requests](compute.md) | [Algebra and homological computations](algebra.md) | [Representation theory](representation-theory.md)

## Workbench

`python -m auslander` and `auslander repl` start IPython when it is installed,
or Python's standard console otherwise. The shell preloads `session`, `F`,
`algebra`, `module`, `show`, `explain`, and `verify_file`.

This session runs replacement, derived Hom, automatic classical transport,
bounded tilting-complex discovery, artifact export, artifact verification,
and recipe persistence:

```python
import auslander

text = """
field 5
vertices 0 1 2
arrows a:0->1 b:1->2
relations a*b = 0
"""
session = auslander.Session(5)
F = session.field
A = session.algebra("A", text)
X = auslander.BoundedComplex(0, [A.simple(0)], [])
Y = auslander.BoundedComplex(0, [A.simple(2)], [])

replacement = X.perfect_replacement()
assert replacement.verify()
assert X.derived_hom(Y).dimension(2) == 1

DA = A.module(
    [2, 2, 1],
    [[[0, 0], [1, 0]], [[0], [1]]],
)
tilting = auslander.ClassicalTiltingModule.classify(
    DA, auslander.TiltingLimits(4, 8)
).tilting
target = tilting.target_presentation(auslander.TargetLimits())
transport = auslander.DerivedEquivalenceCertificate(
    tilting, target
).automatic_transport
assert transport.forward(X).verify()

B = auslander.Algebra.linear_an(2).over(F)
graph = auslander.discover_equivalences(
    B,
    F,
    auslander.EquivalenceDiscoveryLimits(max_vertices=3),
)
assert graph.verify()
assert graph.stop in {"vertex_limit", "exhausted_frontier"}

artifact = auslander.build_derived_artifact(B, [("left", 1)], F)
verified = auslander.verify_derived_artifact(artifact)
assert verified.canonical_json == artifact
session.add_artifact("A2-left", artifact)
session.save("auslander-session.json")
```

## Finite self-Ext workflows

A `WorkflowDefinition` fixes one presentation, one dimension vector, and
one positive degree interval. Its canonical JSON uses schema
`auslander-workflow-definition-v1` and kind `finite-self-ext-workflow-v1`.
`compute()` builds a checked census, runs the bounded homological stream, and
returns a `WorkflowResult`. A cut keeps its typed status and exact prefix.
`verify()` replays every stored stage and returns a `VerifiedWorkflowResult`.
Definition parsing checks syntax. Algebra construction and certificate
verification run when `compute()` builds the algebra.

```python
presentation = """
field 2
vertices 0 1 2 3
arrows a:0->1 b:1->3 c:0->2 d:2->3
relations a*b - c*d = 0
"""
definition = auslander.define(presentation, [2, 1, 1, 2], last_degree=3)
auslander.write_definition("square-workflow.json", definition)
result = auslander.compute(definition)
verified = auslander.verify(result)
assert verified.verification == "replayed"
print(auslander.inspect(verified))
auslander.export(verified, "square-report.md", format="markdown")
```

`inspect()` reads canonical values without replay. `checkpoint()` writes the
selected `census`, `homological`, or `artifact` stage. `resume()` verifies a
cut, applies new absolute limits, and writes the next prefix. Reports use
Markdown or CSV; pass `verify_value=True` to replay before export.

The CLI exposes the same stages:

```sh
auslander workflow define square.txt '[2,1,1,2]' square-workflow.json --field 2
auslander workflow compute square-workflow.json square-result.json --max-sources 4
auslander workflow inspect square-result.json
auslander workflow resume square-result.json square-next.json --max-sources 1000
auslander workflow verify square-next.json
auslander workflow export square-next.json square-report.md --verify
```

## Stable-category batches

`Module.syzygy()` and `Module.cosyzygy()` return the requested module and the
cover or envelope prefix that produced it. `StableHomSpace` retains both the
quotient basis and the basis of maps through projectives. `HomologicalBatch`
shares one resolution per selected source and one projective cover per selected
target.

```python
F = auslander.PrimeField(5)
A = auslander.Algebra.dual_numbers().over(F)
S = A.simple(0)
P = A.projective(0)

omega = S.syzygy()
omega_inverse = S.cosyzygy()
assert omega.verify() and omega_inverse.verify()

stable = S.stable_hom(S)
assert stable.dim == 1
assert stable.projective_factor_dim == 0

batch = auslander.HomologicalBatch.all_pairs([S, P], 2)
assert batch.verify()
assert batch.selected_pairs == [(0, 0), (0, 1), (1, 0), (1, 1)]
```
