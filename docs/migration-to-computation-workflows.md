# Migration to computation workflows

The current API removes two duplicate Python names and retains no deprecated
aliases.

## Algebra class

Replace `auslander.MonomialAlgebra` with `auslander.Algebra`:

```python
A = auslander.Algebra.linear_an(3)
```

`Algebra` still accepts monomial presentations and general relations. Its
named constructors are unchanged.

## Module dimension vector

Replace `module.dim_vector` with `module.dims`:

```python
assert module.dims == [1, 1, 0]
```

The Rust method remains `Module::dim_vector`.

## Computation files

Homological stream checkpoints use envelope schema `auslander-computation-v1`
and payload kind `homological-self-pair-stream-v2`. The payload records each
committed chunk size so replay can reproduce work counters after a partial
chunk is resumed. The reader rejects the previous payload kind explicitly.

For an old stream checkpoint, verify its embedded census with `CensusCheckpoint`.
Start a new homological stream from that verified census. The old rows lack
chunk history and cannot be reused as a current checkpoint. Renaming the kind
field does not convert the data.

Census checkpoints and `auslander-theorem-v1` keep their envelope schemas.
A theorem artifact that embeds an old stream requires regeneration from a
current verified stream.
