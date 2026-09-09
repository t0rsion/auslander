# Self-Ext locus artifacts

A self-Ext locus artifact records one finite claim that another process can
check. It embeds a complete homological checkpoint and names the representative
indices whose self-Ext groups vanish through one positive degree interval.

The format uses schema `auslander-theorem-v1` and kind
`fixed-dimension-self-ext-locus-v1`. The JSON is canonical. Unknown keys,
noncanonical bytes, and unsupported identifiers fail during bounded parsing.

## Build an artifact

The input checkpoint must have status `complete`. Building first replay-checks
the checkpoint, then derives the locus from its exact rows.

```sh
auslander theorem self-ext-locus homology.aus.json 1 4 locus.aus.json
```

The same path is available from Python:

```python
artifact = auslander.build_self_ext_locus_artifact_file(
    "homology.aus.json",
    "locus.aus.json",
    1,
    4,
)
print(artifact.vanishing_count, artifact.fingerprint)
```

`write_theorem_artifact` uses a temporary sibling file, flushes it, and replaces
the target. A failed replace leaves the prior target unchanged.

## Inspect and verify

Inspection checks canonical parsing and the fingerprint. It does not accept the
mathematical claim.

```sh
auslander theorem inspect locus.aus.json
```

Verification rebuilds the embedded census and replays every homological row.
It then recomputes the locus through `ExtSpace::new`. That constructor is the
crate's generic Ext path, not a second Ext implementation. The locus check can
stop at the first mismatch.

```sh
auslander theorem verify locus.aus.json
```

Python exposes the same distinction:

```python
parsed = auslander.load_self_ext_locus_artifact("locus.aus.json")
verified = auslander.verify_self_ext_locus_artifact_file("locus.aus.json")
assert parsed.fingerprint == verified.fingerprint
```

`SelfExtLocusVerifyLimits` bounds the outer input, index list, reconstructed
representatives, degree span, and generic Ext spaces. Its `checkpoint` field
contains the nested checkpoint parser and replay limits.

## Claim boundary

The artifact covers one checked prime field, one fixed dimension vector, and
one finite interval. A complete census proves coverage of its raw matrix
domain. The artifact does not prove a statement over extension fields, other
dimensions, or the full module category.

The FNV-1a fingerprint detects changed canonical bytes. It is not a signature.
Checkpoint replay and the generic `ExtSpace::new` locus check provide the
mathematical check.

The committed starter artifact is
[`commutative-square-f2-d1111-self-ext-1-3.json`](../crates/auslander/artifacts/research/commutative-square-f2-d1111-self-ext-1-3.json),
fingerprint `c89b7f314194f289`. The flagship artifact is
[`commutative-square-f2-d2112-self-ext-1-3.json`](../crates/auslander/artifacts/research/commutative-square-f2-d2112-self-ext-1-3.json),
fingerprint `748d068629a7d970`. See
[`commutative-square-study.md`](commutative-square-study.md).
