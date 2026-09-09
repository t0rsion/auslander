# Checkpoints and theorem artifacts

[Package README](../README.md) | [Python workbench](workbench.md) | [Compute requests](compute.md) | [Algebra and homological computations](algebra.md) | [Representation theory](representation-theory.md)

## Durable module censuses

`CensusCheckpoint` stores one complete census or one checked prefix. The
checkpoint records the certificate, dimension vector, raw cursor, class
representatives, duplicate assignments, retention mode, limits, counters,
status, and a canonical fingerprint. Generic Python iterators do not have
this format.

Run a census in Python with an algebra and one dimension vector:

```python
field = auslander.PrimeField(5)
algebra = auslander.Algebra.linear_an(2)
limits = auslander.CensusLimits(
    max_candidates=100_000,
    max_work_units=1_000_000,
    retention="representatives_only",
)
checkpoint = auslander.run_census(algebra, [1, 1], field, limits)
auslander.write_checkpoint("a2-1-1.aus.json", checkpoint)

verified = auslander.verify_checkpoint(
    "a2-1-1.aus.json",
    auslander.CensusVerifyLimits(max_input_bytes=1_000_000_000, max_candidates=10_000_000),
)
print(verified.status, verified.cursor, verified.raw_space_size)
if verified.status == "cut":
    next_checkpoint = verified.resume(
        auslander.CensusLimits(
            max_candidates=1_000_000,
            max_work_units=10_000_000,
            retention=verified.limits.retention,
        )
    )
    auslander.write_checkpoint("a2-1-1.next.aus.json", next_checkpoint)
```

`write_checkpoint` writes UTF-8 JSON to a temporary file in the target
directory, flushes and syncs it, then replaces the target. A failed write
removes the temporary file. `verify_checkpoint` reads at most
`max_input_bytes + 1` bytes before decoding, rebuilds the algebra from the
embedded completion certificate, and replays the stored prefix. Its
`CensusVerifyLimits` argument sets parser and replay ceilings. The defaults
reject oversized input before allocation. A verified cut can resume with new
absolute limits. A complete checkpoint cannot resume. `CensusLimits.retention`
accepts `all_assignments` or `representatives_only`; the latter drops duplicate
witness records while preserving representatives and counters.

The CLI uses the same format. A start command takes a completion certificate
file, a dimension vector, and an output path:

```sh
auslander census start algebra-certificate.json '[1,1]' census.aus.json \
  --max-candidates 100000 --max-work-units 1000000 \
  --retention representatives_only
auslander census inspect census.aus.json
auslander census verify census.aus.json
auslander census resume census.aus.json census-next.aus.json \
  --max-candidates 1000000 --max-work-units 10000000
```

Each CLI verification starts a new process. `inspect` parses canonical JSON
without replay. `verify` replays the certificate and stored records. `resume`
verifies its input before it writes the next checkpoint. Add
`--verify-max-input-bytes`, `--verify-max-candidates`, and related
`--verify-*` flags when a large file needs higher caller-owned ceilings. Start
also accepts `--max-certificate-bytes`; certificate input is bounded before it
is handed to the algebra verifier. Resume keeps the input retention mode when
`--retention` is omitted. An explicit different mode is rejected.

## Durable homological streams

A homological checkpoint embeds a verified complete census. Its schema is
`auslander-computation-v1` and its payload kind is
`homological-self-pair-stream-v2`. It stores one self-pair row per
representative in census order. Each row contains exact Hom, stable Hom, and
Ext dimensions. A checkpoint also records fixed chunk limits, committed chunk
sizes, cumulative work, a typed status, and a canonical fingerprint. The prior
stream kind is rejected; write a new checkpoint instead of interpreting old
bytes as this format.

The stream commits complete source chunks. Python writes the initial value and
atomically replaces the file after each chunk. If a chunk fails, the last
written file still contains the preceding complete prefix. Resume first rebuilds
the census and replays every stored row. It then starts at `next_source`.

```python
verified_census = auslander.verify_checkpoint("census.aus.json")
stream = auslander.start_homological_stream(
    verified_census,
    4,
    auslander.HomologicalStreamConfig(
        max_live_sources=16,
        max_sources=1_000,
        max_work_units=10_000_000,
    ),
)
checkpoint = auslander.run_homological_stream("homology.aus.json", stream)

if checkpoint.status == "cut":
    checkpoint = auslander.resume_homological_checkpoint(
        "homology.aus.json",
        "homology-next.aus.json",
        auslander.HomologicalStreamBudget(
            max_sources=10_000,
            max_work_units=100_000_000,
        ),
    )
```

The CLI runs the same start, inspect, replay, and resume path:

```sh
auslander homological start census.aus.json 4 homology.aus.json \
  --max-live-sources 16 --max-sources 1000 --max-work-units 10000000
auslander homological inspect homology.aus.json
auslander homological verify homology.aus.json
auslander homological resume homology.aus.json homology-next.aus.json \
  --max-sources 10000 --max-work-units 100000000
```

All source and work ceilings are absolute. Resume rejects a ceiling below the
committed prefix. Parser and replay defaults reject oversized files before
allocation. Raise an outer limit with `--verify-*`. Raise an embedded census
limit with `--verify-census-*`. Start uses `--census-verify-*` for its input
census. Checkpoints are canonical UTF-8 JSON and can move between machines that
run the same schema and engine identifiers.

## Workflow reports

`auslander.export` writes a Markdown report or a structured CSV report. Both
formats include status, verification state, field, dimensions, representative
count, cursor data, and the positive degree interval. Markdown labels a
replayed complete value as verified within its finite scope. A replayed cut
value uses `replay verified prefix` and keeps `status: cut`.

CSV starts with one `record_type=metadata` record. Its `status` and
`verification` fields describe the whole value. `field`, `dimensions`,
`first_degree`, `last_degree`, `raw_space_size`, and
`total_representatives` describe the finite domain. `census_cursor` identifies
the census prefix. `next_source` and `rows` identify the homological prefix.
The remaining records use `record_type=row` and fill `index`, `coordinates`,
and `Ext^n` columns. The metadata record remains when the prefix has no rows.

## Theorem artifacts

`auslander theorem self-ext-locus` turns a complete homological checkpoint
into a finite positive self-Ext vanishing claim. `inspect` parses the canonical
file. `verify` rebuilds its census, replays every stored row, and recomputes
the locus through `ExtSpace::new`. That constructor is the crate's generic Ext
path, not a second Ext implementation. The locus check can stop at the first
mismatch.

See [Self-Ext locus artifacts](../../../docs/theorem-artifacts.md) for the
Python API, CLI commands, verification limits, and claim boundary.
