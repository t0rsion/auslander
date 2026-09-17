# Catalog benchmark

`catalog_benchmark` measures a complete catalog workflow against a finite raw
census. It uses the public Rust API. Each run emits one JSON line per case.

## Run the benchmark

Run the release profile from the workspace root:

```text
cargo run --release -q -p auslander --example catalog_benchmark -- --iterations 3
```

The default runs all cases. `--iterations N` repeats multiplicity enumeration
and cached score queries `N` times. `--case NAME` selects one case:

```text
cargo run --release -q -p auslander --example catalog_benchmark -- \
  --case nakayama-a4-medium --iterations 5
```

The accepted names are `nakayama-a3`, `gentle-tree-branch-ab0`, and
`nakayama-a4-medium`. Save stdout as JSON Lines to retain the measured record:

```text
cargo run --release -q -p auslander --example catalog_benchmark -- \
  --iterations 3 > catalog-benchmark.jsonl
```

The record schema is `catalog-benchmark-v2`. Durations use nanoseconds. The
`memory_peak_kib` value uses Linux `/proc/self/status` `VmHWM`. It is `null` on
targets without that file.

## Cases

The cases use `F_2` and Ext degrees zero through two.

| Case | Algebra and dimension vector | Catalog entries | Raw coordinates | Raw tuples |
| --- | --- | ---: | ---: | ---: |
| `nakayama-a3` | `A_3`, Kupisch `[3,2,1]`, `[1,1,1]` | 6 | 2 | 4 |
| `gentle-tree-branch-ab0` | `0→1→2←3`, `ab = 0`, `[1,1,1,1]` | 8 | 3 | 8 |
| `nakayama-a4-medium` | `A_4`, Kupisch `[4,3,2,1]`, `[1,2,2,1]` | 10 | 8 | 256 |

The gentle case uses arrow `0` followed by arrow `1` for `ab`. The medium case
keeps the raw census at 256 matrix tuples while increasing the catalog size
and the number of multiplicity solutions.

## Measured record

The evidence file
[`catalog-benchmark-2026-09-17.jsonl`](../crates/auslander/artifacts/research/catalog-benchmark-2026-09-17.jsonl)
contains the release-profile run used here:

```text
cargo run --release -q -p auslander --example catalog_benchmark -- --iterations 3
```

The table copies its timing fields. Full atlas setup is algebra construction,
catalog enumeration, and `CatalogAtlas::compute`. Artifact build and serialize
is the sum of `artifact_build` and `artifact_serialize`. Artifact replay is
canonical JSON parsing plus replay verification. Raw census total is domain
setup, the complete raw run, and raw-result replay.

| Case | Full atlas setup (ns) | Query, 3 calls (ns) | Materialize (ns) | Artifact build and serialize (ns) | Artifact replay (ns) | Raw census total (ns) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `nakayama-a3` | 173527 | 8051 | 1554 | 93900 | 681109 | 29177 |
| `gentle-tree-branch-ab0` | 226937 | 15455 | 3169 | 156201 | 1364501 | 504909 |
| `nakayama-a4-medium` | 296469 | 48623 | 7281 | 251260 | 2160096 | 64265510 |

Host record: 13th Gen Intel(R) Core(TM) i9-13900KS, x86_64, Linux 7.2.6-arch2-1.
Compiler: `rustc 1.92.0 (ded5c06cf 2025-12-08)`, release profile. The host was shared with other
development checks during measurement.

The timing table is one sample. It describes the selected build, field, degree
bound, dimensions, limits, and machine. It does not establish a general speed
claim.

## Phase definitions

The atlas setup builds one complete `IndecomposableCatalog`, then computes one
`CatalogAtlas`. The atlas stores every ordered source-target Ext row and one
source resolution per catalog entry. The `atlas_work` object reports pair,
cell, resolution, and table counts.

Each atlas query enumerates all multiplicity vectors for the dimension vector.
It then computes cached self-Ext scores for every solution. Repeated queries
must return the same vectors and score checksum. The query phase excludes
module materialization and generic Ext recomputation.

The materialization phase calls `CatalogAtlas::materialize` once per solution.
It records the number of direct-sum summands and a dimension checksum. Score
verification calls generic `ext_table` on those materialized modules and
compares every degree with the cached score.

Atlas verification calls `CatalogAtlas::verify`. That method rebuilds the atlas
and compares its tables, work counts, and retained resolutions.

## Artifact replay

The artifact phase calls `CatalogAtlasArtifact::from_verified`, serializes the
claim to canonical JSON, parses it under parser limits, and verifies it under
replay limits. The phase checks the parsed claim, complete status,
catalog work, and degree against the in-memory atlas.

`artifact_build` includes `from_verified`, which checks the atlas and computes
one artifact result sequence. `artifact_serialize` measures canonical JSON
serialization. `artifact_replay.timings_ns.total` is parser time plus verifier
time. The record includes artifact bytes, result rows, and the fingerprint.

## Raw census

The raw baseline builds one `Census` domain over the same algebra, field, and
dimension vector. It visits the full checked raw space with
`CensusRetention::RepresentativesOnly`. The record includes raw candidates,
accepted and rejected candidates, representatives, isomorphism checks, and
work units. Raw verification replays the complete census result.

The raw census is a separate enumeration path from catalog multiplicities. The
benchmark compares their complete class counts. It does not treat a stored
artifact as an external oracle. The raw space must remain feasible for the
machine running the command.

## Correctness checks

`cargo test -p auslander --example catalog_benchmark` runs the three fixed
cases. The test checks catalog counts, raw tuple counts, raw class counts,
cached and generic Ext scores, atlas verification, and artifact replay. It has
no timing threshold.

The JSON `verification` object records the same checks for a command-line run.
The `limits` object records the atlas pair, Ext-cell, resolution-term,
materialized-summand, materialized-cell, multiplicity, and raw census ceilings.
The counters describe work performed within those limits.

## Memory scope

On Linux, `memory_peak_kib` is the process high-water resident set size read
from `VmHWM` after the case completes. It includes earlier work in the same
process, so values across multiple output lines are cumulative high-water
observations. The benchmark reports no memory value when the operating system
does not expose this counter.
