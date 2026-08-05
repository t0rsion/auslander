# QPA oracle

Differential harness comparing this library's homological output against QPA (the
GAP package "Quivers and Path Algebras"), an independent implementation with two
decades of use.

## Files

Two JSON files with the same schema, produced by independent tool chains:

- `qpa_expected.json`: committed, and the oracle. A real GAP+QPA run of
  `generate_fixtures.g` generated it. This library never writes it. The always-on
  test `library_matches_the_committed_qpa_truth` compares the library's freshly
  computed values against it, and a missing or unreadable file is a hard test
  failure, not a skip.
- `native_snapshot.json`: committed, and not an oracle. It is this library's own
  output, written by the test's `QPA_ORACLE_WRITE=1` mode. It is kept so that
  unintended drift in our values fails CI even without GAP installed. Agreement
  with it is self-consistency only. Correctness comes from `qpa_expected.json`.

`fixtures_qpa.json` is the name `generate_fixtures.g` writes into its working
directory. It is never committed here.

## Test modes (`crates/auslander/tests/qpa_oracle.rs`)

| Mode | Trigger | Behavior |
| --- | --- | --- |
| Oracle comparison | always on | library values vs `qpa_expected.json`; missing file = failure |
| Snapshot self-consistency | always on | library output vs `native_snapshot.json`, byte for byte |
| Snapshot rewrite | `QPA_ORACLE_WRITE=1` | rewrites `native_snapshot.json` only, never `qpa_expected.json` |
| Live GAP run | `QPA_ORACLE=1` | runs `generate_fixtures.g` under GAP+QPA in a temp dir, compares the fresh output against the library (values) and against `qpa_expected.json` (values, then byte for byte); fails hard when GAP is missing, QPA does not load, no output appears, or anything mismatches |

## GAP discovery (live run and regeneration)

The launcher in the test resolves GAP and QPA in this order:

1. The GAP binary is `$GAP_BIN` when set, otherwise `gap` on `PATH`. Use an
   absolute path (e.g. `/usr/bin/gap`) in shells where `gap` is aliased away.
   Spawned processes never see shell aliases, but interactive commands do.
2. GAP launches plainly when `~/.gap/pkg/qpa` exists, because GAP auto-loads
   packages from the `~/.gap` user root.
3. Otherwise `$QPA_DIR` must point at a QPA source tree. The test creates a
   temporary GAP root with `pkg/qpa` symlinked to it and launches
   `gap -q -T -l ";TMPROOT" generate_fixtures.g` (the leading `;` appends the
   root, so the standard library still resolves). QPA cannot load without its
   `gbnp` dependency in some root. When the system and user roots lack it, set
   `$GBNP_DIR` to a gbnp source tree and it is symlinked alongside.

GAP is invoked with `-q -T` and closed stdin, so an error exits nonzero instead
of hanging in a break loop. A QPA load failure is such an error.

## Regenerating `qpa_expected.json`

Only the GAP path may write this file:

```sh
cd "$(mktemp -d)"
/usr/bin/gap -q -T /path/to/crates/auslander/tests/qpa-oracle/generate_fixtures.g
cp fixtures_qpa.json /path/to/crates/auslander/tests/qpa-oracle/qpa_expected.json
```

Then run the test suite and record the new provenance (below) in this README.
`QPA_ORACLE_WRITE=1 cargo +1.92 test --test qpa_oracle` regenerates
`native_snapshot.json` after an intentional library change. It never touches
`qpa_expected.json`.

## Provenance of the committed `qpa_expected.json`

- Generated: 2026-07-24, on Arch Linux, package `gap 4.16.0-2`
  (`/usr/bin/gap`, `GAPInfo.Version` = `4.16dev`).
- QPA: version 1.36, loaded from `~/.gap/pkg/qpa`, a git clone at
  `v1.36-20-g9100462`.
- Command: `cd "$(mktemp -d)" && /usr/bin/gap -q -T
  .../tests/qpa-oracle/generate_fixtures.g && cp fixtures_qpa.json
  .../tests/qpa-oracle/qpa_expected.json` (12 fixtures written; schema v4
  adding `injdim`).
- SHA-256: `a7109458a2305f79d4fdcf7ccc471d0d58ec743d6c6245b6f979e731f85a3327`.
- The file is byte-identical to `native_snapshot.json` produced by this library,
  as required before committing.

## Schema

```json
{
  "schema": "auslander-qpa-oracle-v4",
  "convention": "right",
  "max_ext_degree": 4,
  "injdim_bound": 6,
  "fixtures": [
    {
      "name": "linear_an_2",
      "num_vertices": 2,
      "dim": 3,
      "cartan": [[1, 1], [0, 1]],
      "tau": [[0, 1], [0, 0]],
      "tau_injectives": [[0, 1], [0, 0]],
      "injdim": [0, 1],
      "ext": [ [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0]], ... ]
    }
  ]
}
```

- `dim`: dimension of the algebra over the base field.
- `cartan`: row `i` is the dimension vector of the indecomposable projective
  `P_i`. The GAP script computes rows as `DimensionVector` of
  `IndecProjectiveModules(A)` rather than calling QPA's `CartanMatrix`, so the row
  meaning is pinned by construction on both sides.
- `tau`: row `i` is the dimension vector of the AR translate `τ S_i`, computed
  by QPA as `DimensionVector(DTr(S_i))`, and the zero vector when `S_i` is
  projective (the library side compares `Tau::Zero` equal to the zero vector).
- `tau_injectives`: row `i` is the dimension vector of `τ I_i` for the
  indecomposable injective `I_i` (`IndecInjectiveModules(A)[i]` in QPA,
  `Module::injective` here), the zero vector when `I_i` is projective. The
  injective family supplies the committed non-simple τ cases across the suite.
  Individual `I_i` may be simple or projective. On most fixtures the minimal
  presentation of `I_i` has several projective summands, so the family
  exercises multi-entry presentations that the simples cannot.
- `injdim[i]`: the injective dimension of `S_i`, from QPA's
  `InjDimensionOfModule(S_i, injdim_bound)`. QPA returns `false` when the
  dimension exceeds the bound. That refusal is written as `injdim_bound + 1`,
  which is exactly the payload of the `Bounded::AtLeast` the library returns for
  the same bound, so neither side encodes a finite value it has not proved.
- `ext[i][j][k]` = `dim Ext^k(S_i, S_j)` for `k = 0..max_ext_degree`. Indices are
  0-based in the file; GAP's 1-based vertex `v` corresponds to index `v - 1`.

Schema history: `auslander-qpa-oracle-v1` lacked `tau`, `v2` lacked
`tau_injectives`, and `v3` lacked `injdim`. The reader rejects all three, so a
stale oracle file fails loudly instead of silently skipping checks.

All stored values are characteristic-free. Both generators use `F_5`, and the
Rust writer also recomputes over `F_2` and asserts agreement. JSON is written
and read by hand: the schema is small and fixed, so `format!` plus a strict
recursive-descent reader replaces a serde dependency. The reader rejects
duplicate object keys and trailing commas at parse time, and the comparator
rejects unknown top-level and fixture keys, so leniency cannot let a corrupted
or hand-edited oracle through. Only whitespace is free-form.

## Conventions

QPA works with right modules and composes paths left to right, exactly like
auslander, so the GAP output stores QPA's values verbatim under
`"convention": "right"` and the comparison is index-for-index. If a file is ever
produced under a left-module setup, mark it `"convention": "left"`. The comparator
then transposes Cartan matrices, swaps the `(i, j)` Ext indices, and reads the
`tau` rows as `τ` over the opposite algebra before comparing. Left modules over
`A` are right modules over `A^op`, every directed pairing flips, and `τ` of a
left module is `τ` over `A^op`. The archived predecessor of this library used the
left convention, which is where its `Ext^1(S_sink, S_source)` values came from.

The frozen archive repo carries vendored GAP and QPA source trees under
`external__gap/` and `external__qpa/`. They can be built for a local installation
when no system GAP is available, and `external__qpa/` is a valid `$QPA_DIR`.
