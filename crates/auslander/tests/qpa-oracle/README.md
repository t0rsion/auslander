# QPA oracle

The harness compares the library against QPA, the GAP package Quivers and
Path Algebras. QPA is an independent implementation. A disagreement points
at one side or the other, not at a shared assumption.

For field definitions and schema history, see
[schema-reference.md](./schema-reference.md).
For fixture identities and conventions, see
[fixture-reference.md](./fixture-reference.md).

## Files

Two JSON files, produced by independent tool chains:

- `qpa_expected.json`: committed, at schema v9, and the oracle the harness
  reads. A real GAP+QPA run of `generate_fixtures.g` generated it. This library
  never writes it. The always-on test `library_matches_the_committed_qpa_truth`
  compares the library's freshly computed values against it, and a missing or
  unreadable file is a hard test failure, not a skip.
- `native_snapshot.json`: committed, at schema v6, and not an oracle. It is this
  library's own output, written by the test's `QPA_ORACLE_WRITE=1` mode. It is
  kept so that unintended drift in our values fails CI even without GAP
  installed. Agreement with it is self-consistency only. Correctness comes from
  `qpa_expected.json`. It stays at v6 because the oracle block holds
  `brute_agreement`, a GAP-internal cross-check with no library counterpart, and
  a snapshot must not invent one. The harness implements exactly these two
  schema strings and rejects every other, so neither file goes stale unnoticed.

`generate_fixtures.g` writes `qpa_generated.json` into its working directory,
which the `.gitignore` here covers. The name is deliberately not the oracle's,
so a run started in this directory cannot overwrite `qpa_expected.json`;
promoting a run is a separate copy.

The gentle-tree oracle uses `generate_catalog_fixtures.g` and
`catalog_qpa_expected.json`. The always-on test
`catalog::catalog_qpa_oracle_matches_the_gentle_catalog` parses this independent
document and compares both F_2 and F_5 modules, Hom, Ext, AR sequences, and
irreducible maps with the gentle catalog. The live test
`catalog::catalog_live_gap_run_agrees_with_committed_truth` runs when
`QPA_ORACLE=1`; it requires the generator sentinel, then compares its values
with the committed document and the Rust catalog. The generator writes
`catalog_qpa_generated.json`, never `catalog_qpa_expected.json`.

## Test modes (`crates/auslander/tests/qpa_oracle.rs`)

| Mode | Trigger | Behavior |
| --- | --- | --- |
| Oracle comparison | always on | library values vs `qpa_expected.json`; missing file = failure |
| Snapshot self-consistency | always on | library output vs `native_snapshot.json`, byte for byte |
| Snapshot rewrite | `QPA_ORACLE_WRITE=1` | rewrites `native_snapshot.json` only, never `qpa_expected.json` |
| Live GAP run | `QPA_ORACLE=1` | runs `generate_fixtures.g` under GAP+QPA in a temp dir, requires the sentinel and the output file, then compares the fresh output against the library (values) and against `qpa_expected.json` (values, then byte for byte); fails hard when GAP is missing, QPA does not load, no output appears, or anything mismatches |
| Catalog oracle comparison | always on | gentle catalog values vs `catalog_qpa_expected.json` for F_2 and F_5 |
| Catalog live GAP run | `QPA_ORACLE=1` | runs `generate_catalog_fixtures.g`, requires its sentinel and output, then compares fresh values with the committed catalog document |

The harness computes every v6 field from the library and compares it entry by
entry. Designated modules are built by construction from their kind and index,
never looked up by dimension vector. Almost-split sequences come from
`almost_split`, and the `ArDualityWitness` of every sequence the harness builds
is rechecked before its values are used. The irreducible morphisms out of a
module are computed over the opposite algebra on its dual, which is the same
computation as the morphisms into a module: `opposite` keeps the vertex ids and
`dual` keeps the dimension vector, so the values compare directly.

Run the legacy live oracle with this command:

```sh
QPA_ORACLE=1 cargo test -p auslander --test qpa_oracle \
  live_gap_run_agrees_with_library_and_committed_truth -- --exact --nocapture
```

The workspace sets `opt-level = 2` for the dev profile. Debug assertions and
overflow checks stay on.
`inclusion-ambiguity` dominates the v6 layer: its almost-split sequences run on
modules of dimension 18 and 24 over a 6-dimensional algebra, and every value is
computed twice, once over the algebra and once over its opposite for the
left-convention test.

## GAP discovery (live run and regeneration)

The launcher in the test resolves GAP and QPA in this order:

1. The GAP binary is `$GAP_BIN` when set, otherwise `gap` on `PATH`. Use an
   absolute path (e.g. `/usr/bin/gap`) in shells where `gap` is aliased away.
   Spawned processes never see shell aliases, but interactive commands do.
2. GAP launches plainly when `~/.gap/pkg/qpa` exists, because GAP auto-loads
   packages from the `~/.gap` user root.
3. Otherwise `$QPA_DIR` must point at a QPA source tree. The test creates a
   temporary GAP root with `pkg/qpa` symlinked to it and launches
   `gap -q -T -m 1g -l ";TMPROOT" generate_fixtures.g` (the leading `;` appends
   the root, so the standard library still resolves). QPA cannot load without
   its `gbnp` dependency in some root. When the system and user roots lack it,
   set `$GBNP_DIR` to a gbnp source tree and it is symlinked alongside.

GAP is invoked with `-q -T` and closed stdin, so an error quits the run instead
of hanging in a break loop. A QPA load failure is such an error. `-m 1g` asks
for a large initial workspace, which the workload needs (see below).

The exit code is not a failure signal. `gap -q -T` with closed stdin exits 0
after an uncaught error, measured for a division by zero, an unbound variable
and a QPA "no method found", so an `output.status.success()` assertion is
vacuous. `qpa_oracle.rs` checks the two signals that do carry:

- The generator writes its output in one final statement, after every value is
  computed and every byte formatted, so a run that dies leaves no output file.
- The last line of stdout is the sentinel `qpa-oracle-generator-ok`, printed
  after the write. An aborted run never reaches it.

## Regenerating the oracle

Only the GAP path may write these files:

```sh
cd "$(mktemp -d)"
/usr/bin/gap -q -T -m 1g \
   /path/to/crates/auslander/tests/qpa-oracle/generate_fixtures.g | tail -1
cp qpa_generated.json \
   /path/to/crates/auslander/tests/qpa-oracle/qpa_expected.json
```

The generator emits schema v9 and the last line must read
`qpa-oracle-generator-ok`. It writes `qpa_generated.json`, never
`qpa_expected.json`, so promoting a run is the deliberate copy above.

Before copying either file, confirm two completed runs in fresh directories
agree byte for byte.

Then run the test suite and record the new provenance in
[schema-reference.md](./schema-reference.md).
`QPA_ORACLE_WRITE=1 cargo +1.92 test --test qpa_oracle` regenerates
`native_snapshot.json` after an intentional library change. It never touches
`qpa_expected.json`.

Regenerate the gentle-tree document through the same GAP+QPA path:

```sh
cd "$(mktemp -d)"
/usr/bin/gap -q -T -m 1g \
   /path/to/crates/auslander/tests/qpa-oracle/generate_catalog_fixtures.g | tail -1
cp catalog_qpa_generated.json \
   /path/to/crates/auslander/tests/qpa-oracle/catalog_qpa_expected.json
```

Run the generator twice in fresh directories and compare the two
`catalog_qpa_generated.json` files before promotion. The final line must be
`qpa-catalog-oracle-generator-ok`. The Rust tests never write the committed
catalog document.

## Regenerating the census oracle

`qpa_census_expected.json` is independent truth for two finite census domains of
the commutative square over F_2: `d1111` and `d2112`. A real GAP+QPA run of
`generate_census_fixtures.g` writes `qpa_census_generated.json`. The Rust census
writer does not write either file.

Run the generator twice in fresh directories. Keep each directory until the
outputs compare byte for byte:

```sh
generator=/path/to/generate_census_fixtures.g
first=$(mktemp -d)
second=$(mktemp -d)
(
  cd "$first"
  gap -q -T -m 1g "$generator" | tee run.log
)
(
  cd "$second"
  gap -q -T -m 1g "$generator" | tee run.log
)
test "$(tail -n 1 "$first/run.log")" = qpa-census-oracle-generator-ok
test "$(tail -n 1 "$second/run.log")" = qpa-census-oracle-generator-ok
cmp "$first/qpa_census_generated.json" "$second/qpa_census_generated.json"
```

The last line and the output file are the completion signals. GAP may return
success after an uncaught error when stdin is closed, so the exit code is not
enough. Promote one verified output with an explicit copy:

```sh
cp "$first/qpa_census_generated.json" /path/to/qpa_census_expected.json
```

The launcher uses `$GAP_BIN`, or `gap` on `PATH`, and the QPA discovery rules
above. Set `$QPA_DIR` and, when required, `$GBNP_DIR` when QPA is not in the
user GAP root. The generated document records the GAP and QPA versions.
The live census test compares all census values and ignores those provenance strings
when the executable version differs.

## Reproducibility

Two claims live in `live_gap_run_agrees_with_library_and_committed_truth`, and
they are not the same strength.

The first is the mathematics: a real GAP+QPA run recomputes these values and
must agree with the library. That runs on any GAP and is asserted
unconditionally. It is the reason this oracle exists.

The second is reproducibility of this file, byte for byte. That holds only
within one GAP version. The test compares documents only when the fresh run's
`gap_version` matches the recorded value in
[schema-reference.md](./schema-reference.md), and otherwise reports the version
gap and stops. A different GAP still gates the mathematics.

CI runs the value comparison on its configured GAP environment. A byte-level
comparison requires the same GAP version as the recorded document.
