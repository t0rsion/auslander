# Derived workbench performance record

The [classical tilting component record](classical-tilting-performance.md)
contains target recovery, certificate, and strict-transport measurements.

This record measures the fixed acceptance fixtures over F_5 and the derived
classification study over F_2. It uses the machine and toolchain below:

```text
Linux 7.2.7-arch1-1 x86_64
13th Gen Intel(R) Core(TM) i9-13900KS
32 logical CPUs, 2 threads per core
rustc 1.92.0
cargo 1.92.0
```

Elapsed samples use the release profile, one process at a time, while other
jobs shared the machine. These values describe this machine. Tests gate
deterministic work counts, not elapsed time.

The harness calibrates each case, runs five trials, and reports the best
trial. The table gives the median of three runs, in nanoseconds per
operation, for the tree before and after the 2026-09-29 hot-path pass.

| Case | before | after |
| --- | ---: | ---: |
| replace_perfect pd2-simple-f5 | 37122.6 | 38817.0 |
| derived_hom pd2-simple-f5 | 44769.9 | 47890.1 |
| discover_equivalences a2-f5 | 417131.7 | 337759.3 |
| present_complex_target a2-f5 | 319840.8 | 106815.5 |
| verify artifact a2-f5 | 501095.0 | 258347.4 |

An interleaved rerun of the first two cases put the two trees within 1% of
each other, so their spread in the table is drift between runs.

The acceptance tests gate these algorithm-level counts:

| Case | Exact count |
| --- | ---: |
| Projective-dimension-two replacement | 28 work units |
| Derived Hom from `S_0` to `S_2` | 3 degrees, 1 chain-map dimension, 1 quotient dimension, 5 work units |
| Bounded A2 discovery | 5 mutations, 3 vertices, 8 terms, 6 matrix entries |
| Multi-degree A2 target | endomorphism dimension 3, 9 radical products, 0 paths, 0 relation terms |
| One-mutation artifact verification | 1 completed and reserved work unit |

The same exact counts hold over F_2 and F_5. The tests compare equality, not
an elapsed threshold.

Command:

```sh
cargo bench -p auslander --bench perf --profile release -- --group workbench --trials 5
```

## Classification study

The study classifies every connected gentle algebra with at most 4
vertices over F_2: 894 members at `n = 4`. The table gives the median wall
time of three runs of each command. Both trees ran the study as the
`derived_classification_study` example. `auslander classify gentle`
runs it with the same flags.

| Command | before | after |
| --- | ---: | ---: |
| study, `--walk-vertices 16` | 106.29 s | 24.39 s |
| study, `--walk-vertices 16 --through-silting` | 86.87 s | 17.80 s |
| `auslander verify` on `derived-atlas-f2-n3.json` | 0.375 s | 0.094 s |

Both trees write the same study records, apart from the `nanoseconds`
fields, and the same atlas bytes.

```sh
cargo run --release -p auslander --bin auslander -- \
  classify gentle --vertices 4 --field 2 --walk-vertices 16
cargo run --release -p auslander --bin auslander -- \
  classify gentle --vertices 4 --field 2 --walk-vertices 16 --through-silting
cargo run --release -p auslander --bin auslander -- \
  verify crates/auslander/artifacts/research/derived-atlas-f2-n3.json
```
