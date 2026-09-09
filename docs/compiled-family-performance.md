# Compiled-family performance

This record compares compiled and generic paths on identical fibers. It uses
the release benchmark harness in optimized mode. Each case calibrates its own
repetition count. The reported value is the best of seven trials.

The raw record is
[`family-benchmark-2026-09-09.tsv`](../crates/auslander/artifacts/research/family-benchmark-2026-09-09.tsv).
It ran with the `rust-toolchain.toml` pin on an Intel Core i9-13900KS under
Linux `x86_64-unknown-linux-gnu`. Compiled Hom for A16 is the
`Hom fixed-interface modules` row.

| Case | Compiled ns/op | Generic ns/op |
| --- | ---: | ---: |
| Square diagonal specialize, dimension 2 | 214.4 | 225.4 |
| Square diagonal specialize, dimension 4 | 326.2 | 345.6 |
| Square diagonal specialize, dimension 8 | 883.4 | 945.8 |
| Square diagonal Hom, dimension 2 | 2137.8 | 2144.6 |
| Square diagonal Hom, dimension 4 | 10523.6 | 9754.3 |
| Square diagonal Hom, dimension 8 | 78268.8 | 73998.3 |
| A16 interface width 2 Hom modules | 49692.3 | 96228.3 |
| A16 interface width 4 Hom modules | 101180.5 | 90068.1 |
| A16 interface width 8 Hom modules | 286284.8 | 89865.2 |

The small square has no interface-elimination advantage. Its compiled and
generic Hom paths stay close. The compiled specialization path is ahead at
all three dimensions, while compiled Hom is ahead at dimension 2 and behind
at dimensions 4 and 8. The A16 plan removes the fixed outer equations once
and reduces only the interface system for each pair. Width 2 is the case where
the compiled modules path is ahead in this record. Widths 4 and 8 are behind.

Compile and setup costs from the same TSV are not per-fiber times:

| Setup case | ns/op |
| --- | ---: |
| Square family compile, dimension 2 | 910.7 |
| Square family compile, dimension 4 | 3949.2 |
| Square family compile, dimension 8 | 22426.2 |
| A16 family compile, width 2 | 13858.4 |
| A16 family compile, width 4 | 13141.9 |
| A16 family compile, width 8 | 13092.3 |
| A16 interface-plan compile, width 2 | 196735.6 |
| A16 interface-plan compile, width 4 | 194722.3 |
| A16 interface-plan compile, width 8 | 158095.2 |

Compilation does not imply a speedup on every shape. It helps when the fixed
block removes enough global work to repay assembly and lifting costs. These
numbers describe one machine and one benchmark run. They are not a
platform-independent performance bound.

The record command was:

```sh
cargo bench -p auslander --bench perf --profile release -- --group family --trials 7
```
