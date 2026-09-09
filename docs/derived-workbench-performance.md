# Derived workbench performance record

The [classical tilting component record](classical-tilting-performance.md)
contains target recovery, certificate, and strict-transport measurements.

This record measures the fixed acceptance fixtures over F_5. It uses the
machine and toolchain below:

```text
Linux 7.1.9-arch1-2 x86_64
13th Gen Intel(R) Core(TM) i9-13900KS
32 logical CPUs, 2 threads per core
rustc 1.92.0
cargo 1.92.0
```

Elapsed samples use the release profile. The harness calibrates each case,
runs five trials, and reports the best trial. These values describe this
machine. Tests gate deterministic work counts, not elapsed time.

```text
group	case	ns_per_op	reps	trials
workbench	replace_perfect pd2-simple-f5	37075.7	332	5
workbench	derived_hom pd2-simple-f5	44662.1	343	5
workbench	discover_equivalences a2-f5	371713.1	44	5
workbench	present_complex_target a2-f5	186450.8	91	5
workbench	verify artifact a2-f5	288181.3	63	5
```

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
