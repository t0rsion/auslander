# Browser verifier

`web/` holds a static page that replays one portable value in the
browser. The page runs the Rust verifier of `auslander verify`, compiled to
WebAssembly by the `auslander-wasm` crate. It loads no external resource and
uploads nothing.

## Build

The build needs the `wasm32-unknown-unknown` target:

```sh
rustup target add wasm32-unknown-unknown
web/build.sh
```

`web/build.sh` builds `auslander-wasm` with the `wasm` profile
(`opt-level = "s"`, LTO, one codegen unit, stripped). It copies
`auslander_wasm.wasm` next to `index.html` and prints its byte count. The
module imports nothing. `auslander-wasm` depends only on `auslander`.

## Run locally

Serve `web/` over HTTP:

```sh
cd web
python -m http.server 8000
```

Then open `http://localhost:8000/`. A browser does not start a module worker
or fetch the `.wasm` file from a `file://` URL, so the page needs a server.
Any static server works.

Choose a file, drop one on the page, or paste the JSON text. The page shows
the status, the kind, the fingerprint, and a summary table for an accepted
value. For a stopped or rejected value it shows the exact verifier message.

## What is checked

`page.js` sends the file bytes to `worker.js`. The worker calls `verify` in
a fresh instance of the module, through the same `verify.js` glue that the
parity run uses. `verify` runs `auslander::artifact::verify_artifact` with
`ArtifactLimits::default()`. That function reads the header with the
portable cursor, selects the kind from `ArtifactKind::ALL`, and runs the
parser and verifier of that kind. The page accepts exactly the kinds that
`auslander verify` accepts.

| Status | Meaning |
| --- | --- |
| `verified` | Every claim replayed, and the value claims a complete result. |
| `verified-cut` | Every stored claim replayed. The value is a cut or active prefix. |
| `stopped` | A verifier ceiling stopped replay. The value is neither accepted nor rejected. |
| `rejected` | The header or the verifier of the kind rejected the value. |
| `failed` | The module trapped. A trap is a panic, which is a verifier defect. |

The module exports `alloc(len)`, `dealloc(ptr, len)`, and `verify(ptr, len)`.
`verify` returns a pointer to a 4-byte little-endian length and that many
bytes of UTF-8 JSON with the members `status`, `kind`, `fingerprint`,
`summary`, and `error`. `crates/auslander-wasm/src/lib.rs` documents the
contract.

## Parity with the native verifier

`web/parity.mjs` runs `auslander verify` and the WebAssembly module on the
same bytes. Both must report the same status. An accepted value must have the
same kind and fingerprint, and a stopped or rejected value the same message.
For each value that is not rejected, a copy with its last digit changed must
be rejected by both with the same message.

```sh
cargo build -p auslander --bin auslander
cargo run -p auslander-wasm --example parity_corpus -- target/parity-corpus
node web/parity.mjs target/debug/auslander web/auslander_wasm.wasm \
  crates/auslander/artifacts target/parity-corpus
```

The `parity_corpus` example writes one value per kind and status: verified,
verified cut, and stopped. CI runs the same steps.

## Derived atlas

The page replays a `derived-atlas-v1` value like any other kind. It
rebuilds every member, recomputes every invariant, and replays every merge,
as section 5 of the [classification contract](derived-classification.md)
describes. The `parity_corpus` example writes seven atlases: the connected
gentle algebras over `F_2` with 2 and with 3 vertices and over `F_3` with 2
vertices (`verified`), a family with one unresolved pair (`verified-cut`),
and the 2-vertex atlas over `F_2` with `max_hom_spaces` above its ceiling
(`stopped`). Two more 2-vertex atlases store walk limits of 8589934592: one
verifies, and one also stores a bar tuple limit of 8589934592, above its
ceiling (`stopped`).

For an accepted atlas, the page also shows a class table. Each row lists the
members of one class and five readings of its first member: the vertex
count, the Cartan determinant, the AAG function, the winding class, and the
Hochschild dimensions. The page parses these rows from the file only after
the verifier accepts its exact bytes. A canonical atlas has no duplicate or
unknown keys, so the parsed rows are the verified rows. A second table lists
each unresolved pair with the stops of its walks. Replay does not rerun a
walk, so these stops are the recorded values, and the column header says
`not replayed`. The WebAssembly result carries only the counts, so the rows
come from the file.

Verification time, median of 5 runs on one development machine on
2026-09-29. The native column runs `target/release/auslander verify` in a
new process each time. The WebAssembly column runs the `wasm` profile module
in Node 26 through `verify.js`. The byte counts are those of the current
files. The times predate the removal of the discovery work limit, which took
20 bytes out of each atlas.

| Atlas | Bytes | Native | WebAssembly |
| --- | --- | --- | --- |
| `derived-atlas-f2-n3.json`, at most 3 vertices | 229608 | 339 ms | 555 ms |
| parity corpus, 3 vertices | 185982 | 343 ms | 553 ms |
| parity corpus, 2 vertices | 15945 | 5 ms | 5 ms |

## Limits

- The page runs the native verifier code with its default limits. It has no
  control to raise or lower them.
- Replay runs on one thread in one Web Worker. A long replay does not block
  the page. Cancel terminates the worker. The verifier itself does not see
  the cancellation.
- `wasm32` has a 32-bit `usize` and at most 4 GiB of memory. The page reads
  the whole file, then copies it into module memory.
- Ceilings and work counters are `u64` on every host. The page reads the
  same values as the native verifier, including the default
  `HomologicalStreamBudget` of `u64::MAX` and the walk and bar limits of a
  derived atlas.
- An index, a dimension, or a degree above 4294967295 is rejected with
  `integer exceeds usize`. The default native ceilings on these values are
  at most 1000000, so the native verifier rejects them too, with a limit
  message. A Hom or Ext dimension in a row has no ceiling of its own: the
  native verifier replays it, and the page rejects it above 4294967295.
- The fingerprint is FNV-1a. It detects accidental changes. It does not
  authenticate the file.
