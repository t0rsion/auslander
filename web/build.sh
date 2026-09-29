#!/bin/sh
# Builds the WebAssembly verifier and copies it next to index.html.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
target=${CARGO_TARGET_DIR:-$root/target}
cargo build --manifest-path "$root/Cargo.toml" -p auslander-wasm --lib \
  --target wasm32-unknown-unknown --profile wasm
cp "$target/wasm32-unknown-unknown/wasm/auslander_wasm.wasm" "$root/web/auslander_wasm.wasm"
wc -c "$root/web/auslander_wasm.wasm"
