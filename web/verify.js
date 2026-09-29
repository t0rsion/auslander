// The JavaScript side of the `auslander-wasm` ABI. `worker.js` and
// `parity.mjs` both call `verifyBytes`, so the parity run tests the page's
// own glue code.

/**
 * Verifies one portable value in a fresh instance of the compiled module.
 *
 * A fresh instance per call means a trap in one verification cannot leave
 * state behind for the next. Returns the parsed result object with the
 * members `status`, `kind`, `fingerprint`, `summary`, and `error`.
 *
 * @param {WebAssembly.Module} module the compiled `auslander_wasm.wasm`
 * @param {Uint8Array} input the raw bytes of the value
 */
export async function verifyBytes(module, input) {
  const instance = await WebAssembly.instantiate(module, {});
  const { memory, alloc, verify } = instance.exports;
  // Pointers cross the ABI as i32, so `>>> 0` reads them as unsigned.
  const pointer = alloc(input.length) >>> 0;
  new Uint8Array(memory.buffer, pointer, input.length).set(input);
  const result = verify(pointer, input.length) >>> 0;
  // `verify` may grow memory, which detaches earlier views of the buffer.
  const length = new DataView(memory.buffer).getUint32(result, true);
  const text = new TextDecoder().decode(
    new Uint8Array(memory.buffer, result + 4, length),
  );
  return JSON.parse(text);
}
