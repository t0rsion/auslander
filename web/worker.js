// Runs verifications off the page thread, so a long replay never blocks
// the page. The page cancels a run by terminating this worker.

import { verifyBytes } from "./verify.js";

let compiled = null;

function loadModule() {
  if (compiled === null) {
    const url = new URL("auslander_wasm.wasm", import.meta.url);
    compiled = fetch(url)
      .then((response) => {
        if (!response.ok) {
          throw new Error(`cannot load ${url.pathname}: HTTP ${response.status}`);
        }
        return response.arrayBuffer();
      })
      .then((bytes) => WebAssembly.compile(bytes));
    compiled.catch(() => {
      compiled = null;
    });
  }
  return compiled;
}

async function handle(input) {
  let module;
  try {
    module = await loadModule();
  } catch (error) {
    return { status: "unavailable", error: String(error.message ?? error) };
  }
  try {
    return await verifyBytes(module, input);
  } catch (error) {
    // A Rust panic reaches JavaScript as a WebAssembly trap.
    return { status: "failed", error: String(error.message ?? error) };
  }
}

self.onmessage = async (event) => {
  const { id, bytes } = event.data;
  const started = performance.now();
  const result = await handle(new Uint8Array(bytes));
  self.postMessage({ id, result, milliseconds: performance.now() - started });
};
