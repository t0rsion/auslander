// Checks that the WebAssembly verifier and the native `auslander verify`
// agree on every JSON file under the given paths.
//
// Usage: node web/parity.mjs AUSLANDER_BINARY AUSLANDER_WASM PATH...
//
// For each file both sides must report the same status. An accepted value
// must have the same kind and fingerprint; a stopped or rejected value must
// have the same message. For each file that is not rejected, one tampered
// copy (its last ASCII digit changed) must be rejected by both sides with
// the same message. For each file with an unquoted integer above
// 4294967295, the `wide` column shows the largest one, and one widened
// copy (a `0` appended to the first such integer) must be rejected by both
// sides with the same message. The exit status is 1 on any disagreement.

import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, join, relative } from "node:path";

import { verifyBytes } from "./verify.js";

const STOPPED = "artifact verification stopped: ";
const U32_MAX = 4294967295n;

// The unquoted digit runs of a JSON text, each with the offset past its last digit.
function integers(bytes) {
  const found = [];
  let quoted = false;
  let escaped = false;
  let start = -1;
  for (let index = 0; index <= bytes.length; index += 1) {
    const byte = index < bytes.length ? bytes[index] : 0x20;
    const digit = byte >= 0x30 && byte <= 0x39;
    if (!quoted && digit) {
      start = start < 0 ? index : start;
      continue;
    }
    if (start >= 0) {
      const text = new TextDecoder().decode(bytes.subarray(start, index));
      found.push({ end: index, value: BigInt(text) });
      start = -1;
    }
    if (escaped) {
      escaped = false;
    } else if (quoted && byte === 0x5c) {
      escaped = true;
    } else if (byte === 0x22) {
      quoted = !quoted;
    }
  }
  return found;
}

function wideIntegers(bytes) {
  return integers(bytes).filter((entry) => entry.value > U32_MAX);
}

function jsonFiles(path) {
  if (!statSync(path).isDirectory()) {
    return [path];
  }
  return readdirSync(path)
    .sort()
    .flatMap((name) => {
      const child = join(path, name);
      return statSync(child).isDirectory() || name.endsWith(".json") ? jsonFiles(child) : [];
    });
}

function native(binary, path) {
  const run = spawnSync(binary, ["verify", path], { encoding: "utf8" });
  if (run.status === 0) {
    const [status, kind, fingerprint] = run.stdout.split("\n")[0].split(" ");
    return { status, kind, fingerprint, error: null };
  }
  const message = run.stderr.trim().replace(/^auslander: /, "");
  const status = message.startsWith(STOPPED) ? "stopped" : "rejected";
  return { status, kind: null, fingerprint: null, error: message };
}

function agree(left, right) {
  if (left.status !== right.status) {
    return false;
  }
  if (left.status.startsWith("verified")) {
    return left.kind === right.kind && left.fingerprint === right.fingerprint;
  }
  return left.error === right.error;
}

function tamper(bytes) {
  const copy = Uint8Array.from(bytes);
  for (let index = copy.length - 1; index >= 0; index -= 1) {
    if (copy[index] >= 0x30 && copy[index] <= 0x39) {
      copy[index] = copy[index] === 0x30 ? 0x31 : 0x30;
      return copy;
    }
  }
  return null;
}

async function tamperedAgree(binary, module, scratch, bytes) {
  const tampered = tamper(bytes);
  if (tampered === null) {
    return "no digit";
  }
  const path = join(scratch, "tampered.json");
  writeFileSync(path, tampered);
  const left = native(binary, path);
  const right = await verifyBytes(module, tampered);
  return left.status === "rejected" && agree(left, right) ? "rejected" : "MISMATCH";
}

async function widenedAgree(binary, module, scratch, bytes, wide) {
  if (wide.length === 0) {
    return "n/a";
  }
  const { end } = wide[0];
  const widened = new Uint8Array(bytes.length + 1);
  widened.set(bytes.subarray(0, end), 0);
  widened[end] = 0x30;
  widened.set(bytes.subarray(end), end + 1);
  const path = join(scratch, "widened.json");
  writeFileSync(path, widened);
  const left = native(binary, path);
  const right = await verifyBytes(module, widened);
  return left.status === "rejected" && agree(left, right) ? "rejected" : "MISMATCH";
}

async function main() {
  const [binary, wasm, ...paths] = process.argv.slice(2);
  if (!binary || !wasm || paths.length === 0) {
    console.error("usage: node web/parity.mjs AUSLANDER_BINARY AUSLANDER_WASM PATH...");
    process.exit(2);
  }
  const module = await WebAssembly.compile(readFileSync(wasm));
  const scratch = mkdtempSync(join(tmpdir(), "auslander-parity-"));
  const rows = [];
  let failures = 0;
  for (const file of paths.flatMap(jsonFiles)) {
    const bytes = readFileSync(file);
    const left = native(binary, file);
    const right = await verifyBytes(module, bytes);
    const same = agree(left, right);
    const tampered =
      left.status === "rejected" ? "n/a" : await tamperedAgree(binary, module, scratch, bytes);
    const wide = wideIntegers(bytes);
    const largest = wide.reduce((max, entry) => (entry.value > max ? entry.value : max), 0n);
    const widened = await widenedAgree(binary, module, scratch, bytes, wide);
    failures +=
      Number(!same) +
      Number(tampered === "MISMATCH" || tampered === "no digit") +
      Number(widened === "MISMATCH");
    rows.push({
      file: relative(process.cwd(), file) || basename(file),
      status: right.status,
      kind: right.kind ?? "",
      fingerprint: right.fingerprint ?? "",
      parity: same ? "same" : `MISMATCH native=${JSON.stringify(left)}`,
      tampered,
      wide: largest === 0n ? "" : largest.toString(),
      widened,
    });
  }
  rmSync(scratch, { recursive: true, force: true });
  console.table(rows);
  const wideFiles = rows.filter((row) => row.wide !== "").length;
  const summary = `${rows.length} files, ${wideFiles} with an integer above ${U32_MAX}`;
  console.log(`${summary}, ${failures} disagreements`);
  process.exit(failures === 0 ? 0 : 1);
}

await main();
