// One verification runs at a time. An accepted derived atlas also gets a
// class table read from its own bytes.

const STATES = {
  verified: ["Verified", "Every claim in the artifact replayed."],
  "verified-cut": [
    "Verified cut",
    "Every stored claim replayed. The artifact records a cut or an active prefix, not a complete result.",
  ],
  stopped: [
    "Stopped",
    "A verifier ceiling stopped the replay. The artifact is neither accepted nor rejected.",
  ],
  rejected: ["Rejected", "The verifier rejected the artifact."],
  failed: ["Failed", "The verifier trapped. This is a defect in the verifier. Report the file that caused it."],
  unavailable: ["Unavailable", "The WebAssembly module did not load. Reload the page. If it fails again, rebuild the module with web/build.sh."],
  cancelled: ["Cancelled", "The replay was cancelled before it finished."],
};

const element = (id) => document.getElementById(id);
const drop = element("drop");
const fileInput = element("file");
const paste = element("paste");
const verifyPaste = element("verify-paste");
const cancel = element("cancel");
const result = element("result");

let worker = null;
let running = null;
let nextId = 0;

function startWorker() {
  worker = new Worker(new URL("worker.js", import.meta.url), { type: "module" });
  worker.onmessage = (event) => {
    if (running === null || event.data.id !== running.id) {
      return;
    }
    const { source } = running;
    running = null;
    setBusy(false);
    render(source, event.data.result, event.data.milliseconds);
  };
}

function setBusy(busy) {
  cancel.hidden = !busy;
  verifyPaste.disabled = busy;
  fileInput.disabled = busy;
  drop.classList.toggle("busy", busy);
}

function submit(source, bytes) {
  if (running !== null) {
    return;
  }
  running = { id: nextId++, source };
  setBusy(true);
  showRunning(source);
  worker.postMessage({ id: running.id, bytes: bytes.buffer }, [bytes.buffer]);
}

function formatBytes(count) {
  return count === 1 ? "1 byte" : `${count.toLocaleString("en-US")} bytes`;
}

function showRunning(source) {
  result.hidden = false;
  result.dataset.state = "running";
  element("badge").textContent = "Verifying";
  element("explanation").textContent = "The replay runs in a worker. Cancel stops it.";
  element("source").textContent = `${source.name}, ${formatBytes(source.size)}`;
  for (const id of ["kind", "fingerprint", "time"]) {
    element(id).textContent = "";
  }
  element("summary").hidden = true;
  element("error").hidden = true;
  hideAtlas();
}

function render(source, outcome, milliseconds) {
  const [label, explanation] = STATES[outcome.status] ?? [outcome.status, ""];
  result.dataset.state = outcome.status;
  element("badge").textContent = label;
  element("explanation").textContent = explanation;
  element("source").textContent = `${source.name}, ${formatBytes(source.size)}`;
  element("kind").textContent = outcome.kind ?? "none";
  element("fingerprint").textContent = outcome.fingerprint ?? "none";
  element("time").textContent =
    milliseconds === undefined ? "" : `${Math.round(milliseconds).toLocaleString("en-US")} ms`;
  const atlas = outcome.kind === ATLAS_KIND && ACCEPTED.has(outcome.status);
  renderSummary(outcome.summary ?? [], atlas ? ATLAS_LABELS : {});
  const error = element("error");
  error.hidden = !outcome.error;
  error.textContent = outcome.error ?? "";
  hideAtlas();
  if (atlas) {
    renderAtlas(source, outcome);
  }
}

function renderSummary(rows, labels) {
  const table = element("summary");
  const body = table.tBodies[0];
  body.replaceChildren();
  for (const [label, value] of rows) {
    const row = body.insertRow();
    const header = document.createElement("th");
    header.scope = "row";
    header.textContent = labels[label] ?? label;
    row.append(header);
    row.insertCell().textContent = label === "field" && labels === ATLAS_LABELS ? `F_${value}` : value;
  }
  table.hidden = rows.length === 0;
}

const ATLAS_KIND = "derived-atlas-v1";
const ACCEPTED = new Set(["verified", "verified-cut"]);
const ATLAS_LABELS = {
  field: "Field",
  members: "Algebras",
  classes: "Classes",
  merges: "Merges",
  separations: "Separated pairs",
  unresolved: "Unresolved pairs",
  status: "Status",
};
const INVARIANT_NAMES = {
  vertex_count: "vertex count",
  cartan_determinant: "Cartan determinant",
  cartan_factors: "invariant factors of C",
  symmetric_factors: "invariant factors of C + C^T",
  skew_factors: "invariant factors of C - C^T",
  cartan_pencil: "Cartan pencil",
  aag_function: "AAG function",
  winding_class: "winding class",
  hochschild_dimensions: "Hochschild dimensions",
  center_dimension: "center dimension",
};
const WINDING = ["planar", "gcd", "odd", "even", "Arf"];

// Each atlas render gets a number, so a slow read of an earlier input
// cannot overwrite the rows of a later one.
let atlasRender = 0;

function hideAtlas() {
  atlasRender += 1;
  element("atlas").hidden = true;
}

// The verifier accepted these exact bytes, and a canonical atlas has no
// duplicate or unknown keys, so the parsed rows are the verified rows. An
// integer beyond 2^53 keeps its digits where the browser exposes the source
// text of a number.
function parseAtlas(text) {
  return JSON.parse(text, (key, value, context) => {
    if (typeof value === "number" && !Number.isSafeInteger(value)) {
      return context?.source ?? "(beyond 2^53)";
    }
    return value;
  });
}

async function renderAtlas(source, outcome) {
  const render = atlasRender;
  let atlas;
  try {
    atlas = parseAtlas(await source.read());
  } catch {
    return;
  }
  if (render !== atlasRender) {
    return;
  }
  element("atlas-lede").textContent = atlasLede(atlas);
  const separations = element("atlas-separations");
  separations.textContent = separationCounts(atlas);
  separations.hidden = separations.textContent === "";
  renderClasses(atlas);
  renderUnresolved(atlas);
  element("atlas").hidden = false;
}

function plural(count, one, many) {
  return `${count.toLocaleString("en-US")} ${count === 1 ? one : many}`;
}

function atlasLede(atlas) {
  const members = plural(atlas.members.length, "algebra", "algebras");
  const classes = plural(atlas.classes.length, "class", "classes");
  const head = `${members} over F_${atlas.field} fall into ${classes} up to derived equivalence.`;
  if (atlas.unresolved.length === 0) {
    return `${head} Every pair of classes is separated by a recomputed invariant.`;
  }
  const open = plural(atlas.unresolved.length, "pair of classes is", "pairs of classes are");
  return `${head} ${open} unresolved: no merge joins them and no finished invariant separates them.`;
}

function separationCounts(atlas) {
  if (atlas.separations.length === 0) {
    return "";
  }
  const counts = new Map();
  for (const separation of atlas.separations) {
    counts.set(separation.kind, (counts.get(separation.kind) ?? 0) + 1);
  }
  const order = Object.keys(INVARIANT_NAMES);
  const rank = (kind) => (order.includes(kind) ? order.indexOf(kind) : order.length);
  const parts = [...counts]
    .sort(([left], [right]) => rank(left) - rank(right))
    .map(([kind, count]) => `${INVARIANT_NAMES[kind] ?? kind} ${count}`);
  return `Separated pairs by the first invariant that differs: ${parts.join(", ")}.`;
}

function reading(row) {
  if (row === undefined) {
    return "none";
  }
  if (row.reading === "not_applicable") {
    return "not applicable";
  }
  if (row.reading === "stopped") {
    return `stopped (${row.stop})`;
  }
  const value = row.value;
  switch (row.kind) {
    case "aag_function": {
      const pairs = [];
      for (let index = 0; index + 1 < value.length; index += 2) {
        pairs.push(`(${value[index]}, ${value[index + 1]})`);
      }
      return `[${pairs.join(", ")}]`;
    }
    case "winding_class": {
      const name = WINDING[value[0]] ?? `class ${value[0]}`;
      return value.length > 1 ? `${name} ${value.slice(1).join(", ")}` : name;
    }
    default:
      return value.join(", ");
  }
}

const CLASS_COLUMNS = [
  ["vertex_count", "n"],
  ["cartan_determinant", "det C"],
  ["aag_function", "AAG"],
  ["winding_class", "winding"],
  ["hochschild_dimensions", "dim HH"],
];

function renderClasses(atlas) {
  const body = element("atlas-classes").tBodies[0];
  body.replaceChildren();
  atlas.classes.forEach((entry, index) => {
    const row = body.insertRow();
    labeled(row, "Class", String(index));
    labeled(row, "Members", entry.members.join(", "));
    const readings = new Map(atlas.invariants[entry.members[0]].map((r) => [r.kind, r]));
    const cell = labeled(row, "Invariants", "");
    for (const [kind, label] of CLASS_COLUMNS) {
      const item = document.createElement("span");
      item.className = "invariant";
      const name = document.createElement("span");
      name.className = "name";
      name.textContent = label;
      item.append(name, ` ${reading(readings.get(kind))}`);
      // The space keeps the items apart in copied text and for screen readers.
      cell.append(item, " ");
    }
  });
  element("atlas-classes-count").textContent = `Classes (${atlas.classes.length})`;
}

function renderUnresolved(atlas) {
  const box = element("atlas-unresolved-box");
  const body = element("atlas-unresolved").tBodies[0];
  body.replaceChildren();
  for (const pair of atlas.unresolved) {
    const row = body.insertRow();
    const [left, right] = pair.classes;
    labeled(row, "Classes", `${left} and ${right}`);
    const first = (index) => atlas.classes[index].members[0];
    labeled(row, "Representatives", `${first(left)} and ${first(right)}`);
    const walks = pair.walks.map((index) => {
      const walk = atlas.walks[index];
      const { kind, ...fields } = walk.stop;
      const detail = Object.entries(fields).map(([name, value]) => `${name} ${value}`);
      const stop = detail.length === 0 ? kind : `${kind} (${detail.join(", ")})`;
      return `member ${walk.member}: ${stop}`;
    });
    const label = "Recorded walk stops (not replayed)";
    labeled(row, label, walks.length === 0 ? "no walk" : walks.join("; "));
  }
  element("atlas-unresolved-count").textContent = `Unresolved pairs (${atlas.unresolved.length})`;
  box.hidden = atlas.unresolved.length === 0;
}

function labeled(row, label, text) {
  const cell = row.insertCell();
  cell.dataset.label = label;
  cell.textContent = text;
  return cell;
}

async function submitFile(file) {
  const bytes = new Uint8Array(await file.arrayBuffer());
  submit({ name: file.name, size: file.size, read: () => file.text() }, bytes);
}

drop.addEventListener("dragover", (event) => {
  event.preventDefault();
  drop.classList.add("over");
});
drop.addEventListener("dragleave", () => drop.classList.remove("over"));
drop.addEventListener("drop", (event) => {
  event.preventDefault();
  drop.classList.remove("over");
  const [file] = event.dataTransfer.files;
  if (file) {
    submitFile(file);
  }
});
drop.addEventListener("click", (event) => {
  // The label and the input already open the picker themselves.
  if (!event.target.closest("label, input")) {
    fileInput.click();
  }
});
drop.addEventListener("keydown", (event) => {
  if (event.key === "Enter" || event.key === " ") {
    event.preventDefault();
    fileInput.click();
  }
});
fileInput.addEventListener("change", () => {
  const [file] = fileInput.files;
  fileInput.value = "";
  if (file) {
    submitFile(file);
  }
});
verifyPaste.addEventListener("click", () => {
  const text = paste.value;
  const bytes = new TextEncoder().encode(text);
  submit({ name: "pasted text", size: bytes.length, read: async () => text }, bytes);
});
cancel.addEventListener("click", () => {
  if (running === null) {
    return;
  }
  const { source } = running;
  worker.terminate();
  running = null;
  startWorker();
  setBusy(false);
  render(source, { status: "cancelled" });
});

startWorker();
