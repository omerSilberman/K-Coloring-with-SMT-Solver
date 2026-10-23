"use strict";

const $ = id => document.getElementById(id);
const esc = s => String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
const store = {
  get(key) { try { return localStorage.getItem(key); } catch (e) { return null; } },
  set(key, value) { try { localStorage.setItem(key, value); } catch (e) { /* private mode */ } },
};

const PAGE = 150;  // formulas rendered per "show more"
const PALETTE = ["#4E79A7", "#F28E2B", "#E15759", "#59A14F", "#EDC948", "#B07AA1", "#76B7B2", "#FF9DA7",
                 "#9C755F", "#86BCB6", "#D37295", "#8CD17D", "#F1CE63", "#A0CBE8", "#FFBE7D", "#BAB0AC"];
const colorFor = i => (i < PALETTE.length ? PALETTE[i] : `hsl(${(i * 137.508) % 360} 60% 55%)`);

const HINTS = {
  "NLRA-SIN": "cvc5 proves UNSAT here but cannot return SAT models (the roots are irrational). Try the dReal version.",
  "NLRA-COS": "cvc5 proves UNSAT here but cannot return SAT models (the roots are irrational). Try the dReal version.",
  "NLRA-SINCOS": "cvc5 proves UNSAT here but cannot return SAT models (the roots are irrational). Try the dReal version.",
  "NLRA-SINPI": "Usually times out with cvc5 (π·x is nonlinear). Try the dReal version.",
  "FF-PRIME": "Only accepts a prime K.",
  "STR-LEX": "Only supports K ≤ 50.",
  "IDL": "Colors are node − zero; the model shows the shifted values.",
};
const GENERIC_HINT = "Theory-independent: the same encoding runs over any element theory.";
const DREAL_HINT = "Solved by dReal (delta-complete). A delta-SAT box is rounded to the exact roots and checked against every edge.";

function family(name) {
  if (/^(LIA|IDL|INT-)/.test(name)) return "Integer arithmetic";
  if (/^BV/.test(name)) return "Bit-vectors";
  if (name === "FP") return "Floating point";
  if (/^NLRA/.test(name)) return "Real arithmetic";
  if (/^FF-/.test(name)) return "Finite fields";
  if (/^(LIST-|PEANO$|UF$)/.test(name)) return "Datatypes & uninterpreted functions";
  if (/^STR/.test(name)) return "Strings";
  if (/^ARR/.test(name)) return "Arrays";
  return "Other";
}

const state = {
  graphs: [], solvers: null, graph: null, graphData: null,
  element: {}, es: null, running: false, startTime: 0, timerId: 0,
  asserts: [], totalAsserts: 0, limit: PAGE, rendered: 0, pendingRender: false,
  mode: store.get("mode") || "pretty", result: null, highlight: null,
  labels: store.get("labels") === "value" ? "value" : "node",
};

// ===========================================================================
// Setup
// ===========================================================================
async function init() {
  let options;
  try {
    options = await (await fetch("/api/options")).json();
  } catch (e) {
    showErrors(["Could not reach the server. Is kcolor_gui.py still running?"]);
    return;
  }
  state.graphs = options.graphs;
  state.solvers = options.solvers;
  try { state.element = JSON.parse(store.get("elements") || "{}"); } catch (e) { state.element = {}; }

  if (state.solvers.error) showErrors([state.solvers.error]);
  buildSolverList();
  renderGraphList();

  const saved = store.get("graph");
  const fallback = state.graphs.find(g => g.path.endsWith("DIMACS/myciel3.col")) || state.graphs[0];
  selectGraph((state.graphs.find(g => g.path === saved) || fallback)?.path);
  $("timeout").value = store.get("timeout") || "";
  setMode(state.mode);

  $("graph-filter").addEventListener("input", renderGraphList);
  $("graph").addEventListener("change", e => selectGraph(e.target.value));
  $("solver").addEventListener("change", onSolverChange);
  $("k").addEventListener("input", updateKReset);
  $("k").addEventListener("keydown", e => { if (e.key === "Enter") run(); });
  $("k-reset").addEventListener("click", () => { $("k").value = state.graph.k; updateKReset(); });
  $("timeout").addEventListener("change", () => store.set("timeout", $("timeout").value));
  $("run").addEventListener("click", run);
  $("stop").addEventListener("click", stop);
  $("formula-filter").addEventListener("input", () => { state.limit = PAGE; rebuildFormulas(); });
  $("formula-more").addEventListener("click", () => { state.limit += PAGE; renderMoreFormulas(); });
  document.querySelectorAll("#formula-mode button").forEach(b => b.addEventListener("click", () => setMode(b.dataset.mode)));
  $("node-filter").addEventListener("input", renderNodeGrid);
  document.querySelectorAll("#label-mode button").forEach(b => b.addEventListener("click", () => setLabels(b.dataset.labels)));
  document.querySelectorAll("#theme-switch button").forEach(b => b.addEventListener("click", () => setTheme(b.dataset.theme)));
  setLabels(state.labels);
  setTheme(store.get("theme") || "auto");
}

// "light" / "dark" pin the theme; "auto" follows the system setting
function setTheme(theme) {
  const root = document.documentElement;
  root.classList.add("theme-switching");
  requestAnimationFrame(() => requestAnimationFrame(() => root.classList.remove("theme-switching")));
  if (theme === "light" || theme === "dark") document.documentElement.dataset.theme = theme;
  else { delete document.documentElement.dataset.theme; theme = "auto"; }
  store.set("theme", theme);
  document.querySelectorAll("#theme-switch button").forEach(b => b.classList.toggle("on", b.dataset.theme === theme));
}

// Label nodes (graph and node list) by node number or by the value the solver assigned
function setLabels(labels) {
  state.labels = labels;
  store.set("labels", labels);
  document.querySelectorAll("#label-mode button").forEach(b => b.classList.toggle("on", b.dataset.labels === labels));
  if (state.result?.colors) { drawGraph(state.result); renderNodeGrid(); }
}

function renderGraphList() {
  const select = $("graph");
  const filter = $("graph-filter").value.trim().toLowerCase();
  const current = state.graph?.path;
  select.innerHTML = "";
  let group = null, folder = null;
  for (const g of state.graphs) {
    if (filter && !g.path.toLowerCase().includes(filter)) continue;
    if (g.folder !== folder) {
      folder = g.folder;
      group = document.createElement("optgroup");
      group.label = folder;
      select.appendChild(group);
    }
    const option = document.createElement("option");
    option.value = g.path;
    option.textContent = `${g.name}   ·  ${g.nodes} nodes  ·  ${g.edges} edges${g.k ? `  ·  K=${g.k}` : ""}`;
    option.selected = g.path === current;
    group.appendChild(option);
  }
}

function selectGraph(path) {
  const g = state.graphs.find(x => x.path === path);
  if (!g) return;
  state.graph = g;
  store.set("graph", path);
  const list = $("graph");
  [...list.options].forEach(o => { o.selected = o.value === path; });
  const option = list.selectedOptions[0];
  if (option) list.scrollTop = option.offsetTop - list.clientHeight / 2;
  const kChip = g.k ? `<span class="chip">${g.status === "OPTIMAL" ? "optimal" : "known"} K <b>${g.k}</b></span>`
                    : `<span class="chip">no known K</span>`;
  $("graph-info").innerHTML = `<span class="chip"><b>${g.nodes}</b> nodes</span><span class="chip"><b>${g.edges}</b> edges</span>${kChip}`;
  $("k").value = g.k ?? "";
  updateKReset();
  $("graph-title").textContent = g.name;
  state.graphData = null;
  if (!state.running) clearResult();
  drawGraph();
  fetch(`/api/graph?path=${encodeURIComponent(path)}`).then(r => r.json()).then(data => {
    if (state.graph !== g) return;
    state.graphData = data;
    drawGraph(state.result?.graph === g.path ? state.result : null);
  });
}

function updateKReset() {
  const g = state.graph, button = $("k-reset");
  const differs = g?.k && String(g.k) !== $("k").value;
  button.hidden = !differs;
  if (differs) button.textContent = `Reset to the optimal K = ${g.k}`;
}

function buildSolverList() {
  const select = $("solver"), s = state.solvers;
  if (!s || s.error) return;
  const groups = {};
  for (const name of s.specific) (groups[family(name)] ||= []).push(name);
  const add = (label, entries) => {
    const group = document.createElement("optgroup");
    group.label = label;
    for (const [value, text] of entries) {
      const o = document.createElement("option");
      o.value = value; o.textContent = text;
      group.appendChild(o);
    }
    select.appendChild(group);
  };
  for (const [label, names] of Object.entries(groups)) add(label, names.map(n => [`cvc5:${n}`, n]));
  add("Theory-independent (any elements)", s.generic.map(n => [`gen:${n}`, `${n}-‹elem›`]));
  if (s.dreal.length) add("dReal (delta-complete)", s.dreal.map(n => [`dreal:${n}`, `${n} · dReal`]));
  const saved = store.get("solver");
  if (saved && [...select.options].some(o => o.value === saved)) select.value = saved;
  else select.value = "cvc5:LIA";
  onSolverChange();
}

function onSolverChange() {
  const [kind, name] = $("solver").value.split(":");
  store.set("solver", $("solver").value);
  $("solver-hint").textContent = kind === "gen" ? GENERIC_HINT : kind === "dreal" ? DREAL_HINT : (HINTS[name] || "");
  $("element-field").hidden = kind !== "gen";
  if (kind !== "gen") return;
  const defaultElement = state.solvers.defaults[name];
  const chosen = state.element[name] || defaultElement;
  const box = $("elements");
  box.innerHTML = "";
  for (const el of state.solvers.elements) {
    const b = document.createElement("button");
    b.type = "button";
    b.innerHTML = esc(el) + (el === defaultElement ? `<span class="def">default</span>` : "");
    b.classList.toggle("on", el === chosen);
    b.addEventListener("click", () => {
      state.element[name] = el;
      store.set("elements", JSON.stringify(state.element));
      box.querySelectorAll("button").forEach(x => x.classList.toggle("on", x === b));
    });
    box.appendChild(b);
  }
}

function currentSolver() {
  const [kind, name] = $("solver").value.split(":");
  if (kind === "gen") {
    const el = state.element[name] || state.solvers.defaults[name];
    return { engine: "cvc5", theory: `${name}-${el}`, label: `${name}-${el}` };
  }
  return { engine: kind === "dreal" ? "dreal" : "cvc5", theory: name, label: kind === "dreal" ? `${name} (dReal)` : name };
}

// ===========================================================================
// Running
// ===========================================================================
function run() {
  if (state.running || !state.graph) return;
  const k = parseInt($("k").value, 10);
  if (!(k >= 1)) { $("k").focus(); showErrors(["Enter K, the number of colors (1 or more)."]); return; }
  const solver = currentSolver(), graph = state.graph;
  const params = new URLSearchParams({ graph: graph.path, solver: solver.theory, engine: solver.engine,
                                       k, timeout: $("timeout").value || 0 });
  clearResult();
  clearFormulas();
  state.running = true;
  state.run = { solver, graph, k };
  setStatus("running", "Running…", `${esc(solver.label)} on <b>${esc(graph.name)}</b> with K = ${k} · starting`);
  $("run").hidden = true;
  $("stop").hidden = false;
  startTimer();

  const es = new EventSource(`/api/run?${params}`);
  state.es = es;
  es.addEventListener("start", e => {
    $("command").textContent = JSON.parse(e.data).command;
    $("command").hidden = false;
  });
  es.addEventListener("phase", e => {
    const phase = JSON.parse(e.data).phase;
    const text = { building: "building the formula", solving: "solving", finishing: "reading the model" }[phase] || phase;
    setStatus("running", phase === "solving" ? "Solving…" : "Running…",
              `${esc(solver.label)} on <b>${esc(graph.name)}</b> with K = ${k} · ${text}`);
  });
  es.addEventListener("assert", e => {
    state.asserts.push(JSON.parse(e.data));
    state.totalAsserts = Math.max(state.totalAsserts, state.asserts.length);
    scheduleFormulaRender();
  });
  es.addEventListener("assert_count", e => { state.totalAsserts = JSON.parse(e.data); updateAssertCount(); });
  es.addEventListener("result", e => finish(JSON.parse(e.data)));
  es.addEventListener("failed", e => finish({ status: "ERROR", errors: [JSON.parse(e.data).message] }));
  es.onerror = () => { if (state.running) finish({ status: "ERROR", errors: ["The connection to the server was lost."] }); };
}

function stop() {
  if (!state.running) return;
  finish({ status: "STOPPED", elapsed: (performance.now() - state.startTime) / 1000 });
}

function startTimer() {
  state.startTime = performance.now();
  $("timer").hidden = false;
  const tick = () => { $("timer").textContent = formatTime((performance.now() - state.startTime) / 1000); };
  tick();
  state.timerId = setInterval(tick, 100);
}

function formatTime(seconds) {
  if (seconds < 60) return `${seconds.toFixed(seconds < 10 ? 2 : 1)} s`;
  const m = Math.floor(seconds / 60), s = seconds - 60 * m;
  return `${m}:${s.toFixed(1).padStart(4, "0")}`;
}

function finish(result) {
  state.running = false;
  if (state.es) { state.es.close(); state.es = null; }
  clearInterval(state.timerId);
  $("run").hidden = false;
  $("stop").hidden = true;
  const { solver, graph, k } = state.run;
  const elapsed = result.elapsed ?? (performance.now() - state.startTime) / 1000;
  $("timer").textContent = formatTime(elapsed);
  const where = `${esc(solver.label)} on <b>${esc(graph.name)}</b> with K = ${k}`;

  const titles = {
    SAT: ["sat", "SAT", `${graph.name} can be colored with ${k} color${k === 1 ? "" : "s"}`],
    UNSAT: ["unsat", "UNSAT", `${graph.name} cannot be colored with ${k} color${k === 1 ? "" : "s"}`],
    UNKNOWN: ["other", "UNKNOWN", "The solver gave up without an answer"],
    TIMEOUT: ["other", "Time limit reached", "No answer within the time limit"],
    STOPPED: ["other", "Stopped", "You stopped the solver"],
    ERROR: ["other", "Error", "The solver did not run to the end"],
  };
  const [cls, title, sentence] = titles[result.status] || titles.ERROR;
  setStatus(cls, title, `${esc(sentence)} · ${where}`);

  const noisy = (result.errors || []).filter(Boolean);
  if (noisy.length && result.status !== "SAT" && result.status !== "UNSAT") showErrors(noisy);
  else if (noisy.length) showErrors(noisy, true);

  if (result.asserts !== undefined) state.totalAsserts = result.asserts;
  updateAssertCount();
  scheduleFormulaRender();

  result.graph = graph.path;
  result.k = k;
  state.result = result;
  if (result.colors) showColoring(result);
}

function setStatus(cls, title, subHtml) {
  $("status").className = `card status ${cls}`;
  $("status-title").textContent = title;
  $("status-sub").innerHTML = subHtml;
}

function showErrors(lines, soft = false) {
  const box = $("errors");
  box.hidden = false;
  box.textContent = (soft ? "Solver messages:\n" : "") + lines.join("\n");
}

function clearResult() {
  state.result = null;
  state.highlight = null;
  $("errors").hidden = true;
  $("legend").hidden = true;
  $("validity").hidden = true;
  $("label-mode").hidden = true;
  $("node-details").hidden = true;
  $("extra-values").hidden = true;
  if (!state.running) {
    $("timer").hidden = true;
    $("command").hidden = true;
    setStatus("idle", "Ready", "Pick a graph, a solver and K, then press <b>Run solver</b>.");
  }
  drawGraph();
}

// ===========================================================================
// Coloring
// ===========================================================================
// The number a model value stands for (123, #b0101, #x1f, #f3m7), or null if it is not one
function numericKey(v) {
  if (/^-?\d+(\.\d+)?$/.test(v)) return Number(v);
  if (/^#b[01]+$/.test(v)) return Number(BigInt("0b" + v.slice(2)));
  if (/^#x[0-9a-fA-F]+$/.test(v)) return Number(BigInt("0x" + v.slice(2)));
  const m = v.match(/^#f(\d+)m\d+$/);
  return m ? Number(m[1]) : null;
}

// A short plain-text form of a model value, for labels inside the drawing:
// "A" -> A, #b01 -> 01₂, @Elem_5 -> Elem₅, (set.union ...) -> {E0, E1}, 1*pi -> 1π
const SUBSCRIPT = { 0: "₀", 1: "₁", 2: "₂", 3: "₃", 4: "₄", 5: "₅", 6: "₆", 7: "₇", 8: "₈", 9: "₉", ",": ",", "-": "₋" };
function plainValue(value) {
  const pi = value.match(/^(-?\d+)\*pi$/);  // dReal's trig roots
  if (pi) return pi[1] === "0" ? "0" : pi[1] === "1" ? "π" : pi[1] === "-1" ? "−π" : `${pi[1]}π`;
  const html = Pretty.toHtml(value);
  if (html === null) return value;
  const text = html
    .replace(/<sub>(.*?)<\/sub>/g, (_, sub) => ([...sub].every(c => c in SUBSCRIPT) ? [...sub].map(c => SUBSCRIPT[c]).join("") : ""))
    .replace(/<sup>(.*?)<\/sup>/g, "^$1")
    .replace(/<[^>]+>/g, "")
    .replace(/[“”]/g, "")
    .replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&quot;/g, '"').replace(/&amp;/g, "&");
  return text;
}
const shorten = (text, max) => (text.length > max ? text.slice(0, max - 1) + "…" : text);

function prettyValue(value) {
  return Pretty.toHtml(value) ?? esc(value);
}

function showColoring(result) {
  const entries = Object.entries(result.colors).map(([n, v]) => [Number(n), v]);
  const values = [...new Set(entries.map(([, v]) => v))];
  const keys = values.map(numericKey);
  if (keys.every(k => k !== null)) {
    const order = new Map(values.map((v, i) => [v, keys[i]]));
    values.sort((a, b) => (order.get(a) < order.get(b) ? -1 : order.get(a) > order.get(b) ? 1 : 0));
  }
  const index = new Map(values.map((v, i) => [v, i]));
  const counts = new Map(values.map(v => [v, 0]));
  entries.forEach(([, v]) => counts.set(v, counts.get(v) + 1));
  result.colorIndex = index;
  result.entries = entries;

  const legend = $("legend");
  legend.hidden = false;
  legend.innerHTML = `<div class="legend-summary">Uses <b>${values.length}</b> of K = ${result.k} color${result.k === 1 ? "" : "s"}. Click a color to highlight its nodes.</div>`;
  values.forEach((v, i) => {
    const item = document.createElement("button");
    item.type = "button";
    item.className = "legend-item";
    item.title = v;
    item.innerHTML = `<span class="swatch" style="background:${colorFor(i)}"></span>`
      + `<span class="val math">${prettyValue(v)}</span><span class="n">× ${counts.get(v)}</span>`;
    item.addEventListener("click", () => {
      state.highlight = state.highlight === v ? null : v;
      legend.querySelectorAll(".legend-item").forEach(x => x.classList.toggle("dim", state.highlight !== null && x !== item));
      applyHighlight();
      renderNodeGrid();
    });
    legend.appendChild(item);
  });

  const validity = $("validity");
  validity.hidden = false;
  const missing = (state.graph.nodes || 0) - entries.length;
  if (result.num_conflicts) {
    validity.className = "validity bad";
    validity.textContent = `✕ ${result.num_conflicts} edge${result.num_conflicts === 1 ? "" : "s"} join same-colored nodes`;
  } else {
    validity.className = "validity ok";
    validity.textContent = missing > 0 ? `✓ No conflicts (${missing} nodes not in the model)` : "✓ Valid coloring";
  }

  $("node-details").hidden = false;
  $("label-mode").hidden = false;
  renderNodeGrid();

  const extra = result.extra || [];
  if (extra.length) {
    const shown = extra.slice(0, 16).map(([k, v]) => `<span class="math">${prettyValue(k)} = ${prettyValue(v)}</span>`).join(" · ");
    $("extra-values").innerHTML = `Other model values: ${shown}${extra.length > 16 ? ` · … (${extra.length - 16} more)` : ""}`;
    $("extra-values").hidden = false;
  }
  drawGraph(result);
}

function renderNodeGrid() {
  const result = state.result;
  if (!result?.entries) return;
  const filter = $("node-filter").value.trim().toLowerCase();
  const rows = [];
  for (const [node, value] of result.entries) {
    if (state.highlight !== null && value !== state.highlight) continue;
    if (filter && !String(node).includes(filter) && !value.toLowerCase().includes(filter)
        && !plainValue(value).toLowerCase().includes(filter)) continue;
    const i = result.colorIndex.get(value);
    const shown = state.labels === "value" ? `<span class="val math">${prettyValue(value)}</span>`
                                           : `<span class="val">color ${i + 1}</span>`;
    rows.push(`<div class="node-chip" title="${esc(value)}"><span class="swatch" style="background:${colorFor(i)}"></span>`
      + `<span class="id">node ${node}</span>${shown}</div>`);
  }
  $("node-grid").innerHTML = rows.join("") || `<p class="empty">No nodes match.</p>`;
}

// ===========================================================================
// Graph drawing (force-directed layout, cached per graph)
// ===========================================================================
const W = 900, H = 560;

function seededRandom(seed) {
  let s = seed >>> 0 || 1;
  return () => ((s = (s * 1664525 + 1013904223) >>> 0) / 4294967296);
}

function computeLayout(n, edges) {
  const rand = seededRandom(n * 7919 + edges.length);
  const pos = Array.from({ length: n + 1 }, () => [W * (0.25 + 0.5 * rand()), H * (0.25 + 0.5 * rand())]);
  const k = Math.sqrt((W * H) / Math.max(n, 1)) * 0.75;
  const iterations = n > 150 ? 220 : 320;
  let temperature = W / 8;
  for (let it = 0; it < iterations; it++) {
    const disp = Array.from({ length: n + 1 }, () => [0, 0]);
    for (let i = 1; i <= n; i++) {
      for (let j = i + 1; j <= n; j++) {
        let dx = pos[i][0] - pos[j][0], dy = pos[i][1] - pos[j][1];
        let d2 = dx * dx + dy * dy;
        if (d2 < 0.01) { dx = rand() - 0.5; dy = rand() - 0.5; d2 = 0.01; }
        const f = (k * k) / d2;
        disp[i][0] += dx * f; disp[i][1] += dy * f;
        disp[j][0] -= dx * f; disp[j][1] -= dy * f;
      }
    }
    for (const [u, v] of edges) {
      if (u < 1 || v < 1 || u > n || v > n) continue;
      const dx = pos[u][0] - pos[v][0], dy = pos[u][1] - pos[v][1];
      const d = Math.sqrt(dx * dx + dy * dy) || 0.01;
      const f = d / k;
      disp[u][0] -= dx * f; disp[u][1] -= dy * f;
      disp[v][0] += dx * f; disp[v][1] += dy * f;
    }
    for (let i = 1; i <= n; i++) {
      // gentle pull to the center keeps disconnected parts on screen
      disp[i][0] += (W / 2 - pos[i][0]) * 0.02 * k / 10;
      disp[i][1] += (H / 2 - pos[i][1]) * 0.02 * k / 10;
      const len = Math.hypot(disp[i][0], disp[i][1]) || 1;
      const step = Math.min(len, temperature);
      pos[i][0] += (disp[i][0] / len) * step;
      pos[i][1] += (disp[i][1] / len) * step;
    }
    temperature *= 0.985;
  }
  // fit into the box
  const xs = pos.slice(1).map(p => p[0]), ys = pos.slice(1).map(p => p[1]);
  const minX = Math.min(...xs), maxX = Math.max(...xs), minY = Math.min(...ys), maxY = Math.max(...ys);
  const pad = 34, sx = (W - 2 * pad) / Math.max(maxX - minX, 1), sy = (H - 2 * pad) / Math.max(maxY - minY, 1);
  const s = Math.min(sx, sy);
  const ox = (W - (maxX - minX) * s) / 2, oy = (H - (maxY - minY) * s) / 2;
  return pos.map(p => [ox + (p[0] - minX) * s, oy + (p[1] - minY) * s]);
}

function drawGraph(result = null) {
  const box = $("drawing");
  const data = state.graphData;
  if (!data) { box.innerHTML = `<div class="msg">Loading graph…</div>`; return; }
  if (!data.edges) {
    box.innerHTML = `<div class="msg">${data.nodes} nodes and ${data.num_edges} edges is too large to draw.`
      + (result?.colors ? " The colors of all nodes are listed below." : "") + `</div>`;
    return;
  }
  const n = data.nodes;
  const layout = data.layout ||= computeLayout(n, data.edges);  // kept with the graph it belongs to
  const r = n <= 25 ? 14 : n <= 60 ? 10 : n <= 130 ? 7 : 5;
  const conflicts = new Set((result?.conflicts || []).map(([u, v]) => `${u}-${v}`));
  const colorOf = node => {
    if (!result?.colors) return null;
    const v = result.colors[String(node)];
    return v === undefined ? null : colorFor(result.colorIndex.get(v));
  };
  const parts = [`<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Graph drawing">`];
  for (const [u, v] of data.edges) {
    if (!layout[u] || !layout[v]) continue;
    const bad = conflicts.has(`${u}-${v}`) ? ` class="conflict"` : "";
    parts.push(`<line${bad} x1="${layout[u][0].toFixed(1)}" y1="${layout[u][1].toFixed(1)}" x2="${layout[v][0].toFixed(1)}" y2="${layout[v][1].toFixed(1)}"/>`);
  }
  // Labels: node numbers inside the circles, or the assigned values (inside when they
  // all fit, otherwise just below each circle)
  const byValue = state.labels === "value" && result?.colors;
  const labelOf = i => {
    if (!byValue) return String(i);
    const v = result.colors[String(i)];
    return v === undefined ? "" : shorten(plainValue(v), 12);
  };
  const labels = Array.from({ length: n + 1 }, (_, i) => (i ? labelOf(i) : ""));
  const inside = !byValue ? n <= 40 : r >= 10 && labels.every(l => l.length <= 3);
  const showLabels = !byValue ? n <= 40 : n <= 120;
  for (let i = 1; i <= n; i++) {
    const fill = colorOf(i), [x, y] = layout[i];
    parts.push(`<circle data-node="${i}" cx="${x.toFixed(1)}" cy="${y.toFixed(1)}" r="${r}"${fill ? ` style="fill:${fill}"` : ""}/>`);
    if (!showLabels || !labels[i]) continue;
    if (inside) parts.push(`<text x="${x.toFixed(1)}" y="${y.toFixed(1)}">${esc(labels[i])}</text>`);
    else parts.push(`<text class="value" x="${x.toFixed(1)}" y="${(y + r + 9).toFixed(1)}">${esc(labels[i])}</text>`);
  }
  parts.push(`</svg>`);
  box.innerHTML = parts.join("");
  attachTooltips(box.querySelector("svg"));
  applyHighlight();
}

function applyHighlight() {
  const result = state.result;
  document.querySelectorAll("#drawing circle").forEach(c => {
    const v = result?.colors?.[c.dataset.node];
    c.classList.toggle("dim", state.highlight !== null && v !== state.highlight);
  });
}

function attachTooltips(svg) {
  if (!svg) return;
  const tip = $("tooltip");
  svg.addEventListener("mousemove", e => {
    const node = e.target.dataset?.node;
    if (!node) { tip.hidden = true; return; }
    const v = state.result?.colors?.[node];
    tip.innerHTML = `<b>node ${node}</b>` + (v !== undefined ? ` <span class="math">= ${prettyValue(v)}</span>` : "");
    tip.hidden = false;
    tip.style.left = `${e.clientX + 14}px`;
    tip.style.top = `${e.clientY + 12}px`;
  });
  svg.addEventListener("mouseleave", () => { tip.hidden = true; });
}

// ===========================================================================
// Formulas
// ===========================================================================
function setMode(mode) {
  state.mode = mode;
  store.set("mode", mode);
  document.querySelectorAll("#formula-mode button").forEach(b => b.classList.toggle("on", b.dataset.mode === mode));
  rebuildFormulas();
}

function clearFormulas() {
  state.asserts = [];
  state.totalAsserts = 0;
  state.limit = PAGE;
  rebuildFormulas();
}

function visibleIndices() {
  const filter = $("formula-filter").value.trim().toLowerCase();
  if (!filter) return null;  // all of them
  const out = [];
  state.asserts.forEach((a, i) => { if (a.toLowerCase().includes(filter)) out.push(i); });
  return out;
}

function formulaItem(i) {
  const li = document.createElement("li");
  li.value = i + 1;
  li.setAttribute("value", i + 1);
  const text = state.asserts[i];
  const html = state.mode === "pretty" ? Pretty.toHtml(text) : null;
  const body = document.createElement("div");
  if (html !== null) { body.className = "math"; body.innerHTML = html; }
  else { body.className = "raw"; body.textContent = text; }
  li.appendChild(body);
  return li;
}

function rebuildFormulas() {
  $("formulas").innerHTML = "";
  state.rendered = 0;
  renderMoreFormulas();
}

function renderMoreFormulas() {
  const list = $("formulas");
  const indices = visibleIndices();
  const available = indices ? indices.length : state.asserts.length;
  const fragment = document.createDocumentFragment();
  while (state.rendered < Math.min(state.limit, available)) {
    fragment.appendChild(formulaItem(indices ? indices[state.rendered] : state.rendered));
    state.rendered++;
  }
  list.appendChild(fragment);
  const remaining = available - state.rendered;
  $("formula-more").hidden = remaining <= 0;
  $("formula-more").textContent = `Show ${Math.min(PAGE, remaining)} more (${remaining} not shown)`;
  $("formula-empty").hidden = state.asserts.length > 0;
  if (state.asserts.length && indices && !indices.length) {
    $("formula-empty").hidden = false;
    $("formula-empty").textContent = "No formula matches the filter.";
  } else {
    $("formula-empty").textContent = "The formulas appear here as soon as the solver has built them.";
  }
  updateAssertCount();
}

function scheduleFormulaRender() {
  if (state.pendingRender) return;
  state.pendingRender = true;
  requestAnimationFrame(() => { state.pendingRender = false; renderMoreFormulas(); });
}

function updateAssertCount() {
  const total = state.totalAsserts, got = state.asserts.length;
  let text = total ? `${total.toLocaleString()}` : "";
  if (total > got && !state.running) text += ` · the first ${got.toLocaleString()} are listed`;
  else if (state.running && total) text += "…";
  $("assert-count").textContent = text;
}

init();
