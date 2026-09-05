from pathlib import Path
p = Path('src/duplotrain/static/editor.html')
s = p.read_text()
s = s.replace('<meta charset="utf-8">', '<meta charset="utf-8">\n<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">', 1)
s = s.replace('grid-template-columns: 300px 1fr; height: 100vh;', 'grid-template-columns: 300px minmax(0, 1fr); height: 100vh; height: 100dvh; overflow: hidden;', 1)
s = s.replace('overflow-y: auto; display: flex;', 'min-height: 0; overflow-y: auto; display: flex;', 1)
s = s.replace('#stage { position: relative;', '#stage { min-width: 0; min-height: 0; position: relative;', 1)
s = s.replace('height: 100%; cursor: grab; }', 'height: 100%; cursor: grab; touch-action: none; user-select: none; }', 1)
s = s.replace('.solverow { display: flex;', '.solverow { display: flex; flex-wrap: wrap;', 1)
s = s.replace('</style>', '''  #save-status { font-size: 12px; color: var(--dim); overflow-wrap: anywhere; }
  #save-status.err { color: var(--open); }
  #toolbar { position: absolute; top: 10px; left: 10px; right: 10px; z-index: 2;
             display: flex; flex-wrap: wrap; gap: 6px; pointer-events: none; }
  #toolbar button { pointer-events: auto; background: var(--panel); }
  #toolbar button.armed { background: var(--accent); color: white; }
  #hint { max-width: calc(100% - 24px); pointer-events: none; }
  .cand .buttons { display: flex; gap: 8px; margin-top: 6px; }
  button:focus-visible, input:focus-visible { outline: 3px solid var(--accent); outline-offset: 2px; }
  body.busy #side button, body.busy #side input { pointer-events: none; opacity: .7; }
  @media (max-width: 700px) {
    body { grid-template-columns: minmax(0, 1fr); grid-template-rows: minmax(220px, 52%) minmax(0, 1fr); }
    #stage { grid-row: 1; }
    #side { grid-row: 2; border-right: 0; border-top: 1px solid #e2e0da;
            padding-bottom: max(14px, env(safe-area-inset-bottom)); }
    #toolbar { top: max(10px, env(safe-area-inset-top)); }
  }
  @media (pointer: coarse) {
    button { min-height: 44px; min-width: 44px; }
    input[type="number"] { min-height: 40px; }
    .variants { gap: 8px; }
  }
</style>''', 1)
s = s.replace('<div id="status">loading…</div>', '<div id="status" role="status" aria-live="polite">loading…</div>\n  <div id="save-status" role="status"></div>', 1)
s = s.replace('  <div id="cands"></div>', '''  <label class="solverow">Search up to
    <input id="max-pieces" type="number" min="1" max="128" step="1" value="26"> added pieces
  </label>
  <button id="expand-search" hidden>Search deeper</button>
  <div id="cands"></div>''', 1)
s = s.replace('  <canvas id="canvas"></canvas>\n  <div id="hint">drag: pan · wheel: zoom · click red arrow: attach · right-click: remove piece/stone</div>', '''  <canvas id="canvas" aria-label="Track layout. Choose a piece, then tap an open end to attach it."></canvas>
  <div id="toolbar" role="toolbar" aria-label="Canvas controls">
    <button id="zoom-in" aria-label="Zoom in">+</button>
    <button id="zoom-out" aria-label="Zoom out">−</button>
    <button id="fit">Fit layout</button>
    <button id="delete-tool" aria-pressed="false">Remove</button>
  </div>
  <div id="hint">drag: pan · pinch / wheel / + −: zoom · red arrow: attach · Remove: tap a piece</div>''', 1)
a = s.index('const api = async')
b = s.index('\nlet S = null;', a)
s = s[:a] + '''let apiBusy = false;
const api = async (path, body) => {
  if (apiBusy) throw new Error("An action is still running; try again when it finishes.");
  apiBusy = true;
  document.body.classList.add("busy");
  try {
    if (window.duplotrainApi) return await window.duplotrainApi(path, body);
    const res = await fetch(path, body === undefined ? {} : {
      method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify(body),
    });
    const data = await res.json();
    if (!res.ok) throw new Error(data.error || res.statusText);
    return data;
  } finally {
    apiBusy = false;
    document.body.classList.remove("busy");
  }
};
''' + s[b:]
s = s.replace('let fitted = false;', '''let fitted = false;
let deleting = false;
let selectedCandidate = null;
let solving = false;
let lastSolve = null;
let recoveryAttempted = false;
let autosaveReady = false;
const STORAGE_KEY = "duplotrain-session/1:" + location.pathname;

// Tool changes are exclusive: a stone can never intercept an endpoint pick.
function selectTool({piece = null, stone = null, pick = null, remove = false} = {}) {
  armed = piece;
  armedStone = stone;
  pickMode = pick;
  deleting = remove;
  const button = document.getElementById("delete-tool");
  button.classList.toggle("armed", remove);
  button.setAttribute("aria-pressed", String(remove));
}

function saveSession() {
  if (!autosaveReady || !S || !S.snapshot) return;
  const notice = document.getElementById("save-status");
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(S.snapshot));
    notice.textContent = "Autosaved on this device · Export JSON for a portable layout copy.";
    notice.className = "";
  } catch (_error) {
    notice.textContent = "Autosave unavailable — export JSON before closing this page.";
    notice.className = "err";
  }
}''', 1)
s = s.replace('window.addEventListener("resize", resize);', '''window.addEventListener("resize", resize);
if (window.ResizeObserver) new ResizeObserver(resize).observe(canvas);
window.addEventListener("pagehide", saveSession);''', 1)
s = s.replace('''    ctx.fillText("Arm a piece on the left, then click anywhere to place the first one.",
                 canvas.clientWidth / 2, canvas.clientHeight / 2);''', '''    ctx.fillText("Choose a piece, then tap or click the floor.",
                 canvas.clientWidth / 2, canvas.clientHeight / 2, canvas.clientWidth - 24);''', 1)
s = s.replace('  } else if (armedStone) {\n    const info = S.stones', '  } else if (deleting) {\n    status("Remove tool — tap a stone or piece. Undo restores it.");\n  } else if (armedStone) {\n    const info = S.stones', 1)
s = s.replace('  el("solve").disabled = opens < 2;', '''  el("solve").disabled = solving || opens < 2;
  el("undo").disabled = solving || !S.can_undo;''', 1)
s = s.replace('input.type = "number"; input.min = 0; input.value = owned;', 'input.type = "number"; input.min = 0; input.max = 10000; input.step = 1; input.value = owned;\n    input.setAttribute("aria-label", `${piece.name} owned`);', 1)
s = s.replace('''        armed = (armed && armed.piece === piece.id && armed.entry === v.entry && armed.exit === v.exit)
          ? null
          : { piece: piece.id, pieceName: piece.name, entry: v.entry, exit: v.exit, label: v.label };
        armedStone = null;
        pickMode = null;''', '''        const same = armed && armed.piece === piece.id && armed.entry === v.entry && armed.exit === v.exit;
        selectTool(same ? {} : {
          piece: {piece: piece.id, pieceName: piece.name, entry: v.entry, exit: v.exit, label: v.label},
        });''', 1)
s = s.replace('''      armedStone = armedStone === sid ? null : sid;
      armed = null; pickMode = null;''', '      selectTool(armedStone === sid ? {} : {stone: sid});', 1)
a = s.index('function renderCandidates()')
b = s.index('\nfunction redraw()', a)
s = s[:a] + '''function renderCandidates() {
  const box = el("cands");
  box.replaceChildren();
  const candidates = S.candidates || [];
  const key = (c) => `${c.revision}:${c.index}`;
  const selected = candidates.find(c => key(c) === selectedCandidate);
  if (!selected) selectedCandidate = null;
  preview = selected ? selected.preview : null;
  for (const c of candidates) {
    const div = document.createElement("div");
    div.className = "cand";
    div.dataset.candidateIndex = c.index;
    const description = document.createElement("div");
    const closure = document.createElement("span");
    closure.className = c.exact ? "exact" : "gap";
    closure.textContent = c.exact ? "exact" : `forced ${c.gap} mm`;
    const added = Object.entries(c.added).map(([k, n]) => `${n}×${k}`).join(" ") || "nothing";
    description.append(closure, `${c.kind === "reversing" ? " reversing (↔ stone on tail)" : ""} — add ${added}`,
      ` (${c.size_cm[0]}×${c.size_cm[1]} cm${c.open_stubs ? `, ${c.open_stubs} stubs` : ""})`);
    div.append(description);
    const buttons = document.createElement("div");
    buttons.className = "buttons";
    const show = document.createElement("button");
    show.textContent = key(c) === selectedCandidate ? "Previewing" : "Preview";
    show.setAttribute("aria-pressed", String(key(c) === selectedCandidate));
    show.addEventListener("click", () => {
      selectedCandidate = key(c);
      renderCandidates();
      draw();
    });
    const apply = document.createElement("button");
    apply.textContent = "Apply";
    apply.disabled = key(c) !== selectedCandidate;
    apply.addEventListener("click", async () => {
      try {
        S = await api("/api/apply", {index: c.index, revision: c.revision});
        selectedCandidate = null;
        fitted = false;
        redraw();
      } catch (e) { status(e.message, "err"); }
    });
    buttons.append(show, apply);
    div.append(buttons);
    div.addEventListener("pointerenter", (event) => {
      if (event.pointerType !== "touch") { preview = c.preview; draw(); }
    });
    div.addEventListener("pointerleave", () => {
      const chosen = candidates.find(candidate => key(candidate) === selectedCandidate);
      preview = chosen ? chosen.preview : null;
      draw();
    });
    box.append(div);
  }
}
''' + s[b:]
s = s.replace('  refreshStatus(); draw();\n}\n\nasync function refresh()', '''  if (lastSolve && lastSolve.revision !== S.revision) el("expand-search").hidden = true;
  refreshStatus(); draw(); saveSession();
}

async function refresh()''', 1)
s = s.replace('''async function refresh() {
  S = await api("/api/state");
  redraw();
}''', '''async function refresh() {
  S = await api("/api/state");
  if (!recoveryAttempted) {
    recoveryAttempted = true;
    try {
      const saved = localStorage.getItem(STORAGE_KEY);
      // A running local server is authoritative; only restore into a fresh engine.
      if (saved && S.revision === 0) {
        if (saved.length > 2 * 1024 * 1024) throw new Error("saved session is too large");
        S = await api("/api/restore", {data: JSON.parse(saved)});
      }
      autosaveReady = true;
    } catch (error) {
      // Do not overwrite a checkpoint that we could not recover.
      const notice = el("save-status");
      notice.textContent = `Recovery unavailable: ${error.message}. Existing save kept; export new work.`;
      notice.className = "err";
    }
  }
  redraw();
}''', 1)
s = s.replace('''  try { S = await api("/api/clear", {}); fitted = false; redraw(); } catch (e) { status(e.message, "err"); }''', '''  try {
    S = await api("/api/clear", {});
    selectTool();
    fitted = false;
    redraw();
    status("Floor cleared — Undo restores it.");
  } catch (e) { status(e.message, "err"); }''', 1)
a = s.index('el("export").addEventListener')
b = s.index('el("import").addEventListener', a)
s = s[:a] + '''el("export").addEventListener("click", async () => {
  try {
    const data = await api("/api/export");
    const blob = new Blob([JSON.stringify(data, null, 2)], {type: "application/json"});
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = "layout.json";
    a.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  } catch (e) { status(e.message, "err"); }
});
''' + s[b:]
s = s.replace('''    pickMode = { stage: "grow", grow: null };
    armed = null;
    renderPalette(); refreshStatus(); draw();''', '''    selectTool({pick: {stage: "grow", grow: null}});
    renderPalette(); renderStones(); refreshStatus(); draw();''', 1)
s = s.replace('''let solving = false;
async function runSolve(grow, close) {''', '''el("expand-search").addEventListener("click", async () => {
  el("max-pieces").value = Math.min(128, Math.max(1, Number(el("max-pieces").value)) * 2);
  if (!lastSolve || lastSolve.revision !== S.revision) { el("solve").click(); return; }
  await runSolve(lastSolve.grow, lastSolve.close);
});

async function runSolve(grow, close) {''', 1)
s = s.replace('''  if (solving) return;
  solving = true;''', '''  if (solving || apiBusy || !S) return;
  selectTool();
  const maxPieces = Number(el("max-pieces").value);
  const slop = Number(el("slop").value);
  if (!Number.isInteger(maxPieces) || maxPieces < 1 || maxPieces > 128 || !Number.isFinite(slop) || slop < 0) {
    status("Use 1–128 added pieces and a finite, non-negative slop.", "err");
    return;
  }
  lastSolve = {grow, close, revision: S.revision};
  el("expand-search").hidden = true;
  selectedCandidate = null;
  solving = true;''', 1)
s = s.replace('  status("searching… (hard gaps can take up to ~30 s)");', '  status("searching…");', 1)
s = s.replace('      slop: parseFloat(el("slop").value || "0"),', '      slop, max_pieces: maxPieces,', 1)
s = s.replace('''      else if (S.aborted)
        status(`Searched ${(S.searched || 0).toLocaleString()} states without luck — ` +
               "a closure may still exist. Try more slop, or simplify the gap.", "err");
      else
        status("No way to close with the remaining pieces — add inventory or slop.", "err");''', '''      else if (!S.complete)
        status(`No completion found within the search limits (${S.stop_reason}, ` +
               `${(S.searched || 0).toLocaleString()} states). A closure may still exist.`, "err");
      else
        status("No completion fits the remaining inventory under these settings.", "err");
      el("expand-search").hidden = !!S.complete || maxPieces >= 128;''', 1)
s = s.replace('status(`${S.candidates.length} way(s) to close — hover to preview, click to apply.`);', 'status(`${S.candidates.length} suggestion(s)${S.complete ? "" : " (search limited)"} — Preview, then Apply.`);', 1)
s = s.replace('    el("solve").disabled = (S && S.open_ends.length < 2) || false;', '    el("solve").disabled = !S || S.open_ends.length < 2;\n    el("undo").disabled = !S || !S.can_undo;', 1)
a = s.index('// canvas interactions')
b = s.index('window.addEventListener("keydown"', a)
s = s[:a] + '''// Pointer events support mouse, pen and touch; capture keeps drags well-defined
// outside the canvas. Any multi-touch gesture suppresses placement until all lift.
const pointers = new Map();
let multiTouch = false;
const canvasPoint = (e) => {
  const r = canvas.getBoundingClientRect();
  return {x: e.clientX - r.left, y: e.clientY - r.top};
};
function zoomAt(factor, sx, sy) {
  const [wx, wy] = screenToWorld(sx, sy);
  view.scale = Math.min(4, Math.max(0.08, view.scale * factor));
  const [nx, ny] = screenToWorld(sx, sy);
  view.x += wx - nx; view.y += wy - ny;
  draw();
}
function pairMetrics() {
  const [a, b] = Array.from(pointers.values());
  return {x: (a.x + b.x) / 2, y: (a.y + b.y) / 2, distance: Math.hypot(a.x - b.x, a.y - b.y)};
}
canvas.addEventListener("pointerdown", (e) => {
  if (e.button !== 0 || !S) return;
  e.preventDefault();
  const p = canvasPoint(e);
  pointers.set(e.pointerId, {...p, startX: p.x, startY: p.y, moved: false});
  canvas.setPointerCapture(e.pointerId);
  if (pointers.size > 1) {
    multiTouch = true;
    for (const pointer of pointers.values()) pointer.moved = true;
  }
});
canvas.addEventListener("pointermove", (e) => {
  const old = pointers.get(e.pointerId);
  if (!old) return;
  const p = canvasPoint(e);
  if (pointers.size > 1) {
    const before = pairMetrics();
    const world = screenToWorld(before.x, before.y);
    Object.assign(old, p, {moved: true});
    const after = pairMetrics();
    if (before.distance > 1) view.scale = Math.min(4, Math.max(0.08, view.scale * after.distance / before.distance));
    const now = screenToWorld(after.x, after.y);
    view.x += world[0] - now[0]; view.y += world[1] - now[1];
  } else {
    if (Math.hypot(p.x - old.startX, p.y - old.startY) > 5) old.moved = true;
    if (old.moved) {
      view.x -= (p.x - old.x) / view.scale;
      view.y += (p.y - old.y) / view.scale;
    }
    Object.assign(old, p);
  }
  draw();
});
canvas.addEventListener("pointerup", async (e) => {
  const pointer = pointers.get(e.pointerId);
  if (!pointer || e.button !== 0) return;
  const activate = !pointer.moved && !multiTouch;
  pointers.delete(e.pointerId);
  if (canvas.hasPointerCapture(e.pointerId)) canvas.releasePointerCapture(e.pointerId);
  if (!pointers.size) multiTouch = false;
  if (activate) {
    const p = canvasPoint(e);
    await activateAt(p.x, p.y);
  }
});
for (const event of ["pointercancel", "lostpointercapture"]) {
  canvas.addEventListener(event, (e) => {
    pointers.delete(e.pointerId);
    if (!pointers.size) multiTouch = false;
  });
}

async function activateAt(sx, sy) {
  if (!S || apiBusy || solving) return;
  const hit = openEndScreenPos().map(p => ({...p, distance: Math.hypot(p.x - sx, p.y - sy)}))
    .filter(p => p.distance < 22).sort((a, b) => a.distance - b.distance)[0];
  try {
    if (pickMode) {
      if (!hit) return;
      if (pickMode.stage === "grow") {
        selectTool({pick: {stage: "close", grow: hit.end}});
        refreshStatus(); draw();
      } else {
        if (hit.end[0] === pickMode.grow[0] && hit.end[1] === pickMode.grow[1]) {
          status("Choose a different open end to close onto.", "err");
          return;
        }
        await runSolve(pickMode.grow, hit.end);
      }
    } else if (deleting) {
      await removeAt(sx, sy);
    } else if (armedStone) {
      const mount = stoneMountAt(sx, sy);
      if (mount) {
        S = await api("/api/stone", {placement: mount.placement, id: armedStone, at_port: mount.at_port});
        redraw();
      }
    } else if (armed && S.layout.placements.length === 0) {
      S = await api("/api/attach", {piece: armed.piece, entry: armed.entry, at: null});
      fitted = false; redraw();
    } else if (armed && hit) {
      S = await api("/api/attach", {piece: armed.piece, entry: armed.entry, at: hit.end});
      redraw();
    } else if (hit && S.matable.length) {
      const mate = S.matable.find(([a, b]) =>
        (a[0] === hit.end[0] && a[1] === hit.end[1]) || (b[0] === hit.end[0] && b[1] === hit.end[1]));
      if (mate) { S = await api("/api/join", {a: mate[0], b: mate[1]}); redraw(); }
    }
  } catch (err) { status(err.message, "err"); }
}
async function removeAt(sx, sy) {
  if (!S || apiBusy || solving) return;
  try {
    const mark = stoneMarkPositions().find(m => Math.hypot(m.x - sx, m.y - sy) < Math.max(16, m.r + 4));
    if (mark) {
      S = await api("/api/stone", {placement: mark.placement, id: mark.id});
    } else {
      const hit = placementAt(sx, sy);
      if (hit === null) return;
      S = await api("/api/remove", {placement: hit});
    }
    redraw();
  } catch (err) { status(err.message, "err"); }
}
canvas.addEventListener("contextmenu", async (e) => {
  e.preventDefault();
  if (e.pointerType === "touch") return;
  const p = canvasPoint(e);
  await removeAt(p.x, p.y);
});
canvas.addEventListener("wheel", (e) => {
  e.preventDefault();
  const p = canvasPoint(e);
  zoomAt(e.deltaY < 0 ? 1.12 : 1 / 1.12, p.x, p.y);
}, {passive: false});
el("zoom-in").addEventListener("click", () => zoomAt(1.25, canvas.clientWidth / 2, canvas.clientHeight / 2));
el("zoom-out").addEventListener("click", () => zoomAt(1 / 1.25, canvas.clientWidth / 2, canvas.clientHeight / 2));
el("fit").addEventListener("click", () => { fitView(); draw(); });
el("delete-tool").addEventListener("click", () => {
  if (!S) return;
  selectTool({remove: !deleting});
  renderPalette(); renderStones(); refreshStatus(); draw();
});
''' + s[b:]
s = s.replace('''  if ((e.ctrlKey || e.metaKey) && e.key === "z") el("undo").click();
  if (e.key === "Escape") {
    armed = null; armedStone = null; pickMode = null;''', '''  if (!S || apiBusy || e.target.closest("input, textarea, [contenteditable='true']")) return;
  if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "z") {
    e.preventDefault();
    el("undo").click();
  }
  if (e.key === "Escape") {
    selectTool();''', 1)
s = s.replace('    div.className = "piece";', '    div.className = "piece";\n    div.dataset.pieceId = piece.id;', 1)
p.write_text(s)
