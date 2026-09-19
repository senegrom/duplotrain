"use strict";
// Transport: the local `duplotrain gui` server answers over HTTP; the static web
// build (see webapp/) installs window.duplotrainApi to run the same Python engine
// in-browser via Pyodide. Checked at call time so either host works unmodified.
let apiBusy = false;
async function api(path, body) {
  if (apiBusy) throw new Error("An action is still running; try again when it finishes.");
  apiBusy = true;
  document.body.classList.add("busy");
  try {
    // Legacy API clients still receive full previews. This editor opts into the
    // versioned drawing-only contract; state reads use the existing read-only POST.
    if (path !== "/api/export") body = {...body, preview_format: "duplotrain-preview/1"};
    if (body !== undefined && path !== "/api/state" && path !== "/api/export") {
      // Capture the state the user acted on; never fill in a newer revision
      // after an await. Preserve an explicit candidate revision as well.
      body = {revision: S && S.revision, ...body};
    }
    if (window.duplotrainApi) return await window.duplotrainApi(path, body);
    const res = await fetch(path, body === undefined ? {} : {
      method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify(body),
    });
    const data = await res.json();
    if (!res.ok) {
      const error = new Error(data.error || res.statusText);
      error.code = data.code;
      error.state = data.state;
      throw error;
    }
    return data;
  } catch (error) {
    if (error.code === "stale_revision" && error.state) {
      S = error.state;
      selectTool();
      selectedCandidate = null;
      preview = null;
      lastSolve = null;
      el("expand-search").hidden = true;
      redraw();
    }
    throw error; // Refresh only: never replay a stale deletion/attachment.
  } finally {
    apiBusy = false;
    document.body.classList.remove("busy");
  }
}

let S = null;                 // last /api/state payload
let armed = null;             // {piece, entry, label}
let armedStone = null;        // stone id
let preview = null;           // candidate layout ghost
let pickMode = null;          // null | {stage: "grow"|"close", grow: [i,p]}
let view = { x: 0, y: 0, scale: 0.9 };
let fitted = false;
let deleting = false;
let selectedCandidate = null;
let solving = false;
let lastSolve = null;
let recoveryAttempted = false;
let autosaveReady = false;

// Tool changes are exclusive: a stone can never intercept an endpoint pick.
function selectTool({piece = null, stone = null, pick = null, remove = false} = {}) {
  armed = piece;
  armedStone = stone;
  pickMode = pick ? {...pick, revision: S && S.revision} : null;
  deleting = remove;
  const button = document.getElementById("delete-tool");
  button.classList.toggle("armed", remove);
  button.setAttribute("aria-pressed", String(remove));
}

// ---------- Checkpoint persistence ----------
// Use a new key so a still-open tab running the old, unconditional writer cannot
// overwrite new checkpoints. The previous key is read once for migration only.
const STORAGE_KEY = "duplotrain-session/2:" + location.pathname;
const LEGACY_STORAGE_KEY = "duplotrain-session/1:" + location.pathname;
const CHECKPOINT_FORMAT = "duplotrain-checkpoint/1";
let savedCheckpoint = null;       // exact revision this tab read or last committed
let lastSavedSnapshot = null;     // ignore redraws and other non-mutating actions

function saveNotice(message, error = false) {
  const notice = document.getElementById("save-status");
  notice.textContent = message;
  notice.className = error ? "err" : "";
}

function pauseAutosave() {
  autosaveReady = false;
  saveNotice("Another tab changed the saved session. Autosave paused here; " +
             "export JSON to keep this tab's work before reloading.", true);
}

function decodeCheckpoint(raw, legacy = false) {
  if (raw.length > 2 * 1024 * 1024) throw new Error("saved session is too large");
  const record = JSON.parse(raw);
  if (!legacy && (!record || record.format !== CHECKPOINT_FORMAT ||
                  typeof record.revision !== "string" || !record.revision ||
                  record.revision.length > 128)) {
    throw new Error("unrecognised checkpoint format");
  }
  const snapshot = legacy ? record : record.snapshot;
  if (!snapshot || snapshot.format !== "duplotrain-session/1") {
    throw new Error("unrecognised session format");
  }
  return snapshot;
}

async function initializeRecovery() {
  try {
    savedCheckpoint = localStorage.getItem(STORAGE_KEY);
    const legacy = savedCheckpoint === null;
    const raw = legacy ? localStorage.getItem(LEGACY_STORAGE_KEY) : savedCheckpoint;
    if (raw !== null) {
      const snapshot = decodeCheckpoint(raw, legacy);
      lastSavedSnapshot = JSON.stringify(snapshot);
      // A running local server is authoritative; restore only a fresh engine.
      if (S.revision === 0) S = await api("/api/restore", {data: snapshot});
    }
    autosaveReady = true;
  } catch (error) {
    // Never overwrite unreadable data, or fall back past a corrupt new save.
    autosaveReady = false;
    saveNotice(`Recovery unavailable: ${error.message}. Existing save kept; export new work.`, true);
  }
}

async function saveSession() {
  if (!autosaveReady || !S || !S.snapshot) return;
  // localStorage alone has no atomic compare-and-swap. All writers use the same
  // origin-scoped Web Lock, and recheck the checkpoint *inside* that lock.
  if (!navigator.locks) {
    autosaveReady = false;
    saveNotice("Safe autosave unavailable in this browser or connection; export JSON before closing.", true);
    return;
  }
  try {
    await navigator.locks.request(STORAGE_KEY, () => {
      if (!autosaveReady) return;
      if (localStorage.getItem(STORAGE_KEY) !== savedCheckpoint) {
        pauseAutosave();
        return;
      }
      // Read the latest state when this queued lock is granted, not an earlier
      // snapshot captured while another save was in flight.
      const snapshot = JSON.stringify(S.snapshot);
      if (savedCheckpoint !== null && snapshot === lastSavedSnapshot) {
        saveNotice("Autosaved on this device · Export JSON for a portable layout copy.");
        return;
      }
      const checkpoint = JSON.stringify({
        format: CHECKPOINT_FORMAT, revision: crypto.randomUUID(), snapshot: S.snapshot,
      });
      if (checkpoint.length > 2 * 1024 * 1024) throw new Error("session is too large to autosave");
      localStorage.setItem(STORAGE_KEY, checkpoint);
      savedCheckpoint = checkpoint;
      lastSavedSnapshot = snapshot;
      saveNotice("Autosaved on this device · Export JSON for a portable layout copy.");
    });
  } catch (_error) {
    autosaveReady = false;
    saveNotice("Autosave unavailable — export JSON before closing this page.", true);
  }
}

// No pagehide/unload write: an exiting stale tab must never replace a checkpoint.
// ---------- End checkpoint persistence ----------

let canvas, ctx;

function resize() {
  canvas.width = canvas.clientWidth * devicePixelRatio;
  canvas.height = canvas.clientHeight * devicePixelRatio;
  draw();
}

function worldToScreen(x, y) {
  return [ (x - view.x) * view.scale + canvas.clientWidth / 2,
           -(y - view.y) * view.scale + canvas.clientHeight / 2 ];
}
function screenToWorld(sx, sy) {
  return [ (sx - canvas.clientWidth / 2) / view.scale + view.x,
           -(sy - canvas.clientHeight / 2) / view.scale + view.y ];
}

// Elevation colour scale, one hue band per bridge-crest level (76.8mm each):
// grey, amber, brick red, purple, indigo, glacier blue, snow at level six.
// Climbing pieces get the gradient along their run, so up- vs down-ramps and
// stacked climbs read at a glance.
const ELEV_STOPS = [
  [0.0, [185, 190, 196]],
  [76.8, [214, 164, 76]],
  [153.6, [196, 94, 69]],
  [230.4, [142, 79, 150]],
  [307.2, [86, 96, 178]],
  [384.0, [70, 150, 180]],
  [460.8, [225, 230, 238]],
];
function elevColor(z) {
  const s = ELEV_STOPS;
  if (z <= s[0][0]) return `rgb(${s[0][1].join(",")})`;
  if (z >= s[s.length - 1][0]) return `rgb(${s[s.length - 1][1].join(",")})`;
  for (let i = 1; i < s.length; i++) {
    if (z <= s[i][0]) {
      const t = (z - s[i - 1][0]) / (s[i][0] - s[i - 1][0]);
      const c = s[i - 1][1].map((a, j) => Math.round(a + t * (s[i][1][j] - a)));
      return `rgb(${c.join(",")})`;
    }
  }
  return "rgb(185,190,196)";
}

function previewPlacements(candidate, state = S) {
  if (!candidate) return null;
  if (!candidate.format) return candidate.placements; // legacy API response
  if (candidate.format !== "duplotrain-preview/1" || !state ||
      !Array.isArray(candidate.placements) ||
      candidate.base_revision !== state.revision ||
      !Number.isInteger(candidate.base_count) || candidate.base_count < 0 ||
      candidate.base_count > state.layout.placements.length) return null;
  const base = state.layout.placements, previous = previewCache.get(candidate);
  if (previous?.base === base && previous.added === candidate.placements &&
      previous.count === candidate.base_count && previous.revision === state.revision) return previous.placements;
  const placements = base.slice(0, candidate.base_count).concat(candidate.placements);
  previewCache.set(candidate, {base, added: candidate.placements, count: candidate.base_count,
    revision: state.revision, placements});
  return placements;
}

function drawLayout(layout, ghost) {
  // Same-height segments of one piece share a fill/stroke, while ramps keep
  // their local elevation order. This avoids thousands of separate flat strokes.
  for (const batch of drawingBatches(layout.placements)) {
    ctx.beginPath();
    for (const segment of batch) {
      segment.edge.forEach(([x, y], i) => {
        const [sx, sy] = worldToScreen(x, y); i ? ctx.lineTo(sx, sy) : ctx.moveTo(sx, sy);
      });
      ctx.closePath();
    }
    ctx.fillStyle = ghost ? "rgba(44,138,75,.35)" : elevColor(batch[0].z); ctx.fill();
    if (!ghost) {
      ctx.beginPath();
      for (const segment of batch) for (const rail of segment.rails) {
        const a = worldToScreen(rail[0][0], rail[0][1]), b = worldToScreen(rail[1][0], rail[1][1]);
        ctx.moveTo(...a); ctx.lineTo(...b);
      }
      ctx.lineWidth = Math.max(1, 1.5 * view.scale); ctx.lineCap = "butt";
      ctx.strokeStyle = "#6d7278"; ctx.stroke();
    }
  }
}

function offsetLine(line, d) {
  const out = [];
  for (let i = 0; i < line.length; i++) {
    const a = line[Math.max(0, i - 1)], b = line[Math.min(line.length - 1, i + 1)];
    let nx = -(b[1] - a[1]), ny = b[0] - a[0];
    const len = Math.hypot(nx, ny) || 1;
    out.push([line[i][0] + nx / len * d, line[i][1] + ny / len * d]);
  }
  return out;
}

function openEndScreenPos() {
  const out = [];
  if (!S) return out;
  S.layout.placements.forEach((pl, i) => {
    for (const p of pl.ports) {
      if (!p.open || p.sealed) continue;
      const [sx, sy] = worldToScreen(p.x, p.y);
      out.push({ end: [i, p.port], x: sx, y: sy, deg: p.deg, name: p.name });
    }
  });
  return out;
}

function stoneMarkPositions() {
  // Screen positions of every drawn stone, mirroring the draw loop's layout.
  const out = [];
  if (!S) return out;
  S.layout.placements.forEach((pl, i) => {
    (pl.stone_marks || []).forEach((mark, k) => {
      let wx = pl.mid[0], wy = pl.mid[1];
      if (mark.at !== null && mark.at !== undefined && pl.ports[mark.at]) {
        const port = pl.ports[mark.at];
        wx = port.x * 0.82 + pl.mid[0] * 0.18;
        wy = port.y * 0.82 + pl.mid[1] * 0.18;
      }
      const [sx, sy] = worldToScreen(wx, wy);
      const r = Math.max(6, 14 * view.scale);
      const oy = (k - ((pl.stone_marks.length - 1) / 2)) * r * 2.2;
      out.push({ placement: i, id: mark.id, at_port: mark.at ?? null, x: sx, y: sy + oy, r });
    });
  });
  return out;
}

function placementAt(sx, sy) {
  return placementsAt(sx, sy)[0]?.placement ?? null;
}

function stoneMountAt(sx, sy) {
  if (!S) return null;
  let best = null;
  S.layout.placements.forEach((pl, i) => {
    if (!pl.stone_ok) return;
    // Near a connector face: position the stone AT that face (it then only acts on
    // trains running into it -- the reversing-terminator trick at a buffer).
    pl.ports.forEach((p) => {
      const [px, py] = worldToScreen(p.x, p.y);
      const d = Math.hypot(px - sx, py - sy);
      if (d < 20 && (!best || d < best.d)) best = { placement: i, at_port: p.port, d };
    });
    const [mx, my] = worldToScreen(pl.mid[0], pl.mid[1]);
    const d = Math.hypot(mx - sx, my - sy);
    if (d < 28 && (!best || d < best.d)) best = { placement: i, at_port: null, d };
  });
  return best;
}

function paint() {
  if (!ctx || !canvas) return;
  ctx.setTransform(devicePixelRatio, 0, 0, devicePixelRatio, 0, 0);
  ctx.clearRect(0, 0, canvas.clientWidth, canvas.clientHeight);
  if (!S) return;
  // faint 128mm grid
  ctx.lineWidth = 1;
  ctx.strokeStyle = "#e9e6df";
  const step = 128 * view.scale;
  if (step > 14) {
    const [wx0, wy0] = screenToWorld(0, canvas.clientHeight);
    const [wx1, wy1] = screenToWorld(canvas.clientWidth, 0);
    for (let gx = Math.floor(wx0 / 128) * 128; gx <= wx1; gx += 128) {
      const [sx] = worldToScreen(gx, 0);
      ctx.beginPath(); ctx.moveTo(sx, 0); ctx.lineTo(sx, canvas.clientHeight); ctx.stroke();
    }
    for (let gy = Math.floor(wy0 / 128) * 128; gy <= wy1; gy += 128) {
      const [, sy] = worldToScreen(0, gy);
      ctx.beginPath(); ctx.moveTo(0, sy); ctx.lineTo(canvas.clientWidth, sy); ctx.stroke();
    }
  }
  drawLayout(S.layout, false);
  const ghost = previewPlacements(preview);
  if (ghost) drawLayout({placements: ghost}, true);

  // action stones (mid-piece, or pulled toward the port face they guard)
  S.layout.placements.forEach((pl) => {
    (pl.stone_marks || []).forEach((mark, k) => {
      const info = S.stones.catalog[mark.id] || {};
      let wx = pl.mid[0], wy = pl.mid[1];
      if (mark.at !== null && mark.at !== undefined && pl.ports[mark.at]) {
        const port = pl.ports[mark.at];
        wx = port.x * 0.82 + pl.mid[0] * 0.18;
        wy = port.y * 0.82 + pl.mid[1] * 0.18;
      }
      const [sx, sy] = worldToScreen(wx, wy);
      const r = Math.max(6, 14 * view.scale);
      const oy = (k - ((pl.stone_marks.length - 1) / 2)) * r * 2.2;
      ctx.beginPath();
      ctx.arc(sx, sy + oy, r, 0, 7);
      ctx.fillStyle = info.color || "#888";
      ctx.fill();
      ctx.lineWidth = 2;
      ctx.strokeStyle = "#ffffff";
      ctx.stroke();
      if (mark.id === "stone_direction" && r > 7) {
        ctx.fillStyle = "#fff";
        ctx.font = `${r}px system-ui`;
        ctx.textAlign = "center";
        ctx.textBaseline = "middle";
        ctx.fillText("↔", sx, sy + oy + 1);
      }
    });
  });

  // joints + open-end arrows (+ sealed buffer faces)
  S.layout.placements.forEach((pl, i) => {
    for (const p of pl.ports) {
      const [sx, sy] = worldToScreen(p.x, p.y);
      if (p.sealed) {
        const rad = -p.deg * Math.PI / 180;
        const bx = Math.cos(rad + Math.PI / 2), by = Math.sin(rad + Math.PI / 2);
        const w = Math.max(8, 26 * view.scale);
        ctx.strokeStyle = "#8c1d18";
        ctx.lineWidth = 5;
        ctx.beginPath();
        ctx.moveTo(sx - bx * w, sy - by * w);
        ctx.lineTo(sx + bx * w, sy + by * w);
        ctx.stroke();
      } else if (!p.open) {
        ctx.fillStyle = "#4d5359";
        ctx.beginPath(); ctx.arc(sx, sy, 2.5, 0, 7); ctx.fill();
      } else {
        const picked = pickMode && pickMode.grow && pickMode.grow[0] === i && pickMode.grow[1] === p.port;
        const rad = -p.deg * Math.PI / 180;
        ctx.strokeStyle = picked ? "#2f6fdb" : "#d0342c";
        ctx.fillStyle = picked ? "#2f6fdb" : "#d0342c";
        ctx.lineWidth = 2.5;
        const len = Math.max(16, 30 * view.scale);
        const ex = sx + Math.cos(rad) * len, ey = sy + Math.sin(rad) * len;
        ctx.beginPath(); ctx.moveTo(sx, sy); ctx.lineTo(ex, ey); ctx.stroke();
        ctx.beginPath();
        ctx.arc(sx, sy, 5.5, 0, 7); ctx.fill();
        ctx.beginPath();
        ctx.moveTo(ex, ey);
        ctx.lineTo(ex + Math.cos(rad + 2.6) * 8, ey + Math.sin(rad + 2.6) * 8);
        ctx.lineTo(ex + Math.cos(rad - 2.6) * 8, ey + Math.sin(rad - 2.6) * 8);
        ctx.closePath(); ctx.fill();
      }
    }
  });
  drawHighlights();
  if (S.layout.placements.length === 0) {
    ctx.fillStyle = "#7a828a";
    ctx.font = "15px system-ui";
    ctx.textAlign = "center";
    ctx.fillText("Choose a piece, then tap or click the floor.",
                 canvas.clientWidth / 2, canvas.clientHeight / 2, canvas.clientWidth - 24);
  }
}

function fitView(placements = S && S.layout.placements) {
  if (!placements || !placements.length) { view = { x: 0, y: 0, scale: 0.9 }; return; }
  let x0 = 1e9, y0 = 1e9, x1 = -1e9, y1 = -1e9;
  for (const pl of placements)
    for (const line of pl.lines)
      for (const [x, y] of line) {
        x0 = Math.min(x0, x); x1 = Math.max(x1, x);
        y0 = Math.min(y0, y); y1 = Math.max(y1, y);
      }
  view.x = (x0 + x1) / 2; view.y = (y0 + y1) / 2;
  const pad = 180;
  view.scale = Math.min((canvas.clientWidth) / (x1 - x0 + pad),
                        (canvas.clientHeight) / (y1 - y0 + pad), 1.6);
}

// ---------- UI wiring ----------
function el(id) { return document.getElementById(id); }

function status(msg, cls) {
  const s = el("status");
  s.textContent = msg;
  s.className = cls || "";
}

function refreshStatus() {
  if (!S) return;
  const n = S.layout.placements.length;
  const opens = S.open_ends.length;
  const issues = S.layout.joint_issues || [];
  if (issues.length) {
    const first = issues[0];
    const forced = issues.every(joint => joint.problems.length === 1 &&
                                         joint.problems[0] === "planar gap");
    const gap = issues.reduce((sum, joint) => sum + joint.gap_mm, 0);
    status((S.layout.closed ? "Fully linked, but not exactly closed. " : `${opens} open end(s). `) +
           (forced ? `Forced fit: ${gap.toPrecision(4)} mm total planar gap; physical fit not verified. `
                   : "Incompatible joint geometry. ") +
           `${issues.length} joint(s) need attention. ` +
           `Joint ${first.a.join(":")} ↔ ${first.b.join(":")}: ` +
           `${first.problems.join(", ")}; height difference ${first.height_mm.toPrecision(4)} mm, ` +
           `heading error ${first.heading_error_deg}°.`, "err");
  } else if (S.layout.exactly_closed && n) {
    status(`Connectors closed — use Check layout for overlaps and stock. ${n} pieces, ${S.layout.size_cm[0]} × ${S.layout.size_cm[1]} cm`, "closed");
  } else if (pickMode) {
    status(pickMode.stage === "grow" ? "Pick the end to GROW from (click a red arrow)"
                                     : "Now pick the end to CLOSE onto");
  } else if (deleting) {
    status("Remove tool — tap a stone or piece. Undo restores it.");
  } else if (armedStone) {
    const info = S.stones.catalog[armedStone];
    status(`${info.name} armed — click a straight to clip it on (or off).`);
  } else if (armed) {
    status(`${armed.pieceName} — ${armed.label} armed. ` +
           (n ? "Click a red arrow to attach." : "Click anywhere to place it."));
  } else {
    status(n ? `${n} pieces, ${opens} open end(s), ${S.layout.size_cm[0]} × ${S.layout.size_cm[1]} cm`
             : "Empty floor. Arm a piece to begin.");
  }
  el("solve").disabled = solving || opens < 2;
  el("undo").disabled = solving || !S.can_undo;
  el("redo").disabled = solving || !S.can_redo;
  el("undo").title = S.undo_label ? `Undo ${S.undo_label}` : "Nothing to undo";
  el("redo").title = S.redo_label ? `Redo ${S.redo_label}` : "Nothing to redo";
}

// Retain controls while their catalogue structure is unchanged. In particular,
// redrawing geometry must not discard focus or an unsubmitted inventory value.
let paletteKey = null, setKey = null, stoneKey = null, candidateKey = null;
let paletteRows = [], stoneRows = [], candidateRows = [];

function renderPalette() {
  const key = JSON.stringify(S.palette);
  if (key !== paletteKey) {
    const pal = el("palette");
    pal.replaceChildren();
    paletteRows = S.palette.map(piece => {
      const div = document.createElement("div");
      div.className = "piece";
      div.dataset.pieceId = piece.id;
      const row = document.createElement("div");
      row.className = "row";
      const name = document.createElement("span");
      name.className = "name";
      name.textContent = piece.name + (piece.provisional ? " ⚠" : "");
      const count = document.createElement("span");
      count.className = "count";
      const label = document.createElement("span");
      const input = document.createElement("input");
      input.type = "number"; input.min = 0; input.max = 10000; input.step = 1;
      input.setAttribute("aria-label", `${piece.name} owned`);
      input.title = "how many you own";
      input.addEventListener("change", async () => {
        await submitInventory(piece.id, input, false);
      });
      count.append(label, input);
      row.append(name, count);
      const vs = document.createElement("div");
      vs.className = "variants";
      const buttons = piece.variants.map(v => {
        const b = document.createElement("button");
        b.textContent = v.label;
        b.addEventListener("click", () => {
          const same = armed && armed.piece === piece.id && armed.entry === v.entry && armed.exit === v.exit;
          selectTool(same ? {} : {
            piece: {piece: piece.id, pieceName: piece.name, entry: v.entry, exit: v.exit, label: v.label},
          });
          renderPalette(); renderStones(); refreshStatus(); draw();
        });
        vs.append(b);
        return {button: b, variant: v};
      });
      div.append(row, vs);
      pal.append(div);
      return {id: piece.id, label, input, buttons, owned: null};
    });
    paletteKey = key;
  }
  const unlimited = !!S.inventory.unlimited;
  el("unlimited").checked = unlimited;
  for (const row of paletteRows) {
    const remaining = S.inventory.remaining[row.id] ?? 0;
    const owned = S.inventory.owned[row.id] ?? 0;
    const label = unlimited ? "∞" : `${remaining}/`;
    if (row.label.textContent !== label) row.label.textContent = label;
    row.input.hidden = unlimited;
    if (row.owned !== owned) {
      row.input.value = owned;
      row.owned = owned;
    }
    for (const {button, variant: v} of row.buttons) {
      button.disabled = !unlimited && remaining <= 0;
      button.classList.toggle("armed", !!armed && armed.piece === row.id &&
                             armed.entry === v.entry && armed.exit === v.exit);
    }
  }
}

function renderSets() {
  const key = JSON.stringify(S.sets || []);
  if (key === setKey) return;
  const box = el("sets");
  box.replaceChildren();
  for (const s of (S.sets || [])) {
    const b = document.createElement("button");
    b.textContent = `+ ${s.code}`;
    b.title = `${s.name} (${s.year}): ` +
      Object.entries(s.pieces).map(([k, n]) => `${n}×${k}`).join(", ");
    b.addEventListener("click", async () => {
      try { S = await api("/api/add_set", { code: s.code }); redraw(); }
      catch (e) { status(e.message, "err"); }
    });
    box.append(b);
  }
  setKey = key;
}

function renderStones() {
  const key = JSON.stringify(S.stones.catalog);
  if (key !== stoneKey) {
    const box = el("stones");
    box.replaceChildren();
    stoneRows = Object.entries(S.stones.catalog).map(([sid, info]) => {
      const b = document.createElement("button");
      b.title = `${info.effect} — click a straight to clip on / off`;
      b.style.borderLeft = `14px solid ${info.color}`;
      b.addEventListener("click", () => {
        selectTool(armedStone === sid ? {} : {stone: sid});
        renderPalette(); renderStones(); refreshStatus(); draw();
      });
      const input = document.createElement("input");
      input.type = "number"; input.min = 0; input.max = 10000; input.step = 1;
      input.setAttribute("aria-label", `${info.name} owned`);
      input.addEventListener("change", () => submitInventory(sid, input, true));
      const row = document.createElement("div");
      row.className = "stone-inventory";
      row.append(b, input);
      box.append(row);
      return {sid, name: info.name.replace(" stone", ""), button: b, input, owned: null};
    });
    stoneKey = key;
  }
  const unlimited = !!S.inventory.unlimited;
  for (const row of stoneRows) {
    const {sid, name, button, input} = row;
    const owned = S.stones.owned?.[sid] ?? 0;
    input.hidden = unlimited;
    if (row.owned !== owned) { input.value = owned; row.owned = owned; }
    const remaining = S.stones.remaining[sid] ?? 0;
    const label = `${name} ×${unlimited ? "∞" : remaining}`;
    if (button.textContent !== label) button.textContent = label;
    button.classList.toggle("armed", armedStone === sid);
    button.disabled = !unlimited && remaining <= 0 && armedStone !== sid;
  }
}

function renderCandidates() {
  const candidates = S.candidates || [];
  const key = (c) => `${c.revision}:${c.index}`;
  const selected = candidates.find(c => key(c) === selectedCandidate);
  if (!selected) selectedCandidate = null;
  preview = selected ? selected.preview : null;
  // Previews can be large: compare only the card's metadata, not its geometry.
  const cards = JSON.stringify(candidates.map(({preview, ...card}) => card));
  if (cards !== candidateKey) {
    const box = el("cands");
    box.replaceChildren();
    candidateRows = candidates.map(c => {
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
      const apply = document.createElement("button");
      apply.textContent = "Apply";
      const row = {candidate: c, show, apply};
      show.addEventListener("click", () => {
        selectedCandidate = key(row.candidate);
        renderCandidates();
        draw();
      });
      apply.addEventListener("click", async () => {
        try {
          const current = row.candidate;
          S = await api("/api/apply", {index: current.index, revision: current.revision});
          selectedCandidate = null;
          fitted = false;
          redraw();
        } catch (e) { status(e.message, "err"); }
      });
      buttons.append(show, apply);
      div.append(buttons);
      div.addEventListener("pointerenter", (event) => {
        if (event.pointerType !== "touch") { preview = row.candidate.preview; draw(); }
      });
      div.addEventListener("pointerleave", () => {
        const chosen = (S.candidates || []).find(candidate => key(candidate) === selectedCandidate);
        preview = chosen ? chosen.preview : null;
        draw();
      });
      box.append(div);
      return row;
    });
    candidateKey = cards;
  }
  candidateRows.forEach((row, i) => {
    row.candidate = candidates[i];
    const active = key(row.candidate) === selectedCandidate;
    const label = active ? "Previewing" : "Preview";
    if (row.show.textContent !== label) row.show.textContent = label;
    row.show.setAttribute("aria-pressed", String(active));
    row.apply.disabled = !active;
  });
}

function redraw() {
  discardStaleInteraction();
  if (!fitted) { fitView(); fitted = true; }
  renderPalette(); renderSets(); renderStones(); renderCandidates();
  const rev = el("reversing");
  if (!rev.dataset.touched) {
    rev.checked = (S.stones.owned.stone_direction || 0) > 0;
  }
  if (lastSolve && lastSolve.revision !== S.revision) el("expand-search").hidden = true;
  renderNavigation();
  refreshStatus(); draw(); saveSession();
}

async function refresh() {
  S = await api("/api/state");
  if (!recoveryAttempted) {
    recoveryAttempted = true;
    await initializeRecovery();
  }
  redraw();
}

let importSequence = 0;

async function runSolve(grow, close, effort = 1) {
  if (solving || apiBusy || !S) return;
  selectTool();
  const maxPieces = Number(el("max-pieces").value);
  const slop = Number(el("slop").value);
  if (!Number.isInteger(maxPieces) || maxPieces < 1 || maxPieces > 128 || !Number.isFinite(slop) || slop < 0) {
    status("Use 1–128 added pieces and a finite, non-negative slop.", "err");
    return;
  }
  lastSolve = {grow, close, effort, revision: S.revision};
  el("expand-search").hidden = true;
  selectedCandidate = null;
  solving = true;
  el("solve").disabled = true;
  solveOperation = globalThis.crypto?.randomUUID?.() || null;
  el("cancel-search").hidden = false;
  status(effort > 1 ? `searching… ${effort}× search budget` : "searching…");
  try {
    S = await api("/api/solve", {
      grow, close,
      ...(solveOperation ? {operation_id: solveOperation} : {}),
      slop, max_pieces: maxPieces, search_effort: effort,
      max_results: 8,
      reversing: el("reversing").checked,
    });
    pickMode = null;
    lastSolve = {grow, close, effort, revision: S.revision};
    redraw();
    if (!S.candidates.length) {
      if (S.reason)
        status(S.reason, "err");
      else if (!S.complete)
        status(`No completion found within the search limits (${S.stop_reason}, ` +
               `${(S.searched || 0).toLocaleString()} states). A closure may still exist.`, "err");
      else
        status("No completion fits the remaining inventory under these settings.", "err");
    } else {
      status(`${S.candidates.length} suggestion(s)${S.complete ? "" : " (search limited)"} — Preview, then Apply.`);
    }
    el("expand-search").hidden = !!S.complete || (maxPieces >= 128 && effort >= 16);
  } catch (e) {
    pickMode = null;
    status(e.message, "err");
  } finally {
    solving = false;
    solveOperation = null;
    el("cancel-search").hidden = true;
    el("solve").disabled = !S || S.open_ends.length < 2;
    el("undo").disabled = !S || !S.can_undo;
  }
}

// Pointer events support mouse, pen and touch; capture keeps drags well-defined
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

async function activateAt(sx, sy) {
  if (!S || apiBusy || solving) return;
  if (pickMode && pickMode.revision !== S.revision) {
    pickMode = null;
    status("The layout changed. Select the endpoints again.", "err");
    return;
  }
  const hit = openEndScreenPos().map(p => ({...p, distance: Math.hypot(p.x - sx, p.y - sy)}))
    .filter(p => p.distance < 22).sort((a, b) => a.distance - b.distance)[0];
  try {
    if (pickMode) {
      if (hit) await activateEnd(hit.end);
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
      await activateEnd(hit.end);
    } else if (hit && S.matable.length) {
      const mate = S.matable.find(([a, b]) =>
        (a[0] === hit.end[0] && a[1] === hit.end[1]) || (b[0] === hit.end[0] && b[1] === hit.end[1]));
      if (mate) { S = await api("/api/join", {a: mate[0], b: mate[1]}); redraw(); }
    } else {
      const hits = placementsAt(sx, sy);
      if (hits.length > 1) showOverlapPicker(hits);
      else { selectedPiece = hits[0]?.placement ?? null; draw(); }
    }
  } catch (err) { status(err.message, "err"); }
}
async function removeAt(sx, sy) {
  if (!S || apiBusy || solving) return;
  try {
    const mark = stoneMarkPositions().find(m => Math.hypot(m.x - sx, m.y - sy) < Math.max(16, m.r + 4));
    if (mark) {
      S = await api("/api/stone", {
        placement: mark.placement, id: mark.id, at_port: mark.at_port, remove: true,
      });
    } else {
      const hits = placementsAt(sx, sy);
      if (hits.length > 1) { showOverlapPicker(hits, true); return; }
      const hit = placementAt(sx, sy);
      if (hit === null) return;
      S = await api("/api/remove", {placement: hit});
    }
    redraw();
  } catch (err) { status(err.message, "err"); }
}


// Bind only after the page is ready; tests can load the whole source without starting it.
function bindEditorEvents() {
  bindExtraEvents();
  window.addEventListener("storage", (event) => {
    if (!autosaveReady || (event.key !== null && event.key !== STORAGE_KEY)) return;
    try {
      // Read current storage: an event describing an older revision may be delayed.
      if (localStorage.getItem(STORAGE_KEY) !== savedCheckpoint) pauseAutosave();
    } catch (_error) {
      autosaveReady = false;
      saveNotice("Autosave unavailable — export JSON before closing this page.", true);
    }
  });
  document.addEventListener("visibilitychange", () => {
    if (document.hidden) saveSession();
  });
  window.addEventListener("beforeunload", (event) => {
    if (S && S.snapshot && JSON.stringify(S.snapshot) !== lastSavedSnapshot) {
      event.preventDefault();
      event.returnValue = "";
    }
  });
  window.addEventListener("resize", resize);
  if (window.ResizeObserver) new ResizeObserver(resize).observe(canvas);
  el("undo").addEventListener("click", async () => {
    try { S = await api("/api/undo", {}); redraw(); } catch (e) { status(e.message, "err"); }
  });
  el("clear").addEventListener("click", async () => {
    try {
      S = await api("/api/clear", {});
      selectTool();
      fitted = false;
      redraw();
      status("Floor cleared — Undo restores it.");
    } catch (e) { status(e.message, "err"); }
  });
  el("export").addEventListener("click", () => {
    try {
      if (!S) throw new Error("The editor is still loading; try exporting again when it finishes.");
      downloadJSON(S.snapshot.layout, "layout.json");
    } catch (e) { status(e.message, "err"); }
  });
  el("import").addEventListener("click", () => el("importfile").click());
  el("importfile").addEventListener("change", async (e) => {
    const file = e.target.files && e.target.files[0];
    e.target.value = "";
    if (!file) return;
    // A slow read must not replace a newer selection or adopt an intervening edit.
    const selection = ++importSequence, revision = S && S.revision;
    if (file.size > 2 * 1024 * 1024) {
      status("import refused: file larger than 2 MB", "err");
      return;
    }
    let data;
    try {
      data = JSON.parse(await file.text());
    } catch (err) {
      if (selection === importSequence) status("import refused: not valid JSON", "err");
      return;
    }
    if (selection !== importSequence) return;
    try {
      S = await api("/api/import", { data, revision });
      clearTransient();
      fitted = false;
      redraw();
      if (selection === importSequence && !S.layout.joint_issues.length)
        status(`imported ${S.layout.placements.length} pieces.`);
    } catch (err) {
      if (selection === importSequence) status(`import refused: ${err.message}`, "err");
    }
  });
  el("solve").addEventListener("click", async () => {
    if (!S || solving || apiBusy) return;
    const opens = S.open_ends.length;
    if (opens > 2) {
      selectTool({pick: {stage: "grow", grow: null}});
      renderPalette(); renderStones(); refreshStatus(); draw();
      return;
    }
    await runSolve(null, null);
  });
  el("expand-search").addEventListener("click", async () => {
    if (solving || apiBusy || !S) return;
    el("max-pieces").value = Math.min(128, Math.max(1, Number(el("max-pieces").value)) * 2);
    if (!lastSolve || lastSolve.revision !== S.revision) { el("solve").click(); return; }
    await runSolve(lastSolve.grow, lastSolve.close, Math.min(16, lastSolve.effort * 2));
  });
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
    if (!old) {
      if (S && e.pointerType !== "touch") {
        const p = canvasPoint(e);
        hoveredPiece = placementAt(p.x, p.y); draw();
      }
      return;
    }
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
  window.addEventListener("keydown", (e) => {
    if (!S || apiBusy || e.target.closest("input, textarea, [contenteditable='true']")) return;
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "z") {
      e.preventDefault();
      el(e.shiftKey ? "redo" : "undo").click();
    }
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "y") {
      e.preventDefault(); el("redo").click();
    }
    if (e.key === "Escape") {
      selectTool(); selectedPiece = null; hoveredPiece = null;
      el("overlap-picker").hidden = true;
      renderPalette(); renderStones(); refreshStatus(); draw();
    }
  });
  el("reversing").addEventListener("change", (e) => { e.target.dataset.touched = "1"; });
  el("unlimited").addEventListener("change", async (e) => {
    try { S = await api("/api/unlimited", { on: e.target.checked }); redraw(); }
    catch (err) { status(err.message, "err"); e.target.checked = !!(S && S.inventory.unlimited); }
  });
}

function initializeEditor() {
  canvas = el("canvas");
  ctx = canvas.getContext("2d");
  bindEditorEvents();
  renderProjects();
  resize();
  if (window.duplotrainBoot) {
    window.duplotrainBoot({ refresh, status,
      checkpoint: () => S && S.snapshot,
      downloadLayout: () => S && downloadJSON(S.snapshot.layout, "layout-recovered.json"),
      downloadSession: () => S && downloadJSON(S.snapshot, "session-recovered.json"),
      restored: (state) => { S = state; clearTransient(); redraw(); },
      readyStatus: (message) => {
      if (!S.layout.joint_issues.length) status(message);
    }});
  } else {
    refresh().catch(e => status(e.message, "err"));
  }
}

document.addEventListener("DOMContentLoaded", initializeEditor, {once: true});

// ---------- Revision-scoped tools, diagnostics and projects ----------
let interactionRevision = null, navigationRevision = null;
let selectedPiece = null, hoveredPiece = null, highlightedPieces = [];
let trainTrace = null, trainStep = -1, trainTimer = null, solveOperation = null;
let framePending = false;
const segmentCache = new WeakMap(), batchCache = new WeakMap(), previewCache = new WeakMap();
const PROJECT_FORMAT = "duplotrain-project/1";
const PROJECT_PREFIX = PROJECT_FORMAT + ":" + location.pathname + ":";

function draw() {
  if (framePending) return;
  if (typeof requestAnimationFrame !== "function") { paint(); return; }
  framePending = true;
  requestAnimationFrame(() => { framePending = false; paint(); });
}

function stopTrain() {
  if (trainTimer !== null) clearInterval(trainTimer);
  trainTimer = null;
}
function clearTransient() {
  pickMode = null; selectedCandidate = null; preview = null; lastSolve = null;
  selectedPiece = null; hoveredPiece = null; highlightedPieces = [];
  stopTrain(); trainTrace = null; trainStep = -1;
  navigationRevision = null;
  for (const id of ["overlap-picker", "expand-search"]) if (el(id)) el(id).hidden = true;
  for (const id of ["diagnostics", "train-report"]) if (el(id)) el(id).textContent = "";
  for (const id of ["train-play", "train-step"]) if (el(id)) el(id).disabled = true;
}
function discardStaleInteraction() {
  if (!S) return;
  if (interactionRevision !== null && interactionRevision !== S.revision) {
    // Keep deliberately armed pieces/stones, but never reassign old index picks.
    const last = lastSolve;
    clearTransient();
    if (last?.revision === S.revision) lastSolve = last;
  }
  if (pickMode && pickMode.revision !== S.revision) pickMode = null;
  interactionRevision = S.revision;
}

async function submitInventory(id, input, stone) {
  const submitted = input.value;
  try { S = await api("/api/inventory", {counts: {[id]: submitted}}); redraw(); }
  catch (error) {
    // Do not destroy a newer unsubmitted draft while the previous request waits.
    if (input.value === submitted) input.value = (stone ? S.stones.owned : S.inventory.owned)[id] ?? 0;
    status(error.message, "err");
  }
}

function strokeSegment(a, b, width, color, cap = "round") {
  const [ax, ay] = worldToScreen(a[0], a[1]), [bx, by] = worldToScreen(b[0], b[1]);
  ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(bx, by);
  ctx.lineWidth = width; ctx.lineCap = cap; ctx.lineJoin = "round";
  ctx.strokeStyle = color; ctx.stroke();
}
const interpolate = (a, b, t) => [0, 1, 2].map(i => (a[i] || 0) + ((b[i] || 0) - (a[i] || 0)) * t);
function drawingSegments(placements) {
  if (segmentCache.has(placements)) return segmentCache.get(placements);
  const segments = [];
  placements.forEach((pl, placement) => {
    for (const line of pl.lines) {
      const rails = [offsetLine(line, 24), offsetLine(line, -24)];
      const edges = [offsetLine(line, pl.width / 2), offsetLine(line, -pl.width / 2)];
      for (let i = 0; i + 1 < line.length; i++) {
        const a = line[i], b = line[i + 1];
        // Bound ramp-local paint order even for sparse/custom preview geometry.
        const divisions = Math.min(256, Math.max(1, Math.ceil(Math.hypot(b[0] - a[0], b[1] - a[1]) / 8)));
        for (let j = 0; j < divisions; j++) {
          const from = j / divisions, to = (j + 1) / divisions;
          const start = interpolate(a, b, from), end = interpolate(a, b, to);
          segments.push({placement, a: start, b: end, width: pl.width,
            z: (start[2] + end[2]) / 2,
            edge: [interpolate(edges[0][i], edges[0][i + 1], from),
              interpolate(edges[0][i], edges[0][i + 1], to),
              interpolate(edges[1][i], edges[1][i + 1], to),
              interpolate(edges[1][i], edges[1][i + 1], from)],
            rails: rails.map(r => [interpolate(r[i], r[i + 1], from), interpolate(r[i], r[i + 1], to)])});
        }
      }
    }
  });
  segments.sort((a, b) => a.z - b.z || a.placement - b.placement);
  segments.forEach((s, order) => { s.order = order; });
  segmentCache.set(placements, segments);
  return segments;
}
function drawingBatches(placements) {
  if (batchCache.has(placements)) return batchCache.get(placements);
  const batches = [];
  for (const segment of drawingSegments(placements)) {
    const batch = batches[batches.length - 1], previous = batch?.[0];
    if (previous && previous.z === segment.z && previous.placement === segment.placement) batch.push(segment);
    else batches.push([segment]);
  }
  batchCache.set(placements, batches);
  return batches;
}

function placementsAt(sx, sy) {
  if (!S) return [];
  const hits = new Map();
  for (const seg of drawingSegments(S.layout.placements)) {
    const [ax, ay] = worldToScreen(seg.a[0], seg.a[1]), [bx, by] = worldToScreen(seg.b[0], seg.b[1]);
    const dx = bx - ax, dy = by - ay;
    const t = Math.max(0, Math.min(1, ((sx - ax) * dx + (sy - ay) * dy) / (dx * dx + dy * dy || 1)));
    const d = Math.hypot(sx - ax - t * dx, sy - ay - t * dy);
    const half = seg.width * view.scale / 2;
    if (d >= Math.max(14, half)) continue;
    const hit = {placement: seg.placement, d, z: seg.z, order: seg.order, painted: d < half};
    const prev = hits.get(hit.placement);
    if (!prev || compareHits(hit, prev) < 0) hits.set(hit.placement, hit);
  }
  return [...hits.values()].sort(compareHits);
}
function compareHits(a, b) {
  // Painted area wins over hit-padding; within it the last painted surface wins.
  return Number(b.painted) - Number(a.painted) ||
    (a.painted && b.painted ? b.z - a.z || b.placement - a.placement : a.d - b.d) || a.d - b.d;
}
function drawHighlights() {
  const indices = new Set([...highlightedPieces, selectedPiece, hoveredPiece]);
  for (const index of indices) {
    const pl = S.layout.placements[index];
    if (!pl) continue;
    for (const line of pl.lines) for (let i = 0; i + 1 < line.length; i++)
      strokeSegment(line[i], line[i + 1], 3, "#2f6fdb");
  }
  if (trainTrace?.revision === S.revision) {
    const step = trainTrace.steps[trainStep];
    const pl = S.layout.placements[step ? step[0] : trainTrace.start[0]];
    if (pl) for (const line of pl.lines) for (let i = 0; i + 1 < line.length; i++)
      strokeSegment(line[i], line[i + 1], 5, "#9a3c9c");
  }
}
function focusPieces(indices) {
  highlightedPieces = indices.filter(i => Number.isInteger(i) && S.layout.placements[i]);
  if (highlightedPieces.length) { fitView(highlightedPieces.map(i => S.layout.placements[i])); fitted = true; }
  draw();
}
function showOverlapPicker(hits, remove = false) {
  const box = el("overlap-picker"), revision = S.revision;
  box.replaceChildren(); box.hidden = false;
  const title = document.createElement("strong");
  title.textContent = remove ? "Choose the piece to remove" : "Overlapping pieces";
  const select = document.createElement("select"); select.setAttribute("aria-label", "Overlapping piece");
  hits.forEach(hit => {
    const option = document.createElement("option"); option.value = hit.placement;
    option.textContent = `#${hit.placement + 1} ${S.layout.placements[hit.placement].name} · ${hit.z.toFixed(1)} mm`;
    select.append(option);
  });
  selectedPiece = hits[0].placement;
  select.addEventListener("change", () => { if (S.revision === revision) { selectedPiece = Number(select.value); draw(); } });
  const confirm = document.createElement("button"); confirm.textContent = remove ? "Remove highlighted piece" : "Select highlighted piece";
  confirm.addEventListener("click", async () => {
    if (S.revision !== revision || apiBusy) return;
    if (remove) {
      try { S = await api("/api/remove", {placement: selectedPiece, revision}); redraw(); }
      catch (error) { status(error.message, "err"); }
    }
    box.hidden = true; draw();
  });
  const cancel = document.createElement("button"); cancel.textContent = "Cancel";
  cancel.addEventListener("click", () => { box.hidden = true; selectedPiece = null; draw(); });
  box.append(title, select, confirm, cancel); select.focus(); draw();
}

async function activateEnd(end) {
  if (!S || apiBusy || solving) return;
  if (pickMode && pickMode.revision !== S.revision) { pickMode = null; status("Select the endpoints again.", "err"); return; }
  if (!S.open_ends.some(e => e[0] === end[0] && e[1] === end[1])) return;
  if (pickMode?.stage === "grow") {
    selectTool({pick: {stage: "close", grow: end}}); refreshStatus(); draw();
  } else if (pickMode) {
    if (pickMode.grow[0] === end[0] && pickMode.grow[1] === end[1]) {
      status("Choose a different open end to close onto.", "err"); return;
    }
    await runSolve(pickMode.grow, end);
  } else if (armed) {
    S = await api("/api/attach", {piece: armed.piece, entry: armed.entry, at: end}); redraw();
  } else {
    const mate = S.matable.find(pair => pair.some(e => e[0] === end[0] && e[1] === end[1]));
    if (mate) { S = await api("/api/join", {a: mate[0], b: mate[1]}); redraw(); }
    else status("Arm a piece or choose Close the loop first.");
  }
}
function renderNavigation() {
  if (!S || navigationRevision === S.revision || !document.createElement) return;
  const pieces = el("piece-select"), ends = el("end-select"), starts = el("train-start");
  if (!pieces?.replaceChildren || !ends?.replaceChildren || !starts?.replaceChildren) return;
  pieces.replaceChildren(); ends.replaceChildren(); starts.replaceChildren();
  const add = (select, value, label) => {
    const option = document.createElement("option"); option.value = value; option.textContent = label; select.append(option);
  };
  S.layout.placements.forEach((pl, i) => {
    add(pieces, i, `#${i + 1} ${pl.name}`);
    pl.ports.forEach(p => {
      if (!p.sealed) add(starts, JSON.stringify([i, p.port]), `#${i + 1} ${pl.name} — enter ${p.name}`);
    });
  });
  S.open_ends.forEach(end => add(ends, JSON.stringify(end), `#${end[0] + 1} ${S.layout.placements[end[0]].name} — port ${end[1]}`));
  for (const id of ["remove-selected", "test-train"]) el(id).disabled = !S.layout.placements.length;
  el("use-end").disabled = !S.open_ends.length;
  navigationRevision = S.revision;
}
async function checkLayout() {
  try {
    const report = await api("/api/check", {});
    if (report.revision !== S.revision) return;
    const box = el("diagnostics"); box.replaceChildren();
    const row = (text, indices = []) => {
      const line = document.createElement(indices.length ? "button" : "p"); line.textContent = text;
      if (indices.length) line.addEventListener("click", () => { if (S.revision === report.revision) focusPieces(indices); });
      box.append(line);
    };
    row(report.connector_closed ? "Connectors: exactly closed" : `Connectors: ${report.open_ends.length} open end(s)`, report.open_ends.map(e => e[0]));
    report.joint_issues.forEach(j => row(`Joint #${j.a[0] + 1} ↔ #${j.b[0] + 1}: ${j.problems.join(", ")}`, [j.a[0], j.b[0]]));
    row(`Overlaps: ${report.overlaps.length}${report.overlap_check_complete ? "" : "+ (report limit reached; check incomplete)"}`);
    report.overlaps.forEach(pair => row(`Overlap: piece #${pair[0] + 1} and #${pair[1] + 1}`, pair));
    row(report.missing.length ? `Stock shortages${report.sandbox ? " (sandbox ignores these)" : ""}:` : "Stock: sufficient");
    report.missing.forEach(m => row(`${m.name}: ${m.missing} missing (${m.used} used, ${m.owned} owned)`, m.placements));
    row(`Provisional geometry: ${report.provisional.length} piece(s)`, report.provisional);
    row(report.model_note);
  } catch (error) { status(error.message, "err"); }
}

function downloadJSON(data, filename) {
  const blob = new Blob([JSON.stringify(data, null, 2)], {type: "application/json"});
  const url = URL.createObjectURL(blob), anchor = document.createElement("a");
  anchor.href = url; anchor.download = filename; anchor.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
function projectSnapshot() {
  if (!S?.snapshot) throw new Error("Wait for the editor to finish loading");
  const name = el("project-name").value.trim() || "Untitled track";
  const max_pieces = Number(el("max-pieces").value), slop = Number(el("slop").value);
  if (name.length > 80 || !Number.isInteger(max_pieces) || max_pieces < 1 || max_pieces > 128 || !Number.isFinite(slop) || slop < 0 || slop > 1e9)
    throw new Error("Use a name up to 80 characters and valid search settings before saving");
  return {format: PROJECT_FORMAT, name, session: S.snapshot,
    preferences: {view: {...view}, search: {max_pieces, slop, reversing: el("reversing").checked}}};
}
async function openProject(data, revision = S && S.revision) {
  // Emergency session downloads use the already supported session format.
  if (data?.format === "duplotrain-session/1") data = {format: PROJECT_FORMAT, name: "Recovered session", session: data, preferences: {}};
  const next = await api("/api/project/open", {data, revision});
  S = next; clearTransient();
  el("project-name").value = next.project.name;
  const prefs = next.project.preferences;
  if (prefs.search) {
    el("max-pieces").value = prefs.search.max_pieces; el("slop").value = prefs.search.slop;
    el("reversing").checked = prefs.search.reversing; el("reversing").dataset.touched = "1";
  }
  if (prefs.view) { view = {...prefs.view}; fitted = true; } else fitted = false;
  redraw(); status(`Opened project: ${next.project.name}`);
}
function renderProjects() {
  const select = el("project-slots"); select.replaceChildren();
  try {
    for (let i = 0; i < localStorage.length; i++) {
      const key = localStorage.key(i);
      if (!key.startsWith(PROJECT_PREFIX)) continue;
      const option = document.createElement("option"); option.value = key;
      const raw = localStorage.getItem(key);
      try {
        if (raw.length > 2 * 1024 * 1024) throw new Error("too large");
        const data = JSON.parse(raw); option.textContent = data.name || "Untitled track";
      } catch (_) { option.textContent = "Unreadable saved project (kept)"; }
      select.append(option);
    }
  } catch (error) { status(`Local projects unavailable: ${error.message}. Download a project instead.`, "err"); }
}
async function saveLocalProject() {
  try {
    const data = projectSnapshot(), raw = JSON.stringify(data);
    if (raw.length > 2 * 1024 * 1024) throw new Error("project larger than 2 MB");
    // Append-only UUID slots avoid cross-tab overwrites, even for identical names.
    const key = PROJECT_PREFIX + crypto.randomUUID();
    localStorage.setItem(key, raw); renderProjects(); el("project-slots").value = key;
    status("Saved a new local project copy. Download project for a portable backup.");
  } catch (error) { status(`Project not saved: ${error.message}`, "err"); }
}
async function readProjectFile(event) {
  const file = event.target.files?.[0]; event.target.value = "";
  if (!file) return;
  const sequence = ++importSequence, revision = S && S.revision;
  try {
    if (file.size > 2 * 1024 * 1024) throw new Error("file larger than 2 MB");
    const data = JSON.parse(await file.text());
    if (sequence !== importSequence) return;
    await openProject(data, revision);
  } catch (error) { if (sequence === importSequence) status(`Project not opened: ${error.message}`, "err"); }
}
async function testTrain() {
  stopTrain();
  try {
    const start = JSON.parse(el("train-start").value);
    const trace = await api("/api/drive", {start, max_steps: 10000});
    if (trace.revision !== S.revision) return;
    trainTrace = trace; trainStep = -1; showTrainStep(); draw();
  } catch (error) { status(error.message, "err"); }
}
function showTrainStep() {
  if (!trainTrace || trainTrace.revision !== S?.revision) { stopTrain(); return; }
  const t = trainTrace, step = t.steps[trainStep];
  el("train-report").textContent = t.outcome === "limit" ? "10,000-step limit reached; no verdict made." :
    `Model result from this start: ${t.outcome}. ${t.visited.length} pieces visited; ${t.reversals} reversal(s)` +
    `${t.period === null ? "" : `; cycle ${t.period} steps`}. Default switch tongues; not a claim about every start.` +
    (step ? ` Step ${trainStep + 1}/${t.steps.length}: #${step[0] + 1}, port ${step[1]} → ${step[2]}.` : "");
  el("train-step").disabled = !t.steps.length;
  el("train-play").disabled = !t.steps.length;
  draw();
}
function advanceTrain() {
  if (!trainTrace || trainTrace.revision !== S?.revision || !trainTrace.steps.length) { stopTrain(); return; }
  if (trainStep + 1 >= trainTrace.steps.length) {
    if (trainTrace.cycle_start !== null) trainStep = trainTrace.cycle_start;
    else { stopTrain(); return; }
  } else trainStep++;
  showTrainStep();
}
async function cancelSearch() {
  if (!solving) return;
  try {
    if (window.duplotrainCancel) await window.duplotrainCancel();
    else if (solveOperation) {
      const result = await fetch("/api/cancel", {method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify({operation_id: solveOperation})});
      if (!result.ok) throw new Error("Cancellation request was rejected");
      const response = await result.json();
      status(response.cancelled ? "Cancelling search at its next checkpoint…" : "Search already finished or is not yet active; retry cancellation.");
    } else status("Cancellation is unavailable for this request; the current layout can still be exported.");
  } catch (error) { status(error.message, "err"); }
}
function bindExtraEvents() {
  const on = (id, action) => el(id)?.addEventListener("click", action);
  on("redo", async () => { try { S = await api("/api/redo", {}); redraw(); } catch (error) { status(error.message, "err"); } });
  on("cancel-search", cancelSearch);
  on("check-layout", checkLayout);
  on("fit-preview", () => { const pl = previewPlacements(preview); if (pl) { fitView(pl); fitted = true; draw(); } });
  on("use-end", async () => { try { await activateEnd(JSON.parse(el("end-select").value)); } catch (e) { status(e.message, "err"); } });
  on("place-first", async () => {
    if (!S || S.layout.placements.length || !armed) { status("Arm a piece on an empty layout first."); return; }
    try { S = await api("/api/attach", {piece: armed.piece, entry: armed.entry, at: null}); fitted = false; redraw(); } catch (e) { status(e.message, "err"); }
  });
  on("remove-selected", async () => {
    if (apiBusy || !S) return;
    const placement = Number(el("piece-select").value);
    if (!S.layout.placements[placement]) return;
    try { S = await api("/api/remove", {placement}); redraw(); } catch (e) { status(e.message, "err"); }
  });
  el("piece-select")?.addEventListener("change", () => { selectedPiece = Number(el("piece-select").value); focusPieces([selectedPiece]); });
  el("end-select")?.addEventListener("change", () => { try { focusPieces([JSON.parse(el("end-select").value)[0]]); } catch (_) {} });
  on("save-project", () => { try { downloadJSON(projectSnapshot(), "project.json"); } catch (e) { status(e.message, "err"); } });
  on("open-project", () => el("projectfile").click());
  el("projectfile")?.addEventListener("change", readProjectFile);
  on("save-local", saveLocalProject);
  on("load-local", async () => {
    const revision = S && S.revision;
    try {
      const raw = localStorage.getItem(el("project-slots").value);
      if (!raw || raw.length > 2 * 1024 * 1024) throw new Error("No readable project selected");
      await openProject(JSON.parse(raw), revision);
    } catch (e) { status(e.message, "err"); }
  });
  on("refresh-projects", renderProjects);
  on("test-train", testTrain); on("train-step", () => { stopTrain(); advanceTrain(); });
  on("train-play", () => {
    stopTrain();
    if (trainTrace?.revision !== S?.revision || !trainTrace?.steps.length) return;
    if (trainTrace.cycle_start === null && trainStep + 1 >= trainTrace.steps.length) trainStep = -1;
    advanceTrain(); trainTimer = setInterval(advanceTrain, 500);
  });
  on("train-pause", stopTrain);
  canvas.addEventListener("pointerleave", () => { hoveredPiece = null; draw(); });
  canvas.addEventListener("keydown", e => {
    if (e.key === "Enter") { e.preventDefault(); el("use-end").click(); }
  });
}
