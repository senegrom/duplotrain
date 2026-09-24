"use strict";
// Transport: the local `duplotrain gui` server answers over HTTP; the static web
// build (see webapp/) installs window.duplotrainApi to run the same Python engine
// in-browser via Pyodide. Checked at call time so either host works unmodified.
let apiBusy = false;
async function send(path, body) {
  if (window.duplotrainApi) return window.duplotrainApi(path, body);
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
}
async function api(path, body, fromJob = false) {
  if (apiBusy) throw new Error("An action is still running; try again when it finishes.");
  // Between its ticks a search or route analysis still owns the session: another
  // action would change it or take the engine from the job's next tick.
  if (jobLoop && !fromJob) throw new Error("A search or route analysis is running; pause it first.");
  apiBusy = true;
  refreshBusy();
  try {
    // Legacy API clients still receive full previews. This editor opts into the
    // versioned drawing-only contract; state reads use the existing read-only POST.
    if (path !== "/api/export") body = {...body, preview_format: "duplotrain-preview/1"};
    if (body !== undefined && path !== "/api/state" && path !== "/api/export") {
      // Capture the state and engine the user acted on; never fill in a newer
      // revision after an await. Preserve an explicit candidate revision as well.
      body = {revision: S && S.revision, ...(S?.instance ? {instance: S.instance} : {}), ...body};
    }
    return await send(path, body);
  } catch (error) {
    if (error.code === "stale_revision" && error.state) await adoptConflictState(error);
    throw error; // Refresh only: never replay a stale deletion/attachment.
  } finally {
    apiBusy = false;
    refreshBusy();
  }
}
// One busy state for a single request or a whole engine job: a job's ticks must
// not flicker the controls (or let clicks through) between their requests.
function refreshBusy() { document.body.classList.toggle("busy", apiBusy || jobLoop); }
async function adoptConflictState(error) {
  const current = error.state;
  if (S?.snapshot && S.instance && current.instance !== S.instance && current.revision === 0) {
    // A restarted engine, such as a new local server on the same port, starts
    // empty. Restore the newest confirmed session there rather than adopting,
    // and autosaving over, the empty one: this tab's own, unless another tab
    // autosaved since this tab last did. If another tab restored first, adopt it.
    const newer = newerCheckpoint();
    try {
      S = await send("/api/restore", {data: newer || S.snapshot, revision: 0, instance: current.instance,
                                      preview_format: "duplotrain-preview/1"});
      error.message = (newer ? "The editor engine restarted; the session another tab saved last was " :
        "The editor engine restarted; this tab's last confirmed session was ") +
        "restored and undo history reset. Your last action was not applied.";
    } catch (restoreError) {
      if (restoreError.code !== "stale_revision" || !restoreError.state) {
        error.message = "The editor engine restarted and restoring this tab's session failed " +
          `(${restoreError.message}). Export JSON or reload before editing.`;
        return;
      }
      S = restoreError.state;
    }
    clearTransient();
  } else {
    // Another engine counts revisions afresh: nothing bound to this tab's
    // revision numbers (picks, selectors, traces) may carry over to its state.
    if (S?.instance && current.instance !== S.instance) clearTransient();
    S = error.state;
  }
  selectTool();
  selectedCandidate = null;
  preview = null;
  el("expand-search").hidden = true;
  redraw();
}

// One API snapshot owner. The companion geometry, projects and train scripts
// read this state; successful API operations publish their new snapshot here.
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
let recoveryAttempted = false;
let autosaveReady = false;

// Tool changes are exclusive: a stone can never intercept an endpoint pick.
function selectTool({piece = null, stone = null, pick = null, remove = false} = {}) {
  closeOverlapPicker();
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

// The session another tab autosaved after this tab's last save or read, if any.
function newerCheckpoint() {
  try {
    const stored = localStorage.getItem(STORAGE_KEY);
    return stored !== null && stored !== savedCheckpoint ? decodeCheckpoint(stored) : null;
  } catch (_error) { return null; } // unreadable: this tab's own session is all there is
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
  drawFloorConstraints();
  drawBaseTrack(S.layout);
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
      if (!screenBoundsVisible(sx, sy + oy, sx, sy + oy, r + 3)) return;
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
      if (!screenBoundsVisible(sx, sy, sx, sy, Math.max(45, 40 * view.scale))) continue;
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
  const candidates = visibleCandidates();
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
          if (solving) return;
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
        const chosen = visibleCandidates().find(candidate => key(candidate) === selectedCandidate);
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
    row.apply.disabled = !active || solving;
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
  renderNavigation(); renderSearchOptions(); renderJobControls();
  refreshStatus(); updateProjectStatus(); draw(); saveSession();
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
  closeOverlapPicker(); clearHover();
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
  closeOverlapPicker(); clearHover();
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
    if (event.key === null || (typeof event.key === "string" && event.key.startsWith(PROJECT_PREFIX))) renderProjects();
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
    await startInteractiveSearch(null, null);
  });
  el("expand-search").addEventListener("click", async () => {
    if (solving || apiBusy || !S || interactiveJob?.revision !== S.revision) return;
    await continueSearch(true);
  });
  canvas.addEventListener("pointerdown", (e) => {
    if (e.button !== 0 || !S) return;
    e.preventDefault();
    clearHover();
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
        queueHover(p.x, p.y);
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
      pointers.delete(e.pointerId); clearHover();
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
    if (!e.deltaY) return; // a sideways swipe is not a zoom
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
  bindOfflineEvents();
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

// ---------- Revision-scoped tools and diagnostics ----------
// Pure drawing caches live in editor-geometry.js, project bookkeeping in
// editor-projects.js and trace state in editor-train.js. All deferred sources
// are loaded before the single DOMContentLoaded initializer above runs.
let interactionRevision = null, navigationRevision = null;
let selectedPiece = null, hoveredPiece = null, highlightedPieces = [];
let framePending = false, pendingHover = null, activeOverlap = null;
let repaintPending = false;
function draw() { scheduleFrame(true); }
function scheduleFrame(repaint) {
  repaintPending = repaintPending || repaint;
  if (framePending) return;
  const finish = () => {
    framePending = false;
    const changed = flushHover(), render = repaintPending || changed;
    if (repaintPending) updateProjectStatus();
    repaintPending = false;
    // Preserve the upstream optimization: unchanged hover never repaints track.
    if (render) paint();
  };
  if (typeof requestAnimationFrame !== "function") { finish(); return; }
  framePending = true;
  requestAnimationFrame(finish);
}

function queueHover(x, y) {
  pendingHover = S ? {x, y, revision: S.revision, placements: S.layout.placements} : null;
  scheduleFrame(false);
}
function flushHover() {
  const pointer = pendingHover; pendingHover = null;
  if (!pointer || pointers.size || activeOverlap || pointer.revision !== S?.revision ||
      pointer.placements !== S?.layout.placements) return false;
  const hovered = placementAt(pointer.x, pointer.y), changed = hovered !== hoveredPiece;
  hoveredPiece = hovered;
  return changed;
}
function clearHover() { pendingHover = null; hoveredPiece = null; }
function closeOverlapPicker() {
  activeOverlap = null;
  const box = el("overlap-picker");
  if (box) box.hidden = true;
}
function clearTransient() {
  clearInteractiveState();
  pickMode = null; selectedCandidate = null; preview = null;
  selectedPiece = null; clearHover(); highlightedPieces = []; closeOverlapPicker();
  invalidateTrain(); initialSwitches = {};
  navigationRevision = null;
  for (const id of ["overlap-picker", "expand-search"]) if (el(id)) el(id).hidden = true;
  for (const id of ["diagnostics", "train-report"]) if (el(id)) el(id).textContent = "";
  for (const id of ["train-play", "train-step"]) if (el(id)) el(id).disabled = true;
}
function discardStaleInteraction() {
  if (!S) return;
  discardInteractiveJob();
  if (interactionRevision !== null && interactionRevision !== S.revision) {
    // Keep deliberately armed pieces/stones, but never reassign old index picks.
    clearTransient();
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

function drawHighlights() {
  const indices = new Set(activeOverlap ? [activeOverlap.target] : [...highlightedPieces, selectedPiece, hoveredPiece]);
  if (trainTrace?.revision === S.revision && trainTrace.complete) {
    const overlays = [["train-unvisited", trainTrace.unvisited, "#be6712"],
      ["train-cycle", trainTrace.cycle_pieces, "#168277"]];
    for (const [id, pieces, color] of overlays) if (el(id)?.checked) {
      for (const index of pieces || []) {
        const pl = S.layout.placements[index];
        if (pl) for (const line of pl.lines) for (let i = 0; i + 1 < line.length; i++)
          strokeSegment(line[i], line[i + 1], 6, color);
      }
    }
  }
  for (const index of indices) {
    const pl = S.layout.placements[index];
    if (!pl) continue;
    for (const line of pl.lines) for (let i = 0; i + 1 < line.length; i++)
      strokeSegment(line[i], line[i + 1], 3, "#2f6fdb");
  }
  if (trainTrace?.revision === S.revision) {
    const step = trainTrace.steps[trainStep];
    const terminal = trainStep === trainTrace.steps.length ? trainTrace.terminal : null;
    const pl = S.layout.placements[terminal ? terminal.placement : step ? step[0] : trainTrace.start[0]];
    if (pl) for (const line of pl.lines) for (let i = 0; i + 1 < line.length; i++)
      strokeSegment(line[i], line[i + 1], 5, "#9a3c9c");
  }
}
function focusPieces(indices) {
  closeOverlapPicker(); clearHover();
  highlightedPieces = indices.filter(i => Number.isInteger(i) && S.layout.placements[i]);
  if (highlightedPieces.length) { fitView(highlightedPieces.map(i => S.layout.placements[i])); fitted = true; }
  draw();
}
function showOverlapPicker(hits, remove = false) {
  closeOverlapPicker(); clearHover();
  if (!S || !hits.length) return;
  const box = el("overlap-picker"), revision = S.revision;
  const choices = new Set(hits.map(h => h.placement).filter(i => Number.isInteger(i) && S.layout.placements[i]));
  if (!choices.size) return;
  const dialog = {revision, choices, target: [...choices][0]}; activeOverlap = dialog;
  box.replaceChildren(); box.hidden = false;
  const title = document.createElement("strong");
  title.textContent = remove ? "Choose the piece to remove" : "Overlapping pieces";
  const select = document.createElement("select"); select.setAttribute("aria-label", "Overlapping piece");
  hits.filter(h => choices.has(h.placement)).forEach(hit => {
    const option = document.createElement("option"); option.value = hit.placement;
    option.textContent = `#${hit.placement + 1} ${S.layout.placements[hit.placement].name} · ${hit.z.toFixed(1)} mm`;
    select.append(option);
  });
  selectedPiece = dialog.target;
  select.addEventListener("change", () => {
    const target = Number(select.value);
    if (activeOverlap !== dialog || S?.revision !== revision || !choices.has(target)) return;
    dialog.target = target; selectedPiece = target; draw();
  });
  const confirm = document.createElement("button"); confirm.textContent = remove ? "Remove highlighted piece" : "Select highlighted piece";
  confirm.addEventListener("click", async () => {
    const target = dialog.target;
    if (activeOverlap !== dialog || S?.revision !== revision || apiBusy ||
        !choices.has(target) || !S.layout.placements[target] || Number(select.value) !== target) return;
    selectedPiece = target;
    if (remove) {
      try { S = await api("/api/remove", {placement: target, revision}); redraw(); }
      catch (error) { status(error.message, "err"); return; }
    }
    if (activeOverlap === dialog) closeOverlapPicker();
    draw();
  });
  const cancel = document.createElement("button"); cancel.textContent = "Cancel";
  cancel.addEventListener("click", () => {
    if (activeOverlap !== dialog) return;
    closeOverlapPicker(); selectedPiece = null; draw();
  });
  box.append(title, select, confirm, cancel); select.focus(); draw();
}

async function activateEnd(end) {
  if (!S || apiBusy || solving) return;
  closeOverlapPicker(); clearHover();
  if (pickMode && pickMode.revision !== S.revision) { pickMode = null; status("Select the endpoints again.", "err"); return; }
  if (!S.open_ends.some(e => e[0] === end[0] && e[1] === end[1])) return;
  if (pickMode?.stage === "grow") {
    selectTool({pick: {stage: "close", grow: end}}); refreshStatus(); draw();
  } else if (pickMode) {
    if (pickMode.grow[0] === end[0] && pickMode.grow[1] === end[1]) {
      status("Choose a different open end to close onto.", "err"); return;
    }
    await startInteractiveSearch(pickMode.grow, end);
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
  renderSwitches();
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

function bindExtraEvents() {
  bindSearchEvents();
  const on = (id, action) => el(id)?.addEventListener("click", action);
  on("redo", async () => { try { S = await api("/api/redo", {}); redraw(); } catch (error) { status(error.message, "err"); } });
  on("cancel-search", () => { if (jobLoop) requestJobPause(); });
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
  on("save-project", () => {
    try { const data = projectSnapshot(); downloadJSON(data, "project.json"); markProjectSaved(data); }
    catch (e) { status(e.message, "err"); }
  });
  on("open-project", () => el("projectfile").click());
  el("projectfile")?.addEventListener("change", readProjectFile);
  on("save-local", saveLocalProject);
  on("load-local", async () => {
    const revision = S && S.revision;
    try {
      const key = el("project-slots").value, raw = localStorage.getItem(key);
      const data = readLocalProject(key, raw);
      await openProject(data, revision);
      projectBaselineSlot = key; closeProjectManagement();
    } catch (e) { status(e.message, "err"); }
  });
  on("refresh-projects", renderProjects);
  on("rename-local", () => manageLocalProject("rename"));
  on("delete-local", () => manageLocalProject("delete"));
  el("project-slots")?.addEventListener("change", closeProjectManagement);
  for (const id of ["project-name", "max-pieces", "slop", "reversing"])
    el(id)?.addEventListener("input", updateProjectStatus);
  on("test-train", testTrain); on("train-step", () => { closeOverlapPicker(); stopTrain(); advanceTrain(); });
  on("train-play", () => {
    closeOverlapPicker(); stopTrain();
    if (trainTrace?.revision !== S?.revision || !traceLength()) return;
    if (trainTrace.cycle_start === null && trainStep + 1 >= traceLength()) trainStep = -1;
    advanceTrain();
    if (trainTrace.cycle_start !== null || trainStep + 1 < traceLength()) trainTimer = setInterval(advanceTrain, 500);
  });
  on("train-pause", stopTrain);
  el("train-start")?.addEventListener("change", () => { invalidateTrain(); draw(); });
  for (const id of ["train-unvisited", "train-cycle"]) el(id)?.addEventListener("change", draw);
  canvas.addEventListener("pointerleave", () => { clearHover(); draw(); });
  canvas.addEventListener("keydown", e => {
    if (e.key === "Enter") { e.preventDefault(); el("use-end").click(); }
  });
}
