"use strict";
// Derived geometry for the editor's immutable drawing snapshots. These helpers
// consume the single S/view/canvas/ctx owner in editor.js; they never mutate an
// exact layout, API revision or project state. One WeakMap owns each collection's
// lazily constructed segments, piece groups, batches and conservative hit bounds.
const geometryCache = new WeakMap(), previewCache = new WeakMap();
function drawingGeometry(placements) {
  let geometry = geometryCache.get(placements);
  if (!geometry) { geometry = {}; geometryCache.set(placements, geometry); }
  return geometry;
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
    if (!batchVisible(batch)) continue;
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

// Bounds cover painted edge/rail vertices. This is presentation only, never a
// collision or picking decision. Non-finite bounds conservatively remain visible.
const batchBounds = new WeakMap();
let baseRaster = null;
function screenBoundsVisible(x0, y0, x1, y1, pad = 3) {
  if (![x0, y0, x1, y1, pad, canvas.clientWidth, canvas.clientHeight].every(Number.isFinite)) return true;
  const guard = 1e-7 + 1e-9 * Math.max(1, Math.abs(x0), Math.abs(x1), Math.abs(y0), Math.abs(y1));
  return Math.max(x0, x1) + pad + guard >= 0 && Math.min(x0, x1) - pad - guard <= canvas.clientWidth &&
    Math.max(y0, y1) + pad + guard >= 0 && Math.min(y0, y1) - pad - guard <= canvas.clientHeight;
}
function batchVisible(batch) {
  let bounds = batchBounds.get(batch);
  if (!bounds) {
    bounds = [Infinity, Infinity, -Infinity, -Infinity];
    for (const segment of batch) for (const [x, y] of [...segment.edge, ...segment.rails.flat()]) {
      bounds[0] = Math.min(bounds[0], x); bounds[1] = Math.min(bounds[1], y);
      bounds[2] = Math.max(bounds[2], x); bounds[3] = Math.max(bounds[3], y);
    }
    batchBounds.set(batch, bounds);
  }
  const [x0, y0] = worldToScreen(bounds[0], bounds[1]), [x1, y1] = worldToScreen(bounds[2], bounds[3]);
  return screenBoundsVisible(x0, y0, x1, y1, Math.max(3, view.scale));
}
function drawBaseTrack(layout) {
  const ratio = globalThis.devicePixelRatio || 1;
  const key = [view.x, view.y, view.scale, canvas.width, canvas.height,
    canvas.clientWidth, canvas.clientHeight, ratio].join(":");
  const canCache = typeof ctx.drawImage === "function" && canvas.width > 0 && canvas.height > 0 &&
    canvas.width * canvas.height <= 8_000_000;
  if (!canCache) { baseRaster = null; drawLayout(layout, false); return; }
  if (!baseRaster || baseRaster.placements !== layout.placements || baseRaster.key !== key) {
    const surface = document.createElement("canvas");
    surface.width = canvas.width; surface.height = canvas.height;
    const target = surface.getContext?.("2d");
    if (!target) { baseRaster = null; drawLayout(layout, false); return; }
    const original = ctx;
    try {
      ctx = target; ctx.setTransform(ratio, 0, 0, ratio, 0, 0);
      drawLayout(layout, false);
    } finally { ctx = original; }
    baseRaster = {surface, key, placements: layout.placements};
  }
  ctx.drawImage(baseRaster.surface, 0, 0, canvas.clientWidth, canvas.clientHeight);
}
function drawFloorConstraints() {
  let options;
  try { options = interactiveJob?.revision === S?.revision && interactiveJob.options ?
    interactiveJob.options : readSearchOptions(); } catch (_) { return; }
  const boxes = [...(options.room ? [[options.room, false]] : []), ...options.keep_out.map(r => [r, true])];
  if (!boxes.length || !ctx.strokeRect) return;
  ctx.save();
  for (const [r, blocked] of boxes) {
    const [x, y] = worldToScreen(r[0], r[3]);
    const width = (r[2] - r[0]) * view.scale, height = (r[3] - r[1]) * view.scale;
    if (!screenBoundsVisible(x, y, x + width, y + height)) continue;
    ctx.strokeStyle = blocked ? "#ab4c3b" : "#4b7380"; ctx.lineWidth = 2;
    ctx.setLineDash([5, 5]); ctx.strokeRect(x, y, width, height);
    if (blocked) { ctx.fillStyle = "rgba(171,76,59,.10)"; ctx.fillRect(x, y, width, height); }
  }
  ctx.restore();
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

function strokeSegment(a, b, width, color, cap = "round") {
  const [ax, ay] = worldToScreen(a[0], a[1]), [bx, by] = worldToScreen(b[0], b[1]);
  if (!screenBoundsVisible(ax, ay, bx, by, width / 2 + 2)) return;
  ctx.beginPath(); ctx.moveTo(ax, ay); ctx.lineTo(bx, by);
  ctx.lineWidth = width; ctx.lineCap = cap; ctx.lineJoin = "round";
  ctx.strokeStyle = color; ctx.stroke();
}
const interpolate = (a, b, t) => [0, 1, 2].map(i => (a[i] || 0) + ((b[i] || 0) - (a[i] || 0)) * t);
function drawingSegments(placements) {
  const geometry = drawingGeometry(placements);
  if (geometry.segments) return geometry.segments;
  const segments = [];
  placements.forEach((pl, placement) => {
    for (const line of pl.lines) {
      const rails = [offsetLine(line, 24), offsetLine(line, -24)];
      const edges = [offsetLine(line, pl.width / 2), offsetLine(line, -pl.width / 2)];
      for (let i = 0; i + 1 < line.length; i++) {
        const a = line[i], b = line[i + 1];
        // Flat sampled chords have no height-order ambiguity; only climbing
        // edges need subdivisions for ramp-local paint and selection order.
        const divisions = (a[2] || 0) === (b[2] || 0) ? 1 :
          Math.min(256, Math.max(1, Math.ceil(Math.hypot(b[0] - a[0], b[1] - a[1]) / 8)));
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
  geometry.segments = segments;
  geometry.byPlacement = placements.map(() => []);
  for (const segment of segments) geometry.byPlacement[segment.placement].push(segment);
  return segments;
}
function drawingBatches(placements) {
  const geometry = drawingGeometry(placements);
  if (geometry.batches) return geometry.batches;
  const batches = [];
  for (const segment of drawingSegments(placements)) {
    const batch = batches[batches.length - 1], previous = batch?.[0];
    if (previous && previous.z === segment.z && previous.placement === segment.placement) batch.push(segment);
    else batches.push([segment]);
  }
  geometry.batches = batches;
  return batches;
}

function hitCandidates(sx, sy, placements) {
  const geometry = drawingGeometry(placements);
  let bounds = geometry.bounds;
  if (!bounds) {
    bounds = placements.map(pl => {
      let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
      for (const line of pl.lines) for (const [x, y] of line) {
        x0 = Math.min(x0, x); x1 = Math.max(x1, x);
        y0 = Math.min(y0, y); y1 = Math.max(y1, y);
      }
      return {x0, x1, y0, y1, width: pl.width};
    });
    geometry.bounds = bounds;
  }
  const candidates = new Set();
  bounds.forEach((b, i) => {
    const a = worldToScreen(b.x0, b.y0), c = worldToScreen(b.x1, b.y1);
    // Outward guard is deliberately permissive at translated/zoomed boundaries.
    const pad = Math.max(14, b.width * view.scale / 2) +
      1e-7 + 1e-9 * Math.max(1, ...a.map(Math.abs), ...c.map(Math.abs));
    if (![...a, ...c, pad].every(Number.isFinite) ||
        (sx >= Math.min(a[0], c[0]) - pad && sx <= Math.max(a[0], c[0]) + pad &&
         sy >= Math.min(a[1], c[1]) - pad && sy <= Math.max(a[1], c[1]) + pad)) candidates.add(i);
  });
  return candidates;
}
function placementsAt(sx, sy) {
  if (!S) return [];
  const hits = new Map(), candidates = hitCandidates(sx, sy, S.layout.placements);
  if (!candidates.size) return [];
  drawingSegments(S.layout.placements);
  const grouped = drawingGeometry(S.layout.placements).byPlacement;
  // Preserve each piece's elevation-ordered segments, but visit only pieces in
  // the conservative shortlist rather than testing every segment's membership.
  for (const placement of candidates) for (const seg of grouped[placement]) {
    const [ax, ay] = worldToScreen(seg.a[0], seg.a[1]), [bx, by] = worldToScreen(seg.b[0], seg.b[1]);
    const dx = bx - ax, dy = by - ay;
    const t = Math.max(0, Math.min(1, ((sx - ax) * dx + (sy - ay) * dy) / (dx * dx + dy * dy || 1)));
    const d = Math.hypot(sx - ax - t * dx, sy - ay - t * dy);
    const half = seg.width * view.scale / 2;
    if (d >= Math.max(14, half)) continue;
    const hit = {placement: seg.placement, d, z: seg.z, painted: d < half};
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
