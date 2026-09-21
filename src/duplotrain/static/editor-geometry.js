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

function strokeSegment(a, b, width, color, cap = "round") {
  const [ax, ay] = worldToScreen(a[0], a[1]), [bx, by] = worldToScreen(b[0], b[1]);
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
