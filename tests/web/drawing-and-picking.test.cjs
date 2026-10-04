"use strict";
// Drawing and picking: elevation-ordered segments, reused world-space rails,
// coalesced hover hit-tests, and which piece a click or right click picks.
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");
const json = v => JSON.parse(JSON.stringify(v));
const tracks = () => [track([[-100, 0, 100], [100, 0, 100]], "Top"),
  track([[0, -100, 0], [0, 100, 0]], "Bottom"), track([[1000, 0, 0], [1100, 0, 0]], "Distant")];

test("elevated visible track is picked first regardless of placement order", () => {
  const raised = track([[-100, 0, 120], [100, 0, 120]]);
  const ground = track([[0, -100, 0], [0, 100, 0]]);
  for (const placements of [[raised, ground], [ground, raised]]) {
    const h = harness({state: scene(placements), overrides: {worldToScreen: (x, y) => [x, y]}});
    assert.equal(h.context.placementAt(0, 0), placements.indexOf(raised));
    const segments = h.context.drawingSegments(placements);
    assert.equal(segments.at(-1).placement, placements.indexOf(raised));
  }
});

test("ramps are ordered by local segments, not whole-piece average elevation", () => {
  const ramp = track([[-100, 0, 0], [100, 0, 200]]);
  const level = track([[-150, 0, 100], [150, 0, 100]]);
  const h = harness({state: scene([ramp, level]), overrides: {worldToScreen: (x, y) => [x, y]}});
  assert.equal(h.context.placementAt(-75, 0), 1);
  assert.equal(h.context.placementAt(75, 0), 0);
});

test("same-height ties agree with painter order and segment picking works between samples", () => {
  const h = harness({state: scene([track([[-200, 0, 0], [200, 0, 0]]),
    track([[-200, 0, 0], [200, 0, 0]])]), overrides: {worldToScreen: (x, y) => [x, y]}});
  assert.equal(h.context.placementAt(0, 0), 1);
  assert.equal(h.context.placementsAt(0, 0).length, 2);
  assert.equal(h.context.placementAt(0, 100), null);
});

test("a click near a joint picks the piece painted there, without a chooser", async () => {
  // Pieces are painted with flat ends: the neighbour's hit padding past its own
  // end neither wins the tie nor makes the click ambiguous.
  const pieces = [track([[0, 0, 0], [128, 0, 0]], "A"), track([[128, 0, 0], [256, 0, 0]], "B")];
  for (const piece of pieces) piece.width = 64;
  for (const scale of [0.9, 4]) {
    const h = harness({state: scene(pieces, 5), events: true});
    h.run(`view = {x: 128, y: 0, scale: ${scale}}; canvas.clientWidth = 1000; canvas.clientHeight = 500`);
    const [jx, jy] = h.run("worldToScreen(128, 0)");
    for (const mm of [3, 8, 30]) {
      assert.equal(h.run(`placementAt(${jx - mm * scale}, ${jy})`), 0, `${mm} mm inside A at ${scale}`);
      assert.equal(h.run(`placementAt(${jx + mm * scale}, ${jy})`), 1, `${mm} mm inside B at ${scale}`);
    }
    h.run("selectTool({remove: true})");
    await h.run(`removeAt(${jx - 8 * scale}, ${jy})`);
    assert.equal(h.el("overlap-picker").hidden, true);
    assert.deepEqual(json(h.calls.at(-1)), {path: "/api/remove", body: {placement: 0}});
  }
});

test("pieces painted over one another under the pointer still offer the chooser", () => {
  const h = harness({state: scene(tracks(), 5), events: true});
  h.run("view = {x: 0, y: 0, scale: 1}; canvas.clientWidth = 1000; canvas.clientHeight = 500");
  const [x, y] = h.run("worldToScreen(0, 0)");
  assert.deepEqual(json(h.run(`placementsAt(${x}, ${y}).map(hit => hit.placement)`)), [0, 1]);
});

test("right-click removes the piece under the pointer; a touch long-press does not", async () => {
  const h = harness({state: scene([track([[-100, 0, 0], [100, 0, 0]])]), events: true, overrides: {redraw() {}}});
  let prevented = 0;
  const menu = pointerType => h.el("canvas").fire("contextmenu",
    {pointerType, clientX: 250, clientY: 250, preventDefault() { prevented++; }});
  await menu("touch");
  assert.equal(h.calls.length, 0);
  await menu("mouse");
  assert.deepEqual(JSON.parse(JSON.stringify(h.calls)), [{path: "/api/remove", body: {placement: 0}}]);
  assert.equal(prevented, 2);  // the browser's own menu never opens over the track
});

test("a click anywhere on an open end's arrow takes that end, the nearest arrow first", async () => {
  // Two straights face each other across a 75 mm gap, and a third, off to the west, ends
  // facing north. Zoomed in, each red arrow reaches 48 px from its connector's dot: its
  // head is as much the end's target as the dot. Zoomed out, the arrows shrink to 16 px,
  // and their targets with them.
  const right = track([[75, 0, 0], [203, 0, 0]], "Right");
  right.ports = [{port: 0, open: true, sealed: false, x: 75, y: 0, deg: 180, name: "a"},
    {port: 1, open: false, sealed: false, x: 203, y: 0, deg: 0, name: "b"}];
  const left = track([[-128, 0, 0], [0, 0, 0]], "Left");
  left.ports = [{port: 0, open: false, sealed: false, x: -128, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: false, x: 0, y: 0, deg: 0, name: "b"}];
  const north = track([[-250, -128, 0], [-250, 0, 0]], "North");
  north.ports = [{port: 0, open: false, sealed: false, x: -250, y: -128, deg: 270, name: "a"},
    {port: 1, open: true, sealed: false, x: -250, y: 0, deg: 90, name: "b"}];
  const state = scene([right, left, north], 5);
  state.open_ends = [[0, 0], [1, 1], [2, 1]];
  const h = harness({state, events: true, overrides: {redraw() {}}});
  h.run("view = {x: 0, y: 0, scale: 1.6}; canvas.clientWidth = 1000; canvas.clientHeight = 500");
  h.run('selectTool({piece: {piece: "straight", pieceName: "Straight rail", entry: 0, exit: 1, label: "ahead"}})');
  // The left straight's dot; the right one's is 120 px on, its arrow pointing back.
  const [x, y] = h.run("worldToScreen(0, 0)");
  // On the left arrow's head, 44 px out; between the two heads, nearer each in turn;
  // and 25 px beside the left arrow's head, out of reach of both.
  for (const [dx, dy] of [[44, 0], [55, 0], [66, 0], [44, 25]]) await h.run(`activateAt(${x + dx}, ${y + dy})`);
  // North is up the screen, though screen y counts downward: on that arrow's head.
  const [nx, ny] = h.run("worldToScreen(-250, 0)");
  await h.run(`activateAt(${nx}, ${ny - 44})`);
  // Zoomed out: on its head, 14 px up; and 40 px up, 24 px beyond the head.
  h.run("view.scale = 0.4");
  const [zx, zy] = h.run("worldToScreen(-250, 0)");
  for (const up of [14, 40]) await h.run(`activateAt(${zx}, ${zy - up})`);
  assert.deepEqual(json(h.calls), [
    {path: "/api/attach", body: {piece: "straight", entry: 0, at: [1, 1]}},
    {path: "/api/attach", body: {piece: "straight", entry: 0, at: [1, 1]}},
    {path: "/api/attach", body: {piece: "straight", entry: 0, at: [0, 0]}},
    {path: "/api/attach", body: {piece: "straight", entry: 0, at: [2, 1]}},
    {path: "/api/attach", body: {piece: "straight", entry: 0, at: [2, 1]}}]);
});

// Two straights face each other across a gap of `gap` mm, as where a loop has nearly come
// round: the left one ends at the origin pointing east, the right one starts beyond the gap
// pointing west. With no gap, the two ends meet at one point.
function facingEnds(gap, overrides = {}) {
  const left = track([[-128, 0, 0], [0, 0, 0]], "Left");
  left.ports = [{port: 0, open: false, sealed: false, x: -128, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: false, x: 0, y: 0, deg: 0, name: "b"}];
  const right = track([[gap, 0, 0], [gap + 128, 0, 0]], "Right");
  right.ports = [{port: 0, open: true, sealed: false, x: gap, y: 0, deg: 180, name: "a"},
    {port: 1, open: false, sealed: false, x: gap + 128, y: 0, deg: 0, name: "b"}];
  const state = scene([left, right], 5);
  state.open_ends = [[0, 1], [1, 0]];
  if (!gap) state.matable = [[[0, 1], [1, 0]]];
  const h = harness({state, events: true, overrides: {redraw() {}, ...overrides}});
  h.run("canvas.clientWidth = 1000; canvas.clientHeight = 500");
  return h;
}

// Zoomed to `scale`, the ends of facingEnds(20), each with where to click it: on its dot,
// and 6 px behind it, just off the dot over its own piece (west of the left end's dot,
// east of the right end's).
function facingClicks(h, scale) {
  h.run(`view = {x: 0, y: 0, scale: ${scale}}`);
  const [lx, ly] = h.run("worldToScreen(0, 0)"), [rx, ry] = h.run("worldToScreen(20, 0)");
  return [[[0, 1], lx, ly], [[0, 1], lx - 6, ly], [[1, 0], rx, ry], [[1, 0], rx + 6, ry]];
}

test("a click on an open end's dot, or just behind it, takes that end though a facing arrow runs over it", async () => {
  // 20 mm apart, the ends are closer than an arrow is long: zoomed in, 32 px apart with
  // 48 px arrows; zoomed out, 8 px apart with 16 px arrows. Each arrow runs over the other
  // end's dot, yet the dot clicked names its own end, and the armed piece attaches there.
  const h = facingEnds(20);
  h.run('selectTool({piece: {piece: "straight", pieceName: "Straight rail", entry: 0, exit: 1, label: "ahead"}})');
  const ends = [];
  for (const scale of [1.6, 0.4]) {
    const clicks = facingClicks(h, scale), [left, right] = h.run("openEndScreenPos()");
    assert.ok(left.tipX > right.x && right.tipX < left.x);  // each arrow runs over the other dot
    for (const [end, x, y] of clicks) {
      await h.run(`activateAt(${x}, ${y})`);
      ends.push(end);
    }
  }
  assert.deepEqual(json(h.calls), ends.map(at => ({path: "/api/attach", body: {piece: "straight", entry: 0, at}})));
});

test("a dot names its end within 22 px; past every dot's reach, the nearest arrow takes the click", async () => {
  // 21 px behind its dot, a click is the end's own, though the facing arrow lies nearer.
  // 23 px behind, out of both dots' reach, the nearest arrow decides: the facing one, its
  // head 7 px off zoomed in and 15 px zoomed out.
  const h = facingEnds(20);
  h.run('selectTool({piece: {piece: "straight", pieceName: "Straight rail", entry: 0, exit: 1, label: "ahead"}})');
  const ends = [];
  for (const scale of [1.6, 0.4]) {
    const [[left, lx, ly], , [right, rx, ry]] = facingClicks(h, scale);
    for (const [end, x, y] of [[left, lx - 21, ly], [right, rx + 21, ry],
      [right, lx - 23, ly], [left, rx + 23, ry]]) {
      await h.run(`activateAt(${x}, ${y})`);
      ends.push(end);
    }
  }
  // The nearest arrow, not the nearest dot. Zoomed in, a straight takes the right one's
  // place: its end stands 60 px on from the left end and 30 px up, its arrow slanting back
  // across the left arrow. A click 44 px out on the left arrow takes the left end, though
  // the slanting arrow passes 10 px off and its dot, 34 px off, is nearer than the left's.
  const slant = track([[37.5, 18.75, 0], [128, 109.25, 0]], "Slant");
  slant.ports = [{port: 0, open: true, sealed: false, x: 37.5, y: 18.75, deg: 225, name: "a"},
    {port: 1, open: false, sealed: false, x: 128, y: 109.25, deg: 45, name: "b"}];
  h.context.S.layout.placements[1] = slant;
  h.run("view = {x: 0, y: 0, scale: 1.6}");
  const [x, y] = h.run("worldToScreen(0, 0)");
  await h.run(`activateAt(${x + 44}, ${y})`);
  ends.push([0, 1]);
  assert.deepEqual(json(h.calls), ends.map(at => ({path: "/api/attach", body: {piece: "straight", entry: 0, at}})));
});

test("Close the loop picks the end whose dot is clicked, and at a dot two ends share, the arrow's", async () => {
  // Grown from on its dot or just behind it, each facing end is the one meant, and a close
  // pick there on the other end closes onto it, never onto the end grown from.
  const searches = [];
  const h = facingEnds(20, {startInteractiveSearch: async (grow, close) => { searches.push(json([grow, close])); }});
  const grown = [], pairs = [];
  for (const scale of [1.6, 0.4]) {
    const [left, leftBehind, right, rightBehind] = facingClicks(h, scale);
    for (const [[grow, gx, gy], [close, cx, cy]] of
      [[left, right], [leftBehind, rightBehind], [right, left], [rightBehind, leftBehind]]) {
      h.run('selectTool({pick: {stage: "grow", grow: null}})');
      await h.run(`activateAt(${gx}, ${gy})`);
      grown.push(json(h.run("pickMode.grow")));
      await h.run(`activateAt(${cx}, ${cy})`);
      pairs.push([grow, close]);
    }
  }
  assert.deepEqual(grown, pairs.map(([grow]) => grow));
  assert.deepEqual(searches, pairs);
  // Two ends that meet share one dot: 10 px out along either arrow, as near the dot for
  // both, the arrow clicked names the end to grow from.
  const met = facingEnds(0), byArrow = [];
  for (const scale of [1.6, 0.4]) {
    met.run(`view = {x: 0, y: 0, scale: ${scale}}`);
    const [x, y] = met.run("worldToScreen(0, 0)");
    for (const dx of [10, -10]) {
      met.run('selectTool({pick: {stage: "grow", grow: null}})');
      await met.run(`activateAt(${x + dx}, ${y})`);
      byArrow.push(json(met.run("pickMode.grow")));
    }
  }
  assert.deepEqual(byArrow, [[0, 1], [1, 0], [0, 1], [1, 0]]);
});

test("an end that meets its mate joins it on a click, though a piece is armed", async () => {
  // Two straights meet end to end unjoined, as a loop's last piece lands on its first:
  // a piece attached there would overlap the mate. The far end, meeting nothing, still
  // takes the armed piece.
  const first = track([[0, 0, 0], [128, 0, 0]], "First");
  first.ports = [{port: 0, open: false, sealed: false, x: 0, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: false, x: 128, y: 0, deg: 0, name: "b"}];
  const last = track([[128, 0, 0], [256, 0, 0]], "Last");
  last.ports = [{port: 0, open: true, sealed: false, x: 128, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: false, x: 256, y: 0, deg: 0, name: "b"}];
  const state = scene([first, last], 5);
  state.open_ends = [[0, 1], [1, 0], [1, 1]];
  state.matable = [[[0, 1], [1, 0]]];
  const h = harness({state, overrides: {worldToScreen: (x, y) => [x, y], redraw() {}}});
  h.run('selectTool({piece: {piece: "straight", pieceName: "Straight rail", entry: 0, exit: 1, label: "ahead"}})');
  await h.run("activateAt(128, 0)");
  await h.run("activateAt(256, 0)");
  assert.deepEqual(json(h.calls), [{path: "/api/join", body: {a: [0, 1], b: [1, 0]}},
    {path: "/api/attach", body: {piece: "straight", entry: 0, at: [1, 1]}}]);
});

test("cached world-space rails survive view changes, redraws coalesce into one frame", () => {
  let paints = 0;
  const h = harness({state: scene([track([[0, 0, 0], [100, 0, 0]])]), schedule: true,
    overrides: {paint: () => { paints++; }}});
  const first = h.context.drawingSegments(h.context.S.layout.placements);
  h.context.view = {x: 10, y: 10, scale: 2};
  assert.equal(h.context.drawingSegments(h.context.S.layout.placements), first);
  h.run("draw(); draw(); draw()"); assert.equal(h.frames.length, 1); assert.equal(paints, 0);
  h.frames.shift()(); assert.equal(paints, 1);
  h.run("draw()"); assert.equal(h.frames.length, 1);
});

test("100 hover events cause one hit-test at the final position per frame", () => {
  const calls=[];let paints=0;
  const h=harness({events:true,schedule:true,overrides:{paint:()=>paints++,placementAt:(x,y)=>{calls.push([x,y]);return 0;}}});
  for(let i=0;i<100;i++)h.el("canvas").listeners.pointermove({pointerId:1,pointerType:"mouse",clientX:i,clientY:2});
  assert.equal(calls.length,0);assert.equal(h.frames.length,1);h.frames.shift()();
  assert.deepEqual(calls,[[99,2]]);assert.equal(paints,1);
});

for(const action of ["leave","revision","replace","drag"]) test(`queued hover is dropped on ${action}`,()=>{
  let calls=0;
  const h=harness({events:true,schedule:true,overrides:{paint(){},placementAt:()=>{calls++;return 0;}}});
  h.el("canvas").listeners.pointermove({pointerId:1,pointerType:"pen",clientX:10,clientY:2});
  if(action === "leave")h.el("canvas").listeners.pointerleave();
  if(action === "revision")h.run("S.revision++");
  if(action === "replace")h.context.S={...h.context.S,layout:{...h.context.S.layout,placements:[]}};
  if(action === "drag")h.run("pointers.set(1,{x:10,y:2})");
  h.frames.shift()();assert.equal(calls,0);
});

test("hovering within the same piece does not repaint after coalesced picking", () => {
  let paints = 0;
  const h = harness({state: scene([track([[0, 0, 0], [200, 0, 0]])]), events: true,
    schedule: true, overrides: {paint: () => { paints++; }}});
  const move = (x, y) => h.el("canvas").listeners.pointermove(
    {pointerId: 7, pointerType: "mouse", clientX: x, clientY: y});
  const flush = () => { while (h.frames.length) h.frames.shift()(); };
  move(260, 250); flush();
  assert.equal(h.run("hoveredPiece"), 0); assert.equal(paints, 1);
  move(300, 252); flush();
  assert.equal(paints, 1);
  move(250, 480); flush();
  assert.equal(h.run("hoveredPiece"), null); assert.equal(paints, 2);
  move(260, 480); flush();
  assert.equal(paints, 2);
  h.run("draw()"); flush();
  assert.equal(paints, 3); // Non-hover redraws are never suppressed.
});

test("viewport culling submits only visible track and includes edge padding", () => {
  let fills=0,strokes=0;
  const h=harness({events:true,overrides:{worldToScreen:(x,y)=>[x,y]}});
  const placements=Array.from({length:1000},(_,i)=>track([[100+i*1000,100,0],[200+i*1000,100,0]]));
  h.context.painted=placements;
  h.context.record={beginPath(){},moveTo(){},lineTo(){},closePath(){},fill(){fills++;},stroke(){strokes++;}};
  h.run("ctx=record; drawLayout({placements:painted},false)");
  assert.equal(fills,1); assert.equal(strokes,1);
  assert.equal(h.context.screenBoundsVisible(-100,-100,-1,-1,3),true);
  assert.equal(h.context.screenBoundsVisible(-100,-100,-10,-10,3),false);
  assert.equal(h.context.screenBoundsVisible(NaN,0,1,1),true);
});

test("base raster builds once a frame repeats, on one reused surface, within its pixel cap", () => {
  const h=harness({events:true}); let direct=0,offscreen=0,blits=0,created=0;
  const originalCreate=h.context.document.createElement;
  h.context.document.createElement=tag=>tag==="canvas" ? (created++,{width:0,height:0,
    getContext:()=>({setTransform(){},clearRect(){},beginPath(){},moveTo(){},lineTo(){},closePath(){},
      fill(){offscreen++;},stroke(){}})}) : originalCreate(tag);
  const target={drawImage(){blits++;},beginPath(){},moveTo(){},lineTo(){},closePath(){},fill(){direct++;},stroke(){}};
  h.context.target=target; h.context.layout={placements:[track([[0,0,0],[100,0,0]])]};
  // A new view paints directly; its repeat builds the raster; later repeats only blit.
  h.run("ctx=target; canvas.width=500; canvas.height=500; drawBaseTrack(layout); drawBaseTrack(layout); drawBaseTrack(layout)");
  assert.deepEqual([direct,offscreen,blits,created],[1,1,2,1]);
  // Pan and zoom frames and new geometry paint directly and allocate nothing.
  h.run("for (let i=0;i<5;i++) { view.x++; drawBaseTrack(layout); }");
  h.run("layout={placements:[...layout.placements]}; drawBaseTrack(layout)");
  assert.deepEqual([direct,offscreen,blits,created],[7,1,2,1]);
  assert.equal(h.run("baseRaster"),null);
  // Once the view rests again, the same surface is re-rendered.
  h.context.devicePixelRatio=2; h.run("drawBaseTrack(layout); drawBaseTrack(layout)");
  assert.deepEqual([direct,offscreen,blits,created],[8,2,3,1]);
  h.run("canvas.width=4000;canvas.height=3000;drawBaseTrack(layout);drawBaseTrack(layout)");
  assert.equal(h.run("baseRaster"),null); assert.equal(h.run("rasterSurface"),null);
  assert.deepEqual([direct,created],[10,1]);
  assert.equal(h.run("ctx"),target);
});

test("base raster always restores the real canvas context if drawing throws", () => {
  const h=harness({events:true});
  const target={drawImage(){},beginPath(){},moveTo(){},lineTo(){},closePath(){},fill(){},stroke(){}};
  h.context.target=target;
  h.context.document.createElement=()=>({getContext:()=>({setTransform(){},beginPath(){throw new Error("paint error");}})});
  h.context.layout={placements:[track([[0,0,0],[100,0,0]])]};
  h.run("ctx=target;canvas.width=500;canvas.height=500;drawBaseTrack(layout)");
  assert.throws(()=>h.run("drawBaseTrack(layout)"),/paint error/);
  assert.equal(h.run("ctx"),target); assert.equal(h.run("baseRaster"),null);
});

test("the cached raster is blitted 1:1 in device pixels at a fractional ratio", () => {
  const h = harness({events: true}); const blits = [];
  h.context.document.createElement = () => ({width: 0, height: 0, getContext: () => ({
    setTransform() {}, clearRect() {}, beginPath() {}, moveTo() {}, lineTo() {}, closePath() {},
    fill() {}, stroke() {}})});
  h.context.target = {drawImage: (_surface, ...box) => blits.push(box), beginPath() {},
    moveTo() {}, lineTo() {}, closePath() {}, fill() {}, stroke() {}};
  h.context.layout = {placements: [track([[0, 0, 0], [100, 0, 0]])]};
  h.context.devicePixelRatio = 1.5;  // 333 CSS px: a 499-pixel store, 332.67 CSS px of it
  h.run("ctx = target; canvas.clientWidth = canvas.clientHeight = 333;" +
        "canvas.width = canvas.height = 499; drawBaseTrack(layout); drawBaseTrack(layout)");
  assert.deepEqual(blits, [[0, 0, 499 / 1.5, 499 / 1.5]]);
});
