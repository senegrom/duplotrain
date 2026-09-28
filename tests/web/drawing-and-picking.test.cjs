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
