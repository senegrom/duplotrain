"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");

function editor(marks, {events = false} = {}) {
  const state = {layout: {placements: [{
    mid: [64, 0], ports: [{x: 0, y: 0}, {x: 128, y: 0}], stone_marks: marks,
  }]}};
  return harness({state, events, overrides: {
    worldToScreen: (x, y) => [x, y], placementAt: () => 0,
    placementsAt: () => [{placement: 0, d: 0, z: 0}], redraw() {},
  }});
}

for (const at of [null, 0, 1]) {
  test(`Remove sends the selected ${at === null ? "midpoint" : "face " + at} marker and removal intent`, async () => {
    const e = editor([null, 0, 1].map(position => ({id: "stone_lights", at: position})));
    await e.run(`const marker = stoneMarkPositions().find(m => m.at_port === ${at}); removeAt(marker.x, marker.y)`);
    assert.equal(e.calls.length, 1);
    assert.equal(e.calls[0].path, "/api/stone");
    assert.equal(e.calls[0].body.placement, 0);
    assert.equal(e.calls[0].body.id, "stone_lights");
    assert.equal(e.calls[0].body.at_port, at);
    assert.equal(e.calls[0].body.remove, true);
    assert.deepEqual(e.notices, []);
  });
}

test("Legacy midpoint markers without at send explicit null", async () => {
  const e = editor([{id: "stone_lights"}]);
  await e.run("const marker = stoneMarkPositions()[0]; removeAt(marker.x, marker.y)");
  assert.equal(e.calls[0].body.at_port, null);
  assert.equal(e.calls[0].body.remove, true);
});

test("Remove and a right click take the stone mark nearest the pointer, not the first in reach", async () => {
  // Zoomed out, the marks of two stones on one piece stand closer together than a
  // mark's reach: the one under the pointer is the stone meant.
  const e = editor([{id: "stone_stop", at: null}, {id: "stone_horn", at: null}], {events: true});
  e.run("view.scale = 0.3");
  const [stop, horn] = e.run("stoneMarkPositions()");
  assert.ok(Math.hypot(stop.x - horn.x, stop.y - horn.y) < Math.max(16, stop.r + 4));
  await e.run(`selectTool({remove: true}); activateAt(${horn.x}, ${horn.y})`);
  const rightClick = mark => e.el("canvas").fire("contextmenu",
    {pointerType: "mouse", clientX: mark.x, clientY: mark.y, preventDefault() {}});
  await rightClick(stop);
  await rightClick(horn);
  assert.deepEqual(e.calls.map(c => [c.path, c.body.id, c.body.remove]), [
    ["/api/stone", "stone_horn", true], ["/api/stone", "stone_stop", true], ["/api/stone", "stone_horn", true]]);
});

for (const flag of ["apiBusy", "jobLoop"]) {
  test(`Remove ignores clicks while ${flag}`, async () => {
    const e = editor([{id: "stone_lights", at: 0}]);
    e.run(`${flag} = true`);
    await e.run("const marker = stoneMarkPositions()[0]; removeAt(marker.x, marker.y)");
    assert.equal(e.calls.length, 0);
  });
}

test("the stone tool clips a stone at the connector face clicked, otherwise mid-piece", async () => {
  const e = editor([]);
  e.run(`Object.assign(S.layout.placements[0], {stone_ok: true, ports: [{port: 0, x: 0, y: 0}, {port: 1, x: 128, y: 0}]});
    armedStone = "stone_stop"`);
  for (const [x, y] of [[3, 2], [125, -4], [64, 10]]) await e.run(`activateAt(${x}, ${y})`);
  assert.deepEqual(e.calls.map(c => [c.path, c.body.placement, c.body.id, c.body.at_port]), [
    ["/api/stone", 0, "stone_stop", 0], ["/api/stone", 0, "stone_stop", 1], ["/api/stone", 0, "stone_stop", null]]);
});

test("Remove away from markers still removes the selected piece", async () => {
  // A stone clipped at the piece's first face sits 52 px from a click mid-piece, beyond
  // a mark's reach: the click means the piece.
  const e = editor([{id: "stone_lights", at: 0}]);
  await e.run("removeAt(64, 0)");
  assert.equal(e.calls[0].path, "/api/remove");
  assert.equal(e.calls[0].body.placement, 0);
});

test("an armed stone or the Remove tool explains itself on a closed layout too", () => {
  const closed = scene([track([[0, 0, 0], [100, 0, 0]])]);
  closed.layout.exactly_closed = true;
  closed.stones.catalog = {stone_direction: {name: "Direction stone"}};
  const h = harness({state: closed});
  h.run('selectTool({stone: "stone_direction"}); refreshStatus()');
  assert.match(h.notices.at(-1).text, /Direction stone armed/);
  h.run("selectTool({remove: true}); refreshStatus()");
  assert.match(h.notices.at(-1).text, /Remove tool/);
  // A closed layout has no end to attach an armed piece to.
  h.run('selectTool({piece: {piece: "straight", pieceName: "Straight", label: "ahead"}}); refreshStatus()');
  assert.match(h.notices.at(-1).text, /Connectors closed/);
});

test("an armed piece says which ends it joins, and a joint warning waits behind the tools", () => {
  const ramp = track([[0, 0, 0], [320, 0, 57.6]], "Bridge ramp");
  ramp.ports = [{port: 0, open: true, sealed: false, x: 0, y: 0, deg: 180, name: "low"},
    {port: 1, open: true, sealed: false, x: 320, y: 0, deg: 0, name: "high", kind: "ramp_top"}];
  const h = harness({state: scene([ramp])});
  h.run('selectTool({piece: {piece: "span", pieceName: "Bridge arch", label: "climb", takes: ["ramp_top"]}})');
  h.run("refreshStatus()");
  assert.match(h.notices.at(-1).text, /Click a red arrow to attach/);
  h.context.S.layout.placements[0].ports[1].open = false;  // the ramp's top is taken
  h.run("refreshStatus()");
  assert.match(h.notices.at(-1).text, /No open end takes it: it joins only a ramp's top\./);
  h.context.S.layout.joint_issues = [{a: [0, 1], b: [1, 0], gap_mm: 0, height_mm: 0,
    heading_error_deg: 0, problems: ["mismatched bridge joint"]}];
  h.run("refreshStatus()");
  assert.match(h.notices.at(-1).text, /Bridge arch — climb armed/);
  h.run("selectTool(); refreshStatus()");
  assert.match(h.notices.at(-1).text, /Joint #1 ↔ #2: mismatched bridge joint\.$/);
});

// A level crossing (#1) with a straight (#2) after it, and the palette offering both.
// The crossing's road plate overhangs its rail ends, so a second crossing cannot sit
// against it; ordinary track can.
function crossingScene() {
  const crossing = track([[0, 0, 0], [128, 0, 0]], "Level crossing plate");
  crossing.plate = true;
  crossing.ports = [{port: 0, open: true, sealed: false, x: 0, y: 0, deg: 180, name: "a"},
    {port: 1, open: false, sealed: false, x: 128, y: 0, deg: 0, name: "b"}];
  const straight = track([[128, 0, 0], [256, 0, 0]], "Straight rail");
  straight.ports = [{port: 0, open: false, sealed: false, x: 128, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: false, x: 256, y: 0, deg: 0, name: "b"}];
  const state = scene([crossing, straight]);
  state.palette = [
    {id: "level_crossing", name: "Level crossing plate", plate: true,
      variants: [{entry: 0, exit: 1, label: "ahead"}]},
    {id: "straight", name: "Straight rail", variants: [{entry: 0, exit: 1, label: "ahead"}]}];
  state.inventory.unlimited = true;
  return state;
}

// Paint on a canvas that notes the colour of each dot drawn, by its place on screen:
// the foot of an open end's arrow, or a joint. With `every`, each place lists the colours
// of all its dots in the order painted, as where two ends meet at one dot.
function dotColours(h, {every = false} = {}) {
  const dots = {}, none = () => {};
  h.context.recorder = {setTransform: none, clearRect: none, beginPath: none, moveTo: none,
    lineTo: none, closePath: none, fill: none, stroke: none, fillText: none,
    arc(x, y) {
      const at = `${x},${y}`;
      dots[at] = every ? [...(dots[at] ?? []), this.fillStyle] : this.fillStyle;
    }};
  h.run("ctx = recorder; paint()");
  return dots;
}

test("a road plate armed from the palette greys another plate's open end, not ordinary track's", () => {
  const h = harness({state: crossingScene(), events: true,
    overrides: {devicePixelRatio: 1, worldToScreen: (x, y) => [x, y]}});
  h.run("renderPalette()");
  const [crossing, straight] = h.run("paletteRows").map(row => row.buttons[0].button);
  crossing.click();
  assert.equal(h.run("armed.plate"), true);
  // Grey at the crossing's end, which a second plate cannot meet; red at the straight's.
  let dots = dotColours(h);
  assert.deepEqual([dots["0,0"], dots["256,0"]], ["#a7adb3", "#d0342c"]);
  // With ordinary track armed instead, both ends are red: track meets a plate.
  straight.click();
  assert.equal(h.run("armed.piece"), "straight");
  dots = dotColours(h);
  assert.deepEqual([dots["0,0"], dots["256,0"]], ["#d0342c", "#d0342c"]);
});

test("an armed road plate says two plates cannot meet when every open end of its kind is a plate's", () => {
  const h = harness({state: crossingScene()});
  const arm = piece => {
    h.run(`selectTool({piece: ${JSON.stringify(piece)}}); refreshStatus()`);
    return h.notices.at(-1).text;
  };
  const crossing = {piece: "level_crossing", pieceName: "Level crossing plate", label: "ahead",
    plate: true};
  const placements = h.context.S.layout.placements;
  assert.match(arm(crossing), /Click a red arrow to attach/);  // at the straight's end
  placements[1].ports[1].open = false;  // the straight's end is taken
  assert.match(arm(crossing),
    /^Level crossing plate — ahead armed\. No open end takes it: two road plates cannot meet\.$/);
  // A straight joins the crossing's end; a bridge arch joins only a ramp's top.
  assert.match(arm({piece: "straight", pieceName: "Straight rail", label: "ahead"}),
    /Click a red arrow to attach/);
  assert.match(arm({piece: "span", pieceName: "Bridge arch", label: "climb", takes: ["ramp_top"]}),
    /No open end takes it: it joins only a ramp's top\./);
  // With a bridge ramp's top open as well, the only end of the plate's kind is still
  // the crossing's.
  const ramp = track([[512, 0, 0], [832, 0, 57.6]], "Bridge ramp");
  ramp.ports = [{port: 0, open: false, sealed: false, x: 512, y: 0, deg: 180, name: "low"},
    {port: 1, open: true, sealed: false, x: 832, y: 0, deg: 0, name: "high", kind: "ramp_top"}];
  placements.push(ramp);
  assert.match(arm(crossing), /No open end takes it: two road plates cannot meet\./);
  // With only the ramp's top open, no end is of a kind the plate joins at all.
  placements[0].ports[0].open = false;
  assert.match(arm(crossing), /No open end takes it: it joins only ordinary track\./);
});

// A level crossing plate's end meets a bridge ramp's foot unjoined, as where a loop comes
// round to its start. The plate's far end and the ramp's top are open, meeting nothing.
function meetingScene() {
  const crossing = track([[0, 0, 0], [128, 0, 0]], "Level crossing plate");
  crossing.plate = true;
  crossing.ports = [{port: 0, open: true, sealed: false, x: 0, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: false, x: 128, y: 0, deg: 0, name: "b"}];
  const ramp = track([[128, 0, 0], [448, 0, 57.6]], "Bridge ramp");
  ramp.ports = [{port: 0, open: true, sealed: false, x: 128, y: 0, deg: 180, name: "low"},
    {port: 1, open: true, sealed: false, x: 448, y: 0, deg: 0, name: "high", kind: "ramp_top"}];
  const state = scene([crossing, ramp]);
  state.open_ends = [[0, 0], [0, 1], [1, 0], [1, 1]];
  state.matable = [[[0, 1], [1, 0]]];
  return state;
}

test("ends that meet keep red arrows though the armed piece cannot take their kind", () => {
  // A click there joins the two ends, armed piece or not. The plate's far end, ordinary
  // track meeting nothing, greys under an armed bridge arch though the plate's other end
  // meets the ramp; the ramp's top takes the arch.
  const h = harness({state: meetingScene(), events: true,
    overrides: {devicePixelRatio: 1, worldToScreen: (x, y) => [x, y]}});
  h.run('selectTool({piece: {piece: "span", pieceName: "Bridge arch", label: "climb", takes: ["ramp_top"]}})');
  const dots = dotColours(h, {every: true});
  // The meeting ends share the dot at (128, 0), and each is painted red there.
  assert.deepEqual([dots["0,0"], dots["128,0"], dots["448,0"]],
    [["#a7adb3"], ["#d0342c", "#d0342c"], ["#d0342c"]]);
});

test("an armed piece's status counts ends that meet as joins, not as places to attach", () => {
  // A click on an end that meets its mate joins the two, so the status names only the
  // other open ends as places to attach, and says what a click on a meeting end does.
  const h = harness({state: meetingScene()});
  const arm = piece => {
    h.run(`selectTool({piece: ${JSON.stringify(piece)}}); refreshStatus()`);
    return h.notices.at(-1).text;
  };
  const straight = {piece: "straight", pieceName: "Straight rail", label: "ahead"};
  const arch = {piece: "span", pieceName: "Bridge arch", label: "climb", takes: ["ramp_top"]};
  const crossing = {piece: "level_crossing", pieceName: "Level crossing plate", label: "ahead",
    plate: true};
  const [plate, ramp] = h.context.S.layout.placements.map(pl => pl.ports);
  const joins = " Ends that meet join on a click.";
  // The arch joins the ramp's top, a straight the plate's far end, which a second plate
  // cannot meet. The ramp's foot, ordinary track, meets its mate.
  assert.equal(arm(arch), "Bridge arch — climb armed. Click a red arrow to attach." + joins);
  assert.equal(arm(straight), "Straight rail — ahead armed. Click a red arrow to attach." + joins);
  assert.equal(arm(crossing),
    "Level crossing plate — ahead armed. No open end takes it: two road plates cannot meet." + joins);
  // With the plate's far end taken, only the meeting ends are ordinary track.
  plate[0].open = false;
  assert.equal(arm(straight),
    "Straight rail — ahead armed. No open end takes it: it joins only ordinary track." + joins);
  // With the ramp's top taken too, the meeting ends are all that is open.
  ramp[1].open = false;
  for (const piece of [straight, arch]) {
    assert.equal(arm(piece),
      `${piece.pieceName} — ${piece.label} armed. Every open end meets another: click one to join them.`);
  }
  // On a loop closed with a forced joint no end is open, so none meets another.
  plate[1].open = ramp[0].open = false;
  h.context.S.matable = [];
  assert.equal(arm(straight), "Straight rail — ahead armed. No open end takes it: it joins only ordinary track.");
});

// Stones at two heights. A straight at height z through the origin, along x or y.
function level(z, vertical = false) {
  const line = vertical ? [[0, -64, z], [0, 64, z]] : [[-64, 0, z], [64, 0, z]];
  return {...track(line, `Straight at ${z}`), stone_ok: true, mid: [0, 0],
    ports: line.map(([x, y], port) => ({x, y, port}))};
}
// A ground straight and one 153.6 mm above it crossing at their midpoints, in either
// order, with a Stop stone on the ground one and a Direction stone on the raised one.
function stacked(reverse = false, stones = false) {
  const bottom = level(0), top = level(153.6, true);
  if (stones) {
    bottom.stone_marks = [{id: "stone_stop", at: null}];
    top.stone_marks = [{id: "stone_direction", at: null}];
  }
  const placements = reverse ? [top, bottom] : [bottom, top];
  const state = scene(placements); state.instance = "test-engine";
  state.stones.catalog = {stone_stop: {name: "Stop stone", color: "#c4281c"},
    stone_direction: {name: "Direction stone", color: "#237841"}};
  const h = harness({state, overrides: {devicePixelRatio: 1, worldToScreen: (x, y) => [x, y], redraw() {}}});
  h.run("canvas = {clientWidth: 500, clientHeight: 500}");
  h.upper = placements.indexOf(top);
  h.lower = placements.indexOf(bottom);
  return h;
}
const chooser = h => h.el("overlap-picker").children;
// The fill colours of the stone marks in the order painted.
function stoneFills(h) {
  const fills = [], none = () => {};
  let arc = false;
  h.context.recorder = new Proxy({arc() { arc = true; }, beginPath() { arc = false; },
    fill() { if (arc) fills.push(this.fillStyle); }}, {get: (t, p) => p in t ? t[p] : none});
  h.run("ctx = recorder; paint()");
  return fills.filter(fill => fill === "#c4281c" || fill === "#237841");
}

for (const reverse of [false, true]) {
  test(`stones paint in the height order of their track, placed ${reverse ? "raised" : "ground"} first`, () => {
    // The raised stone covers the ground one whichever straight was laid first.
    assert.deepEqual(stoneFills(stacked(reverse, true)), ["#c4281c", "#237841"]);
  });

  test(`an armed stone over track at two heights asks where, raised first (placed ${reverse ? "raised" : "ground"} first)`, async () => {
    const h = stacked(reverse);
    h.run('selectTool({stone: "stone_stop"})');
    await h.run("activateAt(0, 0)");
    assert.equal(h.calls.length, 0);
    assert.equal(h.run("selectedPiece"), h.upper);
    assert.match(chooser(h)[1].children[0].textContent, /153\.6 mm · Stop stone · midpoint$/);
    await chooser(h)[2].click();
    assert.deepEqual(h.calls.map(c => [c.path, c.body.placement, c.body.id, c.body.at_port, c.body.remove]),
      [["/api/stone", h.upper, "stone_stop", null, false]]);
  });

  test(`a stone removed over stones at two heights asks which, the one painted on top first (placed ${reverse ? "raised" : "ground"} first)`, async () => {
    const h = stacked(reverse, true);
    assert.equal(h.run("stoneMarkPositions().at(-1).id"), "stone_direction");
    await h.run("removeAt(0, 0)");
    assert.equal(h.calls.length, 0);
    assert.equal(h.run("selectedPiece"), h.upper);
    await chooser(h)[2].click();
    assert.deepEqual(h.calls.map(c => [c.body.placement, c.body.id, c.body.at_port, c.body.remove]),
      [[h.upper, "stone_direction", null, true]]);
  });
}

test("the stone chooser can take the lower track though the selection moves", async () => {
  const h = stacked(false, true);
  await h.run("removeAt(0, 0)");
  const [, select, confirm] = chooser(h);
  select.value = "1"; select.fire("change");
  h.run("selectedPiece = 1");
  await confirm.click();
  assert.deepEqual([h.calls[0].body.placement, h.calls[0].body.id], [0, "stone_stop"]);
});

for (const change of ["revision", "engine", "tool", "cancel", "replace", "selection", "job", "invalid"]) {
  test(`a stone chooser does nothing after ${change}`, async () => {
    const h = stacked(false, true);
    await h.run("removeAt(0, 0)");
    const [, select, confirm, cancel] = chooser(h);
    if (change === "revision") h.run("S.revision++");
    if (change === "engine") h.run('S.instance = "new-engine"');
    if (change === "tool") h.run("selectTool()");
    if (change === "cancel") cancel.click();
    if (change === "replace") await h.run("removeAt(0, 0)");
    if (change === "selection") h.run("focusPieces([0])");
    if (change === "job") h.run("jobLoop = true");
    if (change === "invalid") { select.value = "999"; select.fire("change"); }
    await confirm.click();
    assert.equal(h.calls.length, 0);
  });
}

for (const change of ["revision", "engine"]) {
  test(`a stale stone chooser keeps its target after ${change}`, async () => {
    const h = stacked(false, true);
    await h.run("removeAt(0, 0)");
    const [, select] = chooser(h);
    h.run(change === "revision" ? "S.revision++" : 'S.instance = "new-engine"');
    select.value = "1"; select.fire("change");
    assert.equal(h.run("selectedPiece"), h.upper);
  });
}

test("stacked face stones keep their own faces and identities in the chooser", async () => {
  // Zoomed far out, face stones at two heights fall on one spot.
  const low = level(0), high = level(153.6);
  low.stone_marks = [{id: "stone_stop", at: 0}];
  high.stone_marks = [{id: "stone_direction", at: 1}];
  for (const pl of [low, high]) { pl.ports[0].x = -1; pl.ports[1].x = 1; }
  const h = harness({state: scene([low, high]), overrides: {worldToScreen: (x, y) => [x, y], redraw() {}}});
  h.run("view.scale = 0.1");
  await h.run("removeAt(0, 0)");
  const [, select, confirm] = chooser(h);
  assert.equal(select.children.length, 2);
  select.value = "1"; select.fire("change");
  await confirm.click();
  assert.deepEqual(h.calls.map(c => [c.body.placement, c.body.id, c.body.at_port]), [[0, "stone_stop", 0]]);
});

test("stones at one height keep the nearest rule, even painted over each other", async () => {
  // Two level straights crossing at one height, a stone on each at the crossing: the
  // direction mark lies 3 px east of the stop mark, over it.
  const a = level(0), b = level(0, true);
  a.stone_marks = [{id: "stone_stop", at: null}];
  b.stone_marks = [{id: "stone_direction", at: null}];
  b.mid = [3, 0];
  const h = harness({state: scene([a, b]), overrides: {worldToScreen: (x, y) => [x, y], redraw() {}}});
  await h.run("removeAt(2, 0)");
  await h.run("removeAt(1, 0)");
  assert.equal(h.el("overlap-picker").hidden, true);
  assert.deepEqual(h.calls.map(c => c.body.id), ["stone_direction", "stone_stop"]);
});

test("off the overlap the stone or track under the pointer is taken directly", async () => {
  // The ground mark sits 20 px east of the raised one. A click inside one mark only
  // means that one, though the other lies within its 18 px reach.
  const h = stacked(false, true);
  h.context.S.layout.placements[0].mid = [20, 0];
  await h.run("removeAt(17, 0)");
  await h.run("removeAt(3, 0)");
  assert.equal(h.el("overlap-picker").hidden, true);
  assert.deepEqual(h.calls.map(c => [c.body.placement, c.body.id]), [[0, "stone_stop"], [1, "stone_direction"]]);
  // Both midpoints lie within reach of a click 24 px up the raised straight, or 24 px
  // along the ground one, off the other's track: the straight under the pointer takes it.
  const place = stacked(false);
  place.run('selectTool({stone: "stone_stop"})');
  await place.run("activateAt(0, 24)");
  await place.run("activateAt(24, 0)");
  assert.equal(place.el("overlap-picker").hidden, true);
  assert.deepEqual(place.calls.map(c => [c.body.placement, c.body.at_port]), [[1, null], [0, null]]);
});

test("places at one height keep the nearest rule, whichever straight is under the pointer", async () => {
  // Level straights meet at the origin; 10 px onto the second one both joint faces lie
  // 10 px away, and the tie goes to the first straight's face, the lower index.
  const a = {...level(0), mid: [-64, 0], lines: [[[-128, 0, 0], [0, 0, 0]]],
    ports: [{x: -128, y: 0, port: 0}, {x: 0, y: 0, port: 1}]};
  const b = {...level(0), mid: [64, 0], lines: [[[0, 0, 0], [128, 0, 0]]],
    ports: [{x: 0, y: 0, port: 0}, {x: 128, y: 0, port: 1}]};
  const h = harness({state: scene([a, b]), overrides: {worldToScreen: (x, y) => [x, y], redraw() {}}});
  assert.equal(h.run("placementAt(10, 0)"), 1);
  h.run('selectTool({stone: "stone_stop"})');
  await h.run("activateAt(10, 0)");
  assert.deepEqual(h.calls.map(c => [c.body.placement, c.body.at_port]), [[0, 1]]);
});

test("a joint of raised straights keeps the nearest rule though a ground place is in reach", async () => {
  // Two straights 76.8 mm up meet at the origin; a ground straight runs north 25 px
  // east of the joint, its midpoint 27 px away: in reach, its track not under the pointer.
  const raised = (x0, x1) => ({...track([[x0, 0, 76.8], [x1, 0, 76.8]]), stone_ok: true,
    mid: [(x0 + x1) / 2, 0], ports: [{x: x0, y: 0, port: 0}, {x: x1, y: 0, port: 1}]});
  const ground = {...track([[25, -64, 0], [25, 64, 0]]), stone_ok: true, mid: [25, 10],
    ports: [{x: 25, y: -64, port: 0}, {x: 25, y: 64, port: 1}]};
  const h = harness({state: scene([raised(-128, 0), raised(0, 128), ground]),
    overrides: {worldToScreen: (x, y) => [x, y], redraw() {}}});
  h.run('selectTool({stone: "stone_stop"})');
  await h.run("activateAt(0, 0)");
  assert.equal(h.el("overlap-picker").hidden, true);
  assert.deepEqual(h.calls.map(c => [c.body.placement, c.body.at_port]), [[0, 1]]);
});

for (const z of [0, 153.6]) {
  test(`a joint at ${z} mm keeps the nearest rule though a place at the other height is in reach`, async () => {
    // Zoomed out, two straights at one height meet at the origin, and a straight at the
    // other height lies flush beside the second one: its first face is 17 px from a tap
    // 6 px onto the second straight, in reach, its track not under the pointer. Both
    // joint faces are 6 px away, and the tie goes to the first straight's face, as it
    // does with no other height near.
    const level = (x0, y0, x1, y1, z) => ({...track([[x0, y0, z], [x1, y1, z]]), width: 64,
      stone_ok: true, mid: [(x0 + x1) / 2, (y0 + y1) / 2],
      ports: [{x: x0, y: y0, port: 0}, {x: x1, y: y1, port: 1}]});
    const joint = [level(-128, 0, 0, 0, z), level(0, 0, 128, 0, z)];
    for (const placements of [joint, [...joint, level(0, 16, 128, 16, z ? 0 : 153.6)]]) {
      const h = harness({state: scene(placements), overrides: {worldToScreen: (x, y) => [x, y], redraw() {}}});
      h.run("view.scale = 0.25");
      h.run('selectTool({stone: "stone_stop"})');
      await h.run("activateAt(6, 0)");
      assert.equal(h.el("overlap-picker").hidden, true);
      assert.deepEqual(h.calls.map(c => [c.body.placement, c.body.at_port]), [[0, 1]]);
    }
  });
}

for (const [x, at] of [[-70, 0], [0, null], [70, 1]]) {
  test(`a lone straight still takes the face or midpoint clicked at x=${x}`, async () => {
    const state = scene([level(0)]);
    state.stones.catalog = {stone_stop: {name: "Stop stone"}};
    const h = harness({state, overrides: {worldToScreen: (x, y) => [x, y], redraw() {}}});
    h.run('selectTool({stone: "stone_stop"})');
    await h.context.activateAt(x, 0);
    assert.deepEqual(h.calls.map(c => [c.body.placement, c.body.at_port]), [[0, at]]);
  });
}

test("a stone stands at its straight's height, read from the drawn centreline", () => {
  const pl = level(76.8);
  pl.stone_marks = [{id: "stone_stop", at: 0}, {id: "stone_direction", at: null}];
  const h = harness({state: scene([pl]), overrides: {worldToScreen: (x, y) => [x, y]}});
  const heights = code => Array.from(h.run(code));
  assert.deepEqual(heights("stoneMarkPositions().map(m => m.z)"), [76.8, 76.8]);
  assert.deepEqual(heights("[stoneMountsAt(-64, 0)[0].z, stoneMountsAt(0, 0)[0].z]"), [76.8, 76.8]);
  delete pl.lines;  // nothing drawn to read a height from
  assert.deepEqual(heights("stoneMarkPositions().map(m => m.z)"), [0, 0]);
});
