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
