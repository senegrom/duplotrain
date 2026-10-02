"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");

function straight(z, vertical = false) {
  const line = vertical ? [[0,-64,z],[0,64,z]] : [[-64,0,z],[64,0,z]];
  return {...track(line, `Straight at ${z}`), stone_ok: true, mid: [0,0,z],
    ports: line.map(([x,y,z], port) => ({x,y,z,port}))};
}
function setup(reverse = false, stones = false, extra = {}) {
  const bottom = straight(0), top = straight(153.6, true);
  if (stones) {
    bottom.stone_marks = [{id:"stone_stop", at:null}];
    top.stone_marks = [{id:"stone_direction", at:null}];
  }
  const placements = reverse ? [top,bottom] : [bottom,top];
  const state = scene(placements); state.instance = "test-engine";
  state.stones.catalog = {stone_stop:{name:"Stop stone"}, stone_direction:{name:"Direction stone"}};
  const h = harness({state, ...extra, overrides: {worldToScreen:(x,y)=>[x,y], redraw() {}, ...extra.overrides}});
  h.run("canvas={clientWidth:500,clientHeight:500}");
  h.upper = placements.indexOf(top);
  return h;
}
const picker = h => h.el("overlap-picker").children;

for (const reverse of [false,true]) {
  test(`stone placement follows visible track, order reversed=${reverse}`, async () => {
    const h = setup(reverse);
    h.run('selectTool({stone:"stone_stop"})');
    assert.equal(h.run('stoneMountsAt(0,0)[0].placement'), h.run('placementAt(0,0)'));
    await h.run('activateAt(0,0)');
    assert.equal(h.calls.length,0);
    assert.equal(h.run('selectedPiece'),h.upper);
    assert.match(picker(h)[1].children[0].textContent,/153\.6 mm/);
    await picker(h)[2].click();
    assert.equal(h.calls[0].path,"/api/stone");
    assert.equal(h.calls[0].body.placement,h.upper);
    assert.equal(h.calls[0].body.at_port,null);
    assert.equal(h.calls[0].body.id,"stone_stop");
  });
  test(`overlapping removal chooses the marker painted last, order reversed=${reverse}`, async () => {
    const h = setup(reverse,true);
    assert.equal(h.run('stoneMarkPositions().at(-1).id'),"stone_direction");
    assert.equal(h.run('stoneMarksAt(0,0)[0].id'),"stone_direction");
    await h.run('removeAt(0,0)');
    assert.equal(h.calls.length,0);
    assert.equal(h.run('selectedPiece'),h.upper);
    await picker(h)[2].click();
    assert.equal(h.calls[0].body.placement,h.upper);
    assert.equal(h.calls[0].body.id,"stone_direction");
    assert.equal(h.calls[0].body.remove,true);
  });
}

test("the chooser can deliberately target lower track without global selection retargeting it", async () => {
  const h=setup(false,true);
  await h.run('removeAt(0,0)');
  const [,select,confirm]=picker(h);
  select.value="1"; select.fire("change");
  h.run('selectedPiece=1');
  await confirm.click();
  assert.equal(h.calls[0].body.placement,0);
  assert.equal(h.calls[0].body.id,"stone_stop");
});

for (const change of ["revision","engine","tool","cancel","replace","selection","job","invalid"]) {
  test(`a stone chooser cannot mutate after ${change}`, async () => {
    const h=setup(false,true);
    await h.run('removeAt(0,0)');
    const [,select,confirm,cancel]=picker(h);
    if(change==="revision") h.run('S.revision++');
    if(change==="engine") h.run('S.instance="new-engine"');
    if(change==="tool") h.run('selectTool()');
    if(change==="cancel") cancel.click();
    if(change==="replace") await h.run('removeAt(0,0)');
    if(change==="selection") h.run('focusPieces([0])');
    if(change==="job") h.run('jobLoop=true');
    if(change==="invalid") {select.value="999";select.fire("change");}
    await confirm.click();
    assert.equal(h.calls.length,0);
  });
}

test("two overlapping face stones on one piece keep their own identities", async () => {
  const pl=straight(0); pl.ports[0].x=-1;pl.ports[1].x=1;
  pl.stone_marks=[{id:"stone_stop",at:0},{id:"stone_direction",at:1}];
  const state=scene([pl]);state.stones.catalog={};
  const h=harness({state,overrides:{worldToScreen:(x,y)=>[x,y],redraw(){}}});
  h.run('view.scale=0.1');
  await h.run('removeAt(0,0)');
  const [,select,confirm]=picker(h);
  assert.equal(select.children.length,2);
  select.value="1";select.fire("change");
  await confirm.click();
  assert.equal(h.calls[0].body.placement,0);
  assert.equal(h.calls[0].body.id,"stone_stop");
  assert.equal(h.calls[0].body.at_port,0);
});

for(const [x,at] of [[-70,0],[0,null],[70,1]]) {
  test(`single target retains midpoint/face and touch padding at x=${x}`, async()=>{
    const state=scene([straight(0)]);
    state.stones.catalog={stone_stop:{name:"Stop stone"}};
    const h=harness({state,overrides:{worldToScreen:(x,y)=>[x,y],redraw(){}}});
    h.run('selectTool({stone:"stone_stop"})');
    await h.context.activateAt(x,0);
    assert.equal(h.calls.length,1);
    assert.equal(h.calls[0].body.at_port,at);
    assert.equal(h.calls[0].body.placement,0);
  });
}

test("legacy marker geometry without z remains finite",()=>{
  const pl=straight(0);pl.mid=[0,0];for(const p of pl.ports)delete p.z;
  pl.stone_marks=[{id:"stone_stop",at:0}];
  const h=harness({state:scene([pl]),overrides:{worldToScreen:(x,y)=>[x,y]}});
  assert.equal(h.run('stoneMarkPositions()[0].z'),0);
});
