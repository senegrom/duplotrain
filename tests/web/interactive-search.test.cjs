"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");
const clean = x => JSON.parse(JSON.stringify(x));
const turn = () => new Promise(resolve => setImmediate(resolve));
const candidate = (index, revision = 7) => ({index, revision,
  exact: true, gap: 0, kind: "loop", added: {curve: 6}, size_cm: [50, 50], open_stubs: 0,
  preview: {format: "duplotrain-preview/1", base_count: 0, base_revision: revision, placements: []}});
const job = (extra = {}) => ({job_id: "job-A", revision: 7, status: "running", stage: "plain track",
  searched: 32, found: 0, target: 8, page: 0, candidates: [], complete: false, optimal: false,
  max_pieces: 26, search_effort: 1, resumable: true, can_harden: true, ...extra});
const route = (extra = {}) => ({job_id: "route-A", revision: 7, status: "running", scope: "all",
  runs: 1, required_runs: "4", step_limited_runs: 0, total_drivable: 3, best: null,
  counterexample: null, classification: null, complete: false, ...extra});
function app(overrides = {}) {
  const state = scene([], 7);
  state.open_ends = [[0, 0], [5, 1]];
  return harness({state, events: true, overrides: {setTimeout: fn => { fn(); return 1; },
    redraw() {}, ...overrides}});
}

for (const value of ["0,0,1", "0,0,0,1", "0,0,Infinity,1", "0,0,,1", "0,0,1000001,1"]) {
  test(`room input rejects ${value} before any API call`, async () => {
    const h = app(); h.el("room-bounds").value = value;
    await h.run("startInteractiveSearch(null,null)");
    assert.equal(h.calls.length, 0);
    assert.match(h.notices.at(-1).text, /Rectangles/);
  });
}

test("preferences use centimetres in controls and millimetres in the validated API", () => {
  const h = app(); h.el("room-bounds").value = "-10,-20,200,300";
  h.el("keep-out").value = "1,2,3,4\n\n5,6,7,8";
  const options = clean(h.run("readSearchOptions()"));
  assert.deepEqual(options.room, [-100,-200,2000,3000]);
  assert.deepEqual(options.keep_out, [[10,20,30,40],[50,60,70,80]]);
  h.context.options = options; h.run("restoreSearchOptions(options)");
  assert.deepEqual(clean(h.run("readSearchOptions()")), options);
  h.el("keep-out").value = Array(33).fill("1,2,3,4").join("\n");
  assert.throws(() => h.run("readSearchOptions()"), /32/);
});

test("excluded categories change next-search options, never inventory", async () => {
  const h = app(); h.context.S.palette = [
    {id: "custom-junction", name: "Junction", junction: true, category: "track"},
    {id: "custom-bridge", name: "Bridge", category: "bridge"},
    {id: "straight", name: "Straight", junction: false, category: "track"},
  ];
  const before = clean(h.context.S.inventory);
  await h.el("avoid-junctions").click(); await h.el("avoid-bridges").click();
  assert.deepEqual(clean(h.run("readSearchOptions().exclude")), ["custom-bridge", "custom-junction"]);
  assert.deepEqual(clean(h.context.S.inventory), before); assert.equal(h.calls.length, 0);
  await h.el("reset-exclusions").click(); assert.deepEqual(clean(h.run("readSearchOptions().exclude")), []);
});

test("project saved-change indicator includes optional search restrictions and reversion", () => {
  const h = app(); h.run("markProjectSaved(projectSnapshot())");
  h.el("room-bounds").value = "-100,-100,100,100"; h.run("updateProjectStatus()");
  assert.match(h.el("project-status").textContent, /^Changed/);
  assert.deepEqual(clean(h.run("projectSnapshot().preferences.search.options.room")), [-1000,-1000,1000,1000]);
  h.el("room-bounds").value = ""; h.run("updateProjectStatus()");
  assert.match(h.el("project-status").textContent, /^Unchanged/);
});

test("streamed suggestions cannot apply before pause publishes their exact revision", async () => {
  const calls = []; let finishTick, ticks = 0, h;
  const pending = new Promise(resolve => { finishTick = resolve; });
  const preview = job({found: 1, candidates: [candidate(0)]});
  h = app({api: async (path, body) => {
    calls.push({path, body: clean(body)});
    if (path.endsWith("/start")) return job();
    if (path.endsWith("/tick")) return ++ticks === 1 ? preview : pending;
    if (path.endsWith("/pause")) return {...preview, status: "paused"};
    if (path.endsWith("/publish")) return {...h.context.S, revision: 8, candidates: [candidate(0, 8)],
      search_job: {...preview, status: "paused", revision: 8, candidates: [candidate(0, 8)]}};
    throw new Error("Unexpected API: " + path);
  }});
  const before = clean(h.context.S.snapshot);
  const search = h.run("startInteractiveSearch(null,null)");
  await turn();
  assert.equal(ticks, 2);
  h.run('selectedCandidate="7:0"; renderCandidates()');
  const row = h.run("candidateRows[0]"); assert.equal(row.apply.disabled, true);
  await row.apply.listeners.click();
  assert.ok(!calls.some(c => c.path === "/api/apply"));
  h.run("requestJobPause()"); finishTick(preview); await search;
  h.run("renderCandidates()");
  assert.equal(h.run("interactiveJob.status"), "paused");
  assert.equal(h.context.S.revision, 8);
  assert.equal(h.run("selectedCandidate"), "8:0");
  assert.equal(h.run("candidateRows[0].apply.disabled"), false);
  assert.deepEqual(clean(h.context.S.snapshot), before);
  assert.ok(calls.some(c => c.path === "/api/search/pause"));
  assert.ok(calls.some(c => c.path === "/api/search/publish"));
  assert.ok(!calls.some(c => /restore|undo|restart/.test(c.path)));
});

test("Find more continues the same job with a stable candidate index, separate from harder", async () => {
  const calls = []; let h;
  h = app({api: async (path, body) => {
    calls.push({path, body: clean(body)});
    if (path.endsWith("/continue")) return job({target: 16, found: 16, status: "results_ready", candidates: [candidate(0)]});
    if (path.endsWith("/publish")) return {...h.context.S, revision: 8,
      search_job: job({revision: 8, found: 16, target: 16, status: "results_ready", candidates: [candidate(0,8)]})};
    throw new Error(path);
  }});
  h.context.initial = job({status: "results_ready", found: 8, candidates: [candidate(0)]});
  h.run("interactiveJob=initial; renderJobControls(); selectedCandidate='7:0'");
  await h.el("find-more").click();
  assert.equal(calls[0].path, "/api/search/continue");
  assert.equal(calls[0].body.job_id, "job-A"); assert.equal(calls[0].body.harder, false);
  assert.equal(h.run("interactiveJob.found"),16);
  assert.equal(h.el("max-pieces").value,"26");
  assert.equal(h.run("selectedCandidate"), "8:0");
});

test("paging and sorting use stable engine indices, never the page-local row", async () => {
  const calls = [];
  const h = app({api: async (path, body) => {
    calls.push({path, body: clean(body)});
    return job({status: "results_ready", found: 16, page: body.page, candidates: [candidate(13)]});
  }});
  h.context.initial = job({status: "results_ready", found: 16, candidates: [candidate(0)]});
  h.run("interactiveJob=initial"); h.el("candidate-sort").value="footprint";
  await h.run("searchPageTo(1)");
  assert.equal(calls[0].body.page,1); assert.equal(calls[0].body.sort,"footprint");
  const row=h.run("candidateRows[0]"); await row.show.click(); await row.apply.click();
  assert.equal(calls[1].path,"/api/apply"); assert.equal(calls[1].body.index,13);
});

test("failed tick drops unpublished preview indices instead of enabling stale Apply", async () => {
  let ticks=0;
  const h=app({api:async path=> {
    if (path.endsWith("/start")) return job();
    if (path.endsWith("/tick") && ++ticks===1) return job({found:1,candidates:[candidate(42)]});
    throw new Error("Worker failed");
  }});
  h.context.S.candidates=[candidate(0)];
  await h.run("startInteractiveSearch(null,null)");
  assert.equal(h.run("interactiveJob"),null);
  assert.equal(h.run("selectedCandidate"),null);
  // Starting the job withdrew the older suggestions; none return as applicable.
  assert.deepEqual(clean(h.run("visibleCandidates()")),[]);
  assert.equal(h.run("candidateRows.length"),0);
  assert.match(h.notices.at(-1).text,/Worker failed/);
});

test("an old tick cannot replace imported/restarted content even with reused revision", async () => {
  let finish;
  const h=app({api: async path => path.endsWith("/start") ? job() :
    new Promise(resolve=>{finish=resolve;})});
  const pending=h.run("startInteractiveSearch(null,null)"); await turn();
  h.run("clearInteractiveState(); S={...S,snapshot:{replacement:true}}");
  finish(job({status:"results_ready",found:1,candidates:[candidate(0)]})); await pending;
  assert.equal(h.run("interactiveJob"),null); assert.equal(h.context.S.snapshot.replacement,true);
});

test("route analysis labels incomplete bounds and loads the selected witness only", async () => {
  let traceBody;
  const h=app({testTrain:async ()=>{traceBody={start:h.el("train-start").value,
    switches:clean(h.run("initialSwitches"))};}});
  h.context.report={job_id:"route-A",revision:7,status:"limited",scope:"selected",runs:3,
    required_runs:"64",max_runs:3,max_steps:10000,step_limited_runs:0,total_drivable:83,
    best:{start:[0,0],switch_states:{5:2,6:2},visited:57,cycle_visited:26},counterexample:null,
    complete:false,optimal:false,classification:null};
  h.run("routeAnalysis=report; showRouteAnalysis()");
  const text=h.el("route-report").children.map(c=>c.textContent).join(" ");
  assert.match(text,/among completed runs so far/); assert.match(text,/No universal verdict/);
  assert.match(text,/57 \/ 83/); assert.match(text,/26 visited in the repeating cycle/);
  await h.el("route-witness").click();
  assert.equal(traceBody.start,"[0,0]"); assert.deepEqual(traceBody.switches,{5:2,6:2});
});

test("Load counterexample loads the counterexample's start and switches, not the best route", async () => {
  let traceBody;
  const h = app({testTrain: async () => { traceBody = {start: h.el("train-start").value,
    switches: clean(h.run("initialSwitches"))}; }});
  h.context.report = route({status: "complete", complete: true,
    best: {start: [0, 0], switch_states: {5: 1}, visited: 3, cycle_visited: 3},
    counterexample: {start: [2, 1], switch_states: {5: 2}, visited: 1, cycle_visited: 0},
    classification: {looping: false, completely_looping: false, perfectly_looping: false}});
  h.run("routeAnalysis = report; showRouteAnalysis()");
  assert.equal(h.el("route-counterexample").hidden, false);
  await h.el("route-counterexample").click();
  assert.deepEqual(traceBody, {start: "[2,1]", switches: {5: 2}});
});

test("Pause stops a route analysis at its next checkpoint and offers Resume", async () => {
  const paths = []; let h, ticks = 0;
  h = app({api: async path => {
    paths.push(path);
    if (path === "/api/routes/start") return route();
    if (path === "/api/routes/pause") return route({runs: 2, status: "paused"});
    if (path !== "/api/routes/tick") throw new Error("Unexpected API: " + path);
    if (++ticks === 1) h.el("route-pause").click();  // pressed while the first tick runs
    return ticks < 4 ? route({runs: 1 + ticks}) : route({status: "complete", complete: true});
  }});
  await h.run('startRouteAnalysis("all")');
  assert.deepEqual(paths, ["/api/routes/start", "/api/routes/tick", "/api/routes/pause"]);
  assert.equal(h.run("routeAnalysis.status"), "paused");
  assert.equal(h.el("route-pause").hidden, true);
  assert.equal(h.el("route-resume").hidden, false);
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

test("paused preview uses its captured constraints rather than newer draft controls", () => {
  const drawn = [];
  const h = app({worldToScreen: (x, y) => [x, y], screenBoundsVisible: () => true,
    readSearchOptions() { throw new Error("draft controls must not determine a saved search overlay"); }});
  h.context.paint = {save() {}, restore() {}, setLineDash() {}, strokeRect(...box) { drawn.push(box); }};
  h.context.snapshot = job({options: {room: [0, 0, 100, 200], keep_out: [], exclude: []}, status: "paused"});
  h.run("interactiveJob = snapshot; ctx = paint; drawFloorConstraints(); renderJobControls()");
  assert.deepEqual(drawn, [[0, 200, 100, 200]]);
  assert.match(h.el("search-report").textContent, /changed controls apply to a new search/);
});

for (const [finished, message] of [
  [{complete: false}, /within these limits\. A closure may still exist/],
  [{complete: true}, /No completion fits the remaining inventory/],
  [{complete: true, reason: "impossible: those ends differ by 58 mm in height"}, /differ by 58 mm/],
]) {
  test(`a search without results says why: ${message.source.slice(0, 30)}`, async () => {
    let h;
    const done = job({status: "exhausted", found: 0, resumable: false, ...finished});
    h = app({api: async path => {
      if (path.endsWith("/start")) return done;
      if (path.endsWith("/publish")) return {...h.context.S, revision: 8, search_job: {...done, revision: 8}};
      throw new Error("Unexpected API: " + path);
    }});
    await h.run("startInteractiveSearch(null,null)");
    assert.match(h.notices.at(-1).text, message);
    assert.equal(h.notices.at(-1).kind, "err");
  });
}

test("Close the loop and Search harder ignore clicks before state loads and during work", async () => {
  const calls = [];
  const h = app({api: async (path, body) => { calls.push([path, body.harder]); throw new Error("refused"); }});
  // A paused search of the shown revision, which Search harder, Find more and
  // Resume would continue: only the loading and busy guards can refuse them.
  h.context.paused = job({status: "paused", found: 8});
  h.run("interactiveJob = paused");
  for (const setup of ["S = null", "S = {revision: 7, open_ends: []}; apiBusy = true", "apiBusy = false; jobLoop = true"]) {
    h.run(setup);
    for (const id of ["solve", "expand-search", "find-more", "resume-search"]) await h.el(id).click();
  }
  assert.deepEqual(calls, []);
  h.run("jobLoop = false");
  await h.el("expand-search").click();
  assert.deepEqual(calls, [["/api/search/continue", true]]);
});

test("the busy state holds through a whole search instead of flickering per tick", async () => {
  const state = scene([], 7); state.open_ends = [[0, 0], [5, 1]];
  let body = null, ticks = 0; const gaps = [];
  const h = harness({state, events: true, omit: ["api"], overrides: {redraw() {},
    // nextJobTurn yields here between ticks: the controls must stay busy.
    setTimeout: fn => { if (body) gaps.push(body.classes.has("busy")); fn(); return 1; }}});
  body = h.context.document.body;
  h.context.window.duplotrainApi = async path => {
    if (path.endsWith("/start")) return job();
    if (path.endsWith("/tick")) return ++ticks < 3 ? job({searched: 32 * ticks}) :
      job({status: "results_ready", found: 1, candidates: [candidate(0)]});
    return {...h.context.S, revision: 8, search_job: job({status: "results_ready", revision: 8, found: 1})};
  };
  await h.run("startInteractiveSearch(null, null)");
  assert.equal(ticks, 3);
  assert.deepEqual(gaps, [true, true]);
  assert.equal(body.classes.has("busy"), false);
});

test("Close all gaps asks for exact, non-reversing joins whatever the pair settings say", async () => {
  const bodies = [];
  const h = app({api: async (path, body) => { bodies.push(clean(body)); throw new Error("stop"); }});
  h.el("reversing").checked = true; h.el("slop").value = 5;
  await h.el("close-all").click();
  await h.el("solve").click();
  assert.deepEqual(bodies.map(b => [b.all_gaps, b.reversing, b.slop]), [[true, false, 0], [false, true, 5]]);
});

test("a ranking chosen while a search runs applies from its next tick, on the first page", async () => {
  const calls = []; let ticks = 0, h;
  h = app({api: async (path, body) => {
    calls.push({path, body: clean(body)});
    if (path.endsWith("/resume")) return job({found: 16, page: 1});
    if (path.endsWith("/tick")) {
      if (++ticks === 1) { h.el("candidate-sort").value = "pieces"; h.el("candidate-sort").fire("change"); }
      return ticks < 2 ? job({found: 16}) : job({status: "results_ready", found: 16});
    }
    if (path.endsWith("/publish")) return {...h.context.S, revision: 8,
      search_job: job({revision: 8, status: "results_ready", found: 16})};
    throw new Error("Unexpected API: " + path);
  }});
  h.context.paused = job({status: "paused", found: 16, page: 1});
  h.run("interactiveJob = paused; searchPage = 1");
  await h.run("continueSearch(false, true)");
  assert.deepEqual(calls.map(c => [c.path.split("/").pop(), c.body.page, c.body.sort]),
    [["resume", 1, "discovery"], ["tick", 1, "discovery"], ["tick", 0, "pieces"], ["publish", 0, "pieces"]]);
});

test("between its ticks a running search refuses other actions and keeps the engine", async () => {
  const state = scene([], 7); state.open_ends = [[0, 0], [5, 1]];
  const paths = []; let h, ticks = 0, tried = null;
  h = harness({state, events: true, omit: ["api"], overrides: {redraw() {},
    setTimeout: fn => {
      // The first gap between ticks: a label click on sandbox, then Check layout.
      if (h?.run("jobLoop") && !tried) {
        const box = h.el("unlimited"); box.checked = true;
        tried = Promise.all([box.fire("change", {target: box}), h.run("checkLayout()")]);
      }
      fn(); return 1;
    }}});
  h.context.window.duplotrainApi = async path => {
    paths.push(path);
    if (path.endsWith("/start")) return job();
    if (path.endsWith("/tick")) return ++ticks < 3 ? job({searched: 32 * ticks}) :
      job({status: "results_ready", found: 1, candidates: [candidate(0)]});
    if (path.endsWith("/publish")) return {...h.context.S, revision: 8,
      search_job: job({status: "results_ready", revision: 8, found: 1})};
    throw new Error("Unexpected API: " + path);
  };
  await h.run("startInteractiveSearch(null, null)");
  await tried;
  assert.deepEqual(paths, ["/api/search/start", "/api/search/tick", "/api/search/tick",
    "/api/search/tick", "/api/search/publish"]);
  assert.equal(h.run("interactiveJob.status"), "results_ready");
  assert.equal(h.el("unlimited").checked, false);
  assert.ok(h.notices.some(n => /pause it first/.test(n.text)));
});

test("a tick made stale by another tab's edit says why the search stopped", async () => {
  const state = scene([], 7); state.open_ends = [[0, 0], [5, 1]];
  const h = harness({state, events: true, omit: ["api"], overrides: {setTimeout: fn => { fn(); return 1; }}});
  h.context.window.duplotrainApi = async path => {
    if (path.endsWith("/start")) return job();
    const error = new Error("The layout changed in another window; nothing was applied.");
    error.code = "stale_revision"; error.state = scene([], 9);
    throw error;
  };
  await h.run("startInteractiveSearch(null, null)");
  assert.equal(h.run("interactiveJob"), null);
  assert.equal(h.context.S.revision, 9);
  assert.match(h.notices.at(-1).text, /changed in another window/);
  assert.equal(h.notices.at(-1).kind, "err");
});

test("a failed route tick ends the analysis instead of leaving Pause without a job", async () => {
  let ticks = 0;
  const h = app({api: async path => {
    if (path === "/api/routes/start") return route();
    if (++ticks === 1) return route({runs: 2});
    throw new Error("Worker failed");
  }});
  await h.run('startRouteAnalysis("all")');
  assert.equal(h.run("routeAnalysis"), null);
  assert.equal(h.el("route-pause").hidden, true);
  assert.equal(h.el("route-report").textContent, "");
  assert.match(h.notices.at(-1).text, /Worker failed/);
});

test("Search harder leaves with the paused search a route analysis replaces", async () => {
  const h = app({api: async path => {
    if (path === "/api/routes/start") return route({status: "complete", complete: true});
    throw new Error("Unexpected API: " + path);
  }});
  h.context.paused = job({status: "paused", found: 8});
  h.run("interactiveJob = paused; renderJobControls()");
  assert.equal(h.el("expand-search").hidden, false);
  await h.run('startRouteAnalysis("all")');
  assert.equal(h.el("expand-search").hidden, true);
});

test("publishing a search keeps the train start, switches and trace made on its layout", async () => {
  const piece = (name, x, ports) => ({name, width: 40, lines: [[[x, 0, 0], [x + 128, 0, 0]]],
    mid: [x + 64, 0], stone_marks: [], ports: ports.map((p, i) => ({port: i, name: p, x: x + 128 * i,
      y: 0, deg: 0, open: true, sealed: false}))});
  const state = revision => ({...scene([piece("straight", 0, ["a", "b"]),
    piece("switch", 200, ["stem", "left", "right"])], revision), open_ends: [[0, 0], [1, 2]],
    train_switches: [{placement: 1, default: 1, options: [{port: 1, name: "left"}, {port: 2, name: "right"}]}]});
  let h;
  h = harness({state: state(7), events: true, overrides: {setTimeout: fn => { fn(); return 1; },
    api: async path => {
      if (path === "/api/drive") return {revision: h.context.S.revision, steps: [[1, 0, 2], [0, 1, 0]],
        terminal: null, cycle_start: 0, period: 2, outcome: "endless", reversals: 0,
        visited_drivable: [0, 1], drivable_count: 2, complete: true, unvisited: [], cycle_pieces: [0, 1]};
      if (path === "/api/search/start") return job();
      if (path === "/api/search/tick") return job({status: "results_ready", found: 1});
      if (path === "/api/search/publish") return {...state(8), search_job: job({revision: 8,
        status: "results_ready", found: 1})};
      throw new Error("Unexpected API: " + path);
    }}});
  h.run("redraw()");
  h.el("train-start").value = "[1,1]"; h.el("train-start").fire("change");
  const control = h.el("train-switches").children[0].children[0];
  control.value = "2"; control.fire("change");
  h.el("piece-select").value = "1";
  await h.run("testTrain()");
  await h.run("startInteractiveSearch(null, null)");
  assert.equal(h.context.S.revision, 8);
  assert.equal(h.el("train-start").value, "[1,1]");
  assert.deepEqual(clean(h.run("initialSwitches")), {1: 2});
  assert.equal(h.el("piece-select").value, "1");
  assert.equal(h.run("trainTrace.revision"), 8);
  h.el("train-step").click();
  assert.equal(h.run("trainStep"), 0);
  // The same switch control still accepts a change on the new revision.
  control.value = "1"; control.fire("change");
  assert.deepEqual(clean(h.run("initialSwitches")), {1: 1});
});

test("a paused search reports the pause, never a failure to find", async () => {
  let h, ticks = 0;
  h = app({api: async path => {
    if (path.endsWith("/start")) return job();
    if (path.endsWith("/tick")) { if (++ticks === 1) h.el("pause-search").click(); return job({searched: 64}); }
    if (path.endsWith("/pause")) return job({status: "paused"});
    if (path.endsWith("/publish")) return {...h.context.S, revision: 8, search_job: job({status: "paused", revision: 8})};
    throw new Error("Unexpected API: " + path);
  }});
  await h.run("startInteractiveSearch(null, null)");
  assert.equal(h.notices.at(-1).text, "Search paused. Resume continues it.");
  assert.notEqual(h.notices.at(-1).kind, "err");
});

for (const [status, extra, offered] of [
  ["direct_join", {found: 1, resumable: false, can_harden: false}, []],
  ["exhausted", {found: 3, resumable: false, complete: true}, []],
  ["limited", {found: 3, resumable: false}, ["Search harder"]],
  ["result_cap", {found: 50, resumable: false, can_harden: false}, []],
  ["results_ready", {found: 8}, ["Find more", "Search harder"]],
]) {
  test(`a finished search names only the controls it offers: ${status}`, async () => {
    let h;
    const done = job({status, candidates: [candidate(0)], ...extra});
    h = app({api: async path => {
      if (path.endsWith("/start")) return done;
      if (path.endsWith("/publish")) return {...h.context.S, revision: 8, search_job: {...done, revision: 8}};
      throw new Error("Unexpected API: " + path);
    }});
    await h.run("startInteractiveSearch(null, null)");
    const text = h.notices.at(-1).text;
    assert.match(text, /alternative\(s\) found/);
    for (const [name, id] of [["Find more", "find-more"], ["Search harder", "expand-search"]]) {
      assert.equal(text.includes(name), offered.includes(name), text);
      assert.equal(!h.el(id).hidden, offered.includes(name), id);
    }
  });
}

test("a search pauses with its one Pause, a route analysis with its own", async () => {
  const h = app();
  const pauses = () => ["pause-search", "route-pause"].filter(id => !h.el(id).hidden);
  h.context.running = job({found: 3, candidates: [candidate(0)]});
  h.run("interactiveJob = running; jobLoop = true; renderJobControls()");
  assert.deepEqual(pauses(), ["pause-search"]);
  await h.el("pause-search").click();
  assert.equal(h.run("jobPauseRequested"), true);
  h.run("jobPauseRequested = false; jobLoop = false; renderJobControls()");
  await h.el("pause-search").click();  // a stale click after the search stopped
  assert.equal(h.run("jobPauseRequested"), false);
  h.context.analysis = route();
  h.run("interactiveJob = null; routeAnalysis = analysis; renderJobControls()");
  assert.deepEqual(pauses(), ["route-pause"]);
});

test("Check layout rows still focus their pieces after a search publishes", async () => {
  let h, focused = 0;
  const report = {revision: 7, connector_closed: false, open_ends: [[0, 0]], joint_issues: [],
    overlaps: [[0, 1]], overlap_check_complete: true, missing: [], provisional: [], model_note: "m"};
  h = app({focusPieces: () => { focused++; }, api: async path => {
    if (path === "/api/check") return report;
    if (path.endsWith("/start")) return job();
    if (path.endsWith("/tick")) return job({status: "results_ready", found: 1, candidates: [candidate(0)]});
    if (path.endsWith("/publish"))
      return {...h.context.S, revision: 8, search_job: job({status: "results_ready", found: 1, revision: 8})};
    throw new Error("Unexpected API: " + path);
  }});
  await h.run("checkLayout()");
  await h.run("startInteractiveSearch(null, null)");
  assert.equal(h.context.S.revision, 8);  // publication: a new revision of the same layout
  h.el("diagnostics").children.find(c => c.tag === "button").fire("click");
  assert.equal(focused, 1);
});

test("Best settings for this start waits for a layout to start from", () => {
  const h = app();
  h.run("S.layout.placements = []; S.open_ends = []; navigationRevision = null; renderNavigation()");
  assert.equal(h.el("route-best").disabled, true);
});

test("a job the engine no longer holds withdraws its controls", async () => {
  const h = app({api: async () => { throw new Error("Search expired after 20 minutes of inactivity; start again"); }});
  h.context.paused = job({status: "paused", found: 8});
  h.run("interactiveJob = paused; renderJobControls()");
  await h.el("resume-search").click();
  assert.match(h.notices.at(-1).text, /expired/);
  assert.equal(h.run("interactiveJob"), null);
  assert.deepEqual(["find-more", "resume-search", "expand-search"].filter(id => !h.el(id).hidden), []);
});

for (const [name, code] of [
  ["Close the loop", "startInteractiveSearch(null, null)"],
  ["Find more", "interactiveJob = paused; continueSearch()"],
  ["a route analysis", 'startRouteAnalysis("all")'],
  ["Test train", 'el("train-start").value = "[0,0]"; testTrain()'],
]) {
  test(`${name} refused by another tab's edit says why`, async () => {
    const state = scene([], 7); state.open_ends = [[0, 0], [5, 1]];
    const h = harness({state, events: true, omit: ["api"], overrides: {setTimeout: fn => { fn(); return 1; }}});
    h.run("interactionRevision = 7");
    h.context.window.duplotrainApi = async () => {
      const error = new Error("The session changed in another tab. Your action was not applied.");
      error.code = "stale_revision"; error.state = scene([], 9);
      throw error;
    };
    h.context.paused = job({status: "paused", found: 8});
    await h.run(code);
    assert.equal(h.context.S.revision, 9);
    assert.match(h.notices.at(-1).text, /changed in another tab/);
    assert.equal(h.notices.at(-1).kind, "err");
  });
}

test("hovering a card keeps its ghost while the search ticks on", () => {
  const h = app();
  const ghost = index => ({...candidate(index), preview: {...candidate(index).preview, placements: [{n: index}]}});
  h.context.running = job({found: 2, candidates: [ghost(0), ghost(1)]});
  h.run("interactiveJob = running; renderCandidates()");
  h.el("cands").children[1].fire("pointerenter", {pointerType: "mouse"});
  h.run("interactiveJob = {...running, searched: 64}; renderCandidates()");  // the next tick
  assert.equal(h.run("preview.placements[0].n"), 1);
  h.el("cands").children[1].fire("pointerleave");
  assert.equal(h.run("preview"), null);
});
