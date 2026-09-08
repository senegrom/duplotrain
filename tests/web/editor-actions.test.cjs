"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const html = fs.readFileSync(path.join(__dirname, "../../src/duplotrain/static/editor.html"), "utf8");
const source = html.split("<script>")[1].split("// ---------- Checkpoint persistence ----------")[0] +
  html.slice(html.indexOf("// Retain controls"), html.indexOf("function redraw()")) +
  html.slice(html.indexOf('el("export").addEventListener'), html.indexOf('el("solve").addEventListener')) +
  html.slice(html.indexOf('el("unlimited").addEventListener'), html.indexOf("\nresize();"));

function state(revision, piece = "straight", unlimited = false) {
  const layout = {format: "duplotrain-layout/1", placements: [{piece}], links: [], accessories: []};
  return {revision, snapshot: {layout}, layout: {...layout, joint_issues: []},
    palette: [], inventory: {unlimited}};
}

function editor(transport = "http") {
  const elements = new Map(), calls = [], downloads = [], messages = [];
  const el = id => {
    if (!elements.has(id)) elements.set(id, {
      listeners: {}, value: "", checked: false, classList: {toggle() {}},
      setAttribute() {}, replaceChildren() {},
      addEventListener(event, callback) { this.listeners[event] = callback; },
      fire(event) { return this.listeners[event]({target: this}); },
    });
    return elements.get(id);
  };
  let current = state(7);
  const dispatch = (url, body) => {
    calls.push({url, body});
    if (url === "/api/export") return current.snapshot.layout;
    if (body.revision !== current.revision) throw Object.assign(new Error("Your action was not applied"), {
      code: "stale_revision", state: current,
    });
    current = url === "/api/unlimited" ? state(current.revision + 1, "straight", body.on) :
      state(current.revision + 1, body.data.placements[0].piece);
    return current;
  };
  const context = vm.createContext({
    window: {}, el, Blob, setTimeout() {}, status: message => messages.push(message),
    document: {body: {classList: {add() {}, remove() {}}}, getElementById: el,
      createElement: () => ({click() {}})},
    URL: {createObjectURL(blob) { downloads.push(blob); return "blob:layout"; }, revokeObjectURL() {}},
    redraw: () => vm.runInContext("renderPalette()", context),
    fetch: async (url, options) => {
      try {
        const data = dispatch(url, options.body && JSON.parse(options.body));
        return {ok: true, json: async () => data};
      } catch (error) {
        return {ok: false, json: async () => ({...error, error: error.message})};
      }
    },
  });
  if (transport === "worker") context.window.duplotrainApi = async (url, body) => dispatch(url, body);
  vm.runInContext(source, context);
  context.initial = current;
  vm.runInContext("S = initial; renderPalette();", context);
  return {context, el, calls, downloads, messages,
    server: value => { current = value; },
    run: code => vm.runInContext(code, context),
    import(file) { el("importfile").files = [file]; return el("importfile").fire("change"); },
  };
}

function file(piece) {
  const {promise, resolve, reject} = Promise.withResolvers();
  return {name: piece + ".json", size: 100, text: () => promise,
    finish: () => resolve(JSON.stringify(state(0, piece).snapshot.layout)), resolve, reject};
}

for (const transport of ["http", "worker"]) {
  test(`${transport} export preserves the displayed layout when another tab changes the engine`, async () => {
    const e = editor(transport);
    const displayed = JSON.parse(e.run("JSON.stringify(S.snapshot.layout)"));
    e.server(state(8, "curve"));
    await e.el("export").fire("click");
    assert.equal(e.downloads.length, 1);
    assert.deepEqual(JSON.parse(await e.downloads[0].text()), displayed);
    assert.equal(e.calls.length, 0);
  });

  test(`${transport} a slower earlier import cannot replace the latest file selection`, async () => {
    const e = editor(transport), first = file("straight"), latest = file("curve");
    const pending = e.import(first), chosen = e.import(latest);
    latest.finish(); await chosen;
    first.finish(); await pending;
    assert.equal(e.run("S.layout.placements[0].piece"), "curve");
    assert.equal(e.calls.length, 1);
    assert.equal(e.calls[0].body.revision, 7);
  });

  for (const location of ["this tab", "another tab"]) {
    test(`${transport} a pending import cannot overwrite edits in ${location}`, async () => {
      const e = editor(transport), incoming = file("curve"), pending = e.import(incoming);
      e.server(state(8, "switch"));
      if (location === "this tab") e.run('S.revision = 8; S.layout.placements = [{piece: "switch"}];');
      incoming.finish(); await pending;
      assert.equal(e.calls[0].body.revision, 7);
      assert.equal(e.run("S.layout.placements[0].piece"), "switch");
      assert.equal(e.run("S.revision"), 8);
      assert.match(e.messages.at(-1), /not applied/);
    });
  }

  for (const unlimited of [false, true]) {
    test(`${transport} sandbox checkbox matches refreshed state (${unlimited}) after a conflict`, async () => {
      const e = editor(transport);
      e.server(state(8, "straight", unlimited));
      e.el("unlimited").checked = true;
      await e.el("unlimited").fire("change");
      assert.equal(e.el("unlimited").checked, unlimited);
      assert.equal(e.run("S.inventory.unlimited"), unlimited);
      assert.match(e.messages.at(-1), /not applied/);
    });
  }
}

test("export still works when the backend is unavailable", async () => {
  const e = editor();
  e.context.fetch = async () => { throw new Error("offline"); };
  await e.el("export").fire("click");
  assert.equal(e.downloads.length, 1);
  assert.equal(JSON.parse(await e.downloads[0].text()).placements[0].piece, "straight");
});

test("export before state loads reports an error without downloading undefined", async () => {
  const e = editor(); e.run("S = null");
  await e.el("export").fire("click");
  assert.equal(e.downloads.length, 0);
  assert.match(e.messages.at(-1), /loading/i);
});

for (const failure of ["invalid JSON", "read error"]) {
  test(`a superseded import's ${failure} cannot replace the latest status`, async () => {
    const e = editor(), first = file("straight"), latest = file("curve");
    const pending = e.import(first), chosen = e.import(latest);
    latest.finish(); await chosen;
    const message = e.messages.at(-1);
    if (failure === "read error") first.reject(new Error("unreadable"));
    else first.resolve("{");
    await pending;
    assert.equal(e.messages.at(-1), message);
  });
}

for (const invalid of ["oversize", "invalid JSON"]) {
  test(`selecting an ${invalid} file also cancels an older pending import`, async () => {
    const e = editor(), first = file("curve"), pending = e.import(first);
    await e.import({size: invalid === "oversize" ? 3 * 1024 * 1024 : 1, text: async () => "{"});
    const message = e.messages.at(-1);
    first.finish(); await pending;
    assert.equal(e.calls.length, 0);
    assert.equal(e.run("S.revision"), 7);
    assert.equal(e.messages.at(-1), message);
  });
}

test("sandbox checkbox returns to the viewed value after a network failure", async () => {
  const e = editor();
  e.context.fetch = async () => { throw new Error("offline"); };
  e.el("unlimited").checked = true;
  await e.el("unlimited").fire("change");
  assert.equal(e.el("unlimited").checked, false);
  assert.equal(e.run("S.inventory.unlimited"), false);
  assert.equal(e.messages.at(-1), "offline");
});
