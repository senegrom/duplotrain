"use strict";
// Load the actual, complete editor source. No HTML or comment-boundary slicing.
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const scripts = ["editor.js", "editor-geometry.js", "editor-projects.js", "editor-train.js"];
const sources = scripts.map(name => [name,
  fs.readFileSync(path.join(__dirname, "../../src/duplotrain/static", name), "utf8")]);
const stateNames = new Set(["S", "armed", "armedStone", "preview", "pickMode", "view", "fitted",
  "deleting", "selectedCandidate", "solving", "lastSolve", "recoveryAttempted", "autosaveReady", "apiBusy"]);

function loadEditor(context, {events = false} = {}) {
  const overrides = {...context};
  const elements = new Map();
  const element = id => {
    if (!elements.has(id)) elements.set(id, {
      addEventListener() {}, setAttribute() {}, classList: {toggle() {}, add() {}, remove() {}},
      dataset: {}, style: {},
    });
    return elements.get(id);
  };
  context.location ??= {pathname: "/"};
  context.window ??= {};
  context.window.addEventListener ??= () => {};
  context.document ??= {};
  context.document.addEventListener ??= () => {};
  context.document.getElementById ??= overrides.el || element;
  context.navigator ??= {};
  for (const [filename, source] of sources) vm.runInContext(source, context, {filename});
  for (const [name, value] of Object.entries(overrides)) {
    if (stateNames.has(name)) {
      context.__injected = value;
      vm.runInContext(`${name} = __injected`, context);
      // Allow the small test harnesses to inspect/replace the real lexical state.
      Object.defineProperty(context, name, {
        configurable: true,
        get() { return vm.runInContext(name, context); },
        set(next) {
          context.__injected = next;
          vm.runInContext(`${name} = __injected`, context);
          delete context.__injected;
        },
      });
    } else {
      context[name] = value;
    }
  }
  delete context.__injected;
  if (events) {
    // Minimal event-only elements: production startup (canvas sizing/API loads)
    // is still exercised by the real Chromium/WebKit tests.
    const get = context.document.getElementById;
    context.document.getElementById = id => {
      const target = get(id);
      target.addEventListener ??= () => {};
      return target;
    };
    context.__canvas = context.document.getElementById("canvas");
    vm.runInContext('canvas = __canvas; bindEditorEvents()', context);
    delete context.__canvas;
  }
}

module.exports = {loadEditor};
