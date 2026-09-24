"use strict";
// One DOM and browser stub for the editor's node tests: the complete editor
// source runs in a vm context whose elements record listeners, classes and
// attributes, whose storage, locks and timers are in-memory, and whose api and
// status calls are recorded. Tests pass their own state and overrides; a name
// in `omit` keeps the editor's own definition instead of the stub.
const vm = require("node:vm");
const {loadEditor} = require("./editor-harness.cjs");

function scene(placements = [], revision = 1) {
  return {revision, layout: {placements, closed: false, exactly_closed: false,
    joint_issues: [], size_cm: [20, 20]}, open_ends: [], matable: [], candidates: [],
    can_undo: false, can_redo: false, sets: [], palette: [],
    inventory: {owned: {straight: 17}, remaining: {straight: 17}, unlimited: false},
    stones: {catalog: {}, owned: {stone_stop: 2}, remaining: {stone_stop: 2}},
    snapshot: {format: "duplotrain-session/1", inventory: {straight: 17},
      stones: {stone_stop: 2}, unlimited: false, layout: {format: "duplotrain-layout/1", placements: []}}};
}
function track(line, name = "track") {
  return {name, width: 40, lines: [line], ports: [], mid: line[0], stone_marks: []};
}
function harness({state = scene(), events = false, schedule = false, overrides = {}, omit = []} = {}) {
  const elements = new Map(), calls = [], notices = [], windowEvents = {}, frames = [], intervals = new Map();
  const saved = new Map();
  let created = 0;
  class Element {
    constructor(tag = "div") {
      created++;
      this.tag = tag; this.tagName = tag; this.children = []; this.listeners = {}; this.registered = {};
      this.dataset = {}; this.style = {};
      this.attributes = {}; this._value = ""; this.textContent = ""; this.disabled = false; this.hidden = false;
      this.checked = false;
      const classes = this.classes = new Set();
      this.classList = {
        add: name => classes.add(name), remove: name => classes.delete(name),
        toggle(name, on) { if (on ?? !classes.has(name)) classes.add(name); else classes.delete(name); },
        contains: name => classes.has(name),
      };
      this.clientWidth = 500; this.clientHeight = 500;
    }
    set value(v) { this._value = String(v); }
    get value() { return this._value || (this.tag === "select" ? this.children[0]?.value || "" : ""); }
    append(...children) { this.children.push(...children); }
    replaceChildren(...children) { this.children = children; this._value = ""; }
    setAttribute(k, v) { this.attributes[k] = String(v); }
    // fire() and click() call the latest listener; `registered` keeps every one, so
    // a control bound twice (one click, two actions) stays visible to a test.
    addEventListener(event, action) { (this.registered[event] ??= []).push(action); this.listeners[event] = action; }
    listenerCount(event) { return this.registered[event]?.length ?? 0; }
    fire(event, data = {target: this}) { return this.listeners[event]?.(data); }
    click() { if (!this.disabled) return this.fire("click"); }
    focus() { context.document.activeElement = this; }
    closest() { return null; }
    getBoundingClientRect() { return {left: 0, top: 0}; }
  }
  const el = id => {
    if (!elements.has(id)) elements.set(id, new Element(id.includes("select") || id === "train-start" || id === "project-slots" ? "select" : "div"));
    return elements.get(id);
  };
  const stubs = {
    status: (text, kind) => notices.push({text, kind}),
    api: async (path, body) => { calls.push({path, body}); return state; },
    saveSession() {}, setTimeout() {}, ...(schedule ? {} : {draw() {}}),
  };
  for (const name of omit) delete stubs[name];
  const context = vm.createContext({
    S: state, fitted: true, pickMode: null, armed: null, preview: null, view: {x: 0, y: 0, scale: 1},
    window: {addEventListener(name, fn) { windowEvents[name] = fn; }},
    document: {getElementById: el, createElement: tag => new Element(tag),
      body: new Element("body"), addEventListener() {}},
    location: {pathname: "/test/"}, navigator: {locks: {request: async (_name, action) => action()}},
    localStorage: {get length() { return saved.size; }, key(i) { return [...saved.keys()][i]; },
      getItem(k) { return saved.get(k) ?? null; }, setItem(k, v) { saved.set(k, String(v)); }, removeItem(k) { saved.delete(k); }},
    crypto: {randomUUID: () => `project-${saved.size + 1}`},
    requestAnimationFrame(fn) { frames.push(fn); },
    setInterval(fn) { const id = Symbol(); intervals.set(id, fn); return id; },
    clearInterval(id) { intervals.delete(id); },
    ...stubs, ...overrides,
  });
  loadEditor(context, {events});
  const run = code => vm.runInContext(code, context);
  el("max-pieces").value = 26; el("slop").value = 0; el("reversing").checked = false;
  return {context, run, el, calls, notices, saved, intervals, frames, windowEvents, Element,
    created: () => created};
}

module.exports = {harness, scene, track};
