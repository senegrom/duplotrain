"use strict";
const {test} = require("node:test"), assert = require("node:assert/strict");
const fs = require("node:fs"), path = require("node:path"), vm = require("node:vm");
const source = fs.readFileSync(path.join(__dirname, "../../src/duplotrain/static/editor-search.js"), "utf8");
function render(property, outcome="endless", revision=1) {
  const lines = [], out = {replaceChildren() { lines.length=0; }, append(p) {lines.push(p.textContent);} };
  const context = vm.createContext({S:{revision:1}, document:{createElement:()=>({})},
    el:id=>id==="route-report"?out:null});
  vm.runInContext(source, context);
  context.report = {revision, runs:2, required_runs:"10", status:"paused", scope:"all",
    complete:false, step_limited_runs:0, counterexample_property:property,
    counterexample: property ? {outcome} : null};
  vm.runInContext("renderJobControls=()=>{}; routeAnalysis=report; showRouteAnalysis()", context);
  return lines.join("\n");
}
for (const [property, description] of [
  ["looping", "every start/setting loops endlessly"],
  ["completely", "every run visits all drivable track"],
  ["perfectly", "every repeating cycle traverses all drivable track both ways"]
]) test(`route witness explains failure of ${property} without a universal verdict`, () => {
  const text=render(property, property==="looping"?"derailed":"endless");
  assert.ok(text.includes("Counterexample disproves: " + description));
  assert.match(text,/Analysis incomplete\. No universal verdict/);
  assert.ok(text.includes("This run is " + (property==="looping"?"derailed":"endless")));
});
test("absent witness is not described as a failed property",()=>{
  assert.doesNotMatch(render(null),/Counterexample disproves/);
});
test("stale route responses cannot render a witness",()=>{
  assert.equal(render("looping","derailed",0),"");
});
