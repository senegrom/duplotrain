"use strict";
// Presentation of one bounded engine trace. This is not a second drive model or
// API state store: revision checks use the editor.js snapshot before adoption.
let trainTrace = null, trainStep = -1, trainTimer = null;
let trainConfigSequence = 0, initialSwitches = {};
const switchControls = new Map();

function invalidateTrain() {
  closeOverlapPicker();
  stopTrain(); trainTrace = null; trainStep = -1; trainConfigSequence++;
  for (const id of ["train-play", "train-step", "train-unvisited", "train-cycle"])
    if (el(id)) el(id).disabled = true;
  for (const id of ["train-unvisited", "train-cycle"]) if (el(id)) el(id).checked = false;
  if (el("train-report")) el("train-report").textContent = "";
}
function renderSwitches() {
  const box = el("train-switches");
  if (!box?.replaceChildren) return;
  box.replaceChildren(); initialSwitches = {}; switchControls.clear();
  for (const item of S.train_switches || []) {
    initialSwitches[item.placement] = item.default;
    const label = document.createElement("label"), select = document.createElement("select");
    const name = `Initial switch #${item.placement + 1}`;
    label.textContent = name + " "; select.setAttribute("aria-label", name);
    for (const choice of item.options) {
      const option = document.createElement("option"); option.value = choice.port;
      option.textContent = choice.name; select.append(option);
    }
    select.value = item.default; switchControls.set(item.placement, select);
    select.addEventListener("change", () => {
      if (navigationRevision !== S?.revision) return; // built for another layout
      const value = Number(select.value);
      if (!item.options.some(o => o.port === value)) return;
      initialSwitches[item.placement] = value; invalidateTrain(); draw();
    });
    label.append(select); box.append(label);
  }
}
async function testTrain() {
  invalidateTrain();
  const sequence = trainConfigSequence;
  try {
    const start = JSON.parse(el("train-start").value);
    const trace = await api("/api/drive", {start, max_steps: 10000, switch_states: {...initialSwitches}});
    if (sequence !== trainConfigSequence || trace.revision !== S.revision) return;
    trainTrace = trace; trainStep = -1; showTrainStep(); draw();
  } catch (error) { if (sequence === trainConfigSequence) status(error.message, "err"); }
}
function traceLength(trace = trainTrace) { return trace ? trace.steps.length + (trace.terminal ? 1 : 0) : 0; }
function showTrainStep() {
  if (!trainTrace || trainTrace.revision !== S?.revision) { stopTrain(); return; }
  const t = trainTrace, step = t.steps[trainStep];
  const terminal = trainStep === t.steps.length ? t.terminal : null;
  const count = t.visited_drivable?.length ?? t.visited?.length ?? 0;
  const total = t.drivable_count ?? S.layout.placements.length;
  const reason = {stop_stone: "stop stone", buffer: "buffer", open_end: "open end", dead_route: "no onward route"};
  el("train-report").textContent = t.outcome === "limit" ? `${t.limit || 10000}-step limit reached; no verdict or coverage claim made.` :
    `Model result from this start: ${t.outcome}. ${count} / ${total} drivable pieces visited; ${t.reversals} reversal(s)` +
    `${t.period === null ? "" : `; cycle ${t.period} steps`}. Selected initial switches; not a claim about every start.` +
    (step ? ` Step ${trainStep + 1}/${t.steps.length}: #${step[0] + 1}, port ${step[1]} → ${step[2]}.` : "") +
    (terminal ? ` Final event: #${terminal.placement + 1}, entered port ${terminal.entry}, ` +
      `${terminal.at_port === null ? "midpoint" : `at port ${terminal.at_port}`} — ${reason[terminal.reason] || terminal.reason}.` : "");
  const available = traceLength(t) > 0;
  el("train-step").disabled = !available || (t.cycle_start === null && trainStep + 1 >= traceLength(t));
  el("train-play").disabled = !available;
  el("train-unvisited").disabled = !t.complete || !t.unvisited?.length;
  el("train-cycle").disabled = !t.complete || !t.cycle_pieces?.length;
  draw();
}
function advanceTrain() {
  if (!trainTrace || trainTrace.revision !== S?.revision || !traceLength()) { stopTrain(); return; }
  if (trainStep + 1 >= traceLength()) {
    if (trainTrace.cycle_start !== null) trainStep = trainTrace.cycle_start;
    else { stopTrain(); return; }
  } else trainStep++;
  if (trainTrace.cycle_start === null && trainStep + 1 >= traceLength()) stopTrain();
  showTrainStep();
}

function stopTrain() {
  if (trainTimer !== null) clearInterval(trainTimer);
  trainTimer = null;
}
