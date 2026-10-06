"use strict";
// One engine job at a time. Tick responses are read-only, validated previews;
// only publish changes candidate revisions, and only Apply changes the layout.
let interactiveJob = null, routeAnalysis = null, jobSequence = 0;
let jobPauseRequested = false, jobLoop = false, searchPage = 0;
let exclusions = new Set(), exclusionKey = null;
// Between ticks, a turn of the browser's event loop. A hidden tab clamps timers to
// one a second, and the engine's reply has returned to the event loop already.
const nextJobTurn = () => document.hidden ? Promise.resolve()
  : new Promise(resolve => setTimeout(resolve, 0));

function visibleCandidates() {
  return interactiveJob?.revision === S?.revision ? interactiveJob.candidates : S?.candidates || [];
}
// Publication sends the page shown, not every suggestion (page_only). That page
// stays the session's when the job is gone; only a page of the published
// revision is kept, and its array is shared, never copied.
function retainPublishedPage() {
  if (interactiveJob?.revision === S?.revision &&
      S?.search_job?.job_id === interactiveJob.job_id && S.search_job.revision === S.revision) {
    S.candidates = interactiveJob.candidates;
    S.search_job = interactiveJob;
  }
}
// Once the job is gone, the engine still pages and ranks what it published.
const publishedPages = () =>
  !interactiveJob && S?.search_job?.revision === S?.revision ? S.search_job : null;
// The cards follow the Rank select: a ranking chosen while another request
// ran, such as a search's final publication, is asked for once it is done.
function followRanking() {
  const pages = interactiveJob?.revision === S?.revision ? interactiveJob : publishedPages();
  if (!pages) return;
  if (pages.sort !== jobView().sort) return searchPageTo(0);
  searchPage = pages.page;  // a ranking changed and changed back: the page shown stays
}
function clearInteractiveState() {
  jobSequence++; interactiveJob = routeAnalysis = null;
  jobPauseRequested = true; jobLoop = false; refreshBusy();
  el("route-report").textContent = "";
  renderJobControls();
}
function discardInteractiveJob() {
  if ((interactiveJob && interactiveJob.revision !== S?.revision) ||
      (routeAnalysis && routeAnalysis.revision !== S?.revision)) clearInteractiveState();
}
function rectangleInput(text) {
  // The placeholder writes "−" (U+2212), as typeset text may.
  const values = text.replaceAll("\u2212", "-").split(",").map(s => s.trim()).map(s => s === "" ? NaN : Number(s) * 10);
  if (values.length !== 4 || values.some(v => !Number.isFinite(v) || Math.abs(v) > 1e7) ||
      values[0] >= values[2] || values[1] >= values[3])
    throw new Error("Rectangles use xmin, ymin, xmax, ymax in cm, with positive area.");
  return values;
}
function readSearchOptions() {
  const room = (el("room-bounds").value || "").trim();
  const keep = (el("keep-out").value || "").trim();
  const keep_out = keep ? keep.split(/\n/).filter(s => s.trim()).map(rectangleInput) : [];
  if (keep_out.length > 32) throw new Error("Use at most 32 keep-out rectangles.");
  return {sort: el("candidate-sort").value || "discovery", exclude: [...exclusions].sort(),
    room: room ? rectangleInput(room) : null, keep_out};
}
function restoreSearchOptions(options) {
  exclusions = new Set(options?.exclude || []); exclusionKey = null;
  el("candidate-sort").value = options?.sort || "discovery";
  const text = rect => rect.map(v => v / 10).join(", ");
  el("room-bounds").value = options?.room ? text(options.room) : "";
  el("keep-out").value = (options?.keep_out || []).map(text).join("\n");
  renderSearchOptions();
}
function renderSearchOptions() {
  const box = el("search-exclusions");
  if (!S) return;
  const key = JSON.stringify([(S.palette || []).map(p => [p.id, p.name]), [...exclusions].sort()]);
  if (key === exclusionKey) return;
  exclusionKey = key; box.replaceChildren();
  for (const piece of S.palette || []) {
    const label = document.createElement("label"), input = document.createElement("input");
    input.type = "checkbox"; input.checked = exclusions.has(piece.id);
    input.setAttribute("aria-label", `Exclude ${piece.name} from search`);
    input.addEventListener("change", () => {
      if (input.checked) exclusions.add(piece.id); else exclusions.delete(piece.id);
      exclusionKey = null; updateProjectStatus();
      status("Piece exclusions apply to the next new search; owned inventory is unchanged.");
    });
    label.append(input, ` ${piece.name}`); box.append(label);
  }
}
// What a search can still do; its controls and its final message both follow the engine.
function searchOutcome(job) {
  if (job.status === "paused")
    return `Search paused${job.found ? ` with ${job.found} alternative(s) — preview and apply` : ""}. Resume continues it.`;
  // A reason also explains what was found: closures set aside, walks cut short.
  const found = `${job.found} alternative(s) found — preview and apply.`;
  const summary = job.found ? (job.reason ? `${found} ${job.reason}` : found) :
    job.reason || (job.complete ? "No completion fits the remaining inventory under these settings." :
      "No completion found within these limits. A closure may still exist.");
  const next = [job.resumable && "Find more resumes this search",
                job.can_harden && "Search harder raises its limits"].filter(Boolean);
  return next.length ? `${summary} ${next.join("; ")}.` : summary;
}
function renderJobControls() {
  const show = (id, visible, disabled = false) => {
    const target = el(id); target.hidden = !visible; target.disabled = disabled;
  };
  const job = interactiveJob, active = !!job && job.revision === S?.revision;
  const pages = active ? job : publishedPages();
  show("find-more", active && job.resumable, jobLoop);
  show("resume-search", active && job.status === "paused", jobLoop);
  if (pages) {
    const total = Math.max(1, Math.ceil(pages.found / 8));
    el("candidate-page").textContent = `Page ${pages.page + 1} / ${total}`;
    show("candidate-prev", total > 1, jobLoop || pages.page === 0);
    show("candidate-next", total > 1, jobLoop || pages.page + 1 >= total);
  } else {
    for (const id of ["candidate-prev", "candidate-next"]) show(id, false);
    el("candidate-page").textContent = "";
  }
  if (active) {
    show("expand-search", job.can_harden, jobLoop);
    el("search-report").textContent =
      `${job.stage}: ${job.searched.toLocaleString()} search nodes; ${job.found} distinct alternative(s). ` +
      `${job.status.replaceAll("_", " ")}. Sorted best among found only; no global optimum guaranteed. ` +
      "Constraints shown belong to this search; changed controls apply to a new search.";
  } else {
    show("expand-search", false);
    el("search-report").textContent = "";
  }
  if (S) show("close-all", true, jobLoop || (S.open_ends?.length ?? 0) < 2);
  // A route analysis pauses with its own button.
  show("pause-search", jobLoop && !routeAnalysis);
  show("route-pause", !!routeAnalysis && routeAnalysis.status === "running");
  show("route-resume", !!routeAnalysis && routeAnalysis.status === "paused", jobLoop);
  show("route-witness", !!routeAnalysis?.best, jobLoop);
  show("route-counterexample", !!routeAnalysis?.counterexample, jobLoop);
}
function jobCurrent(sequence, response) {
  return sequence === jobSequence && response?.revision === S?.revision;
}
// A refused request to a running job. A stale revision was adopted, and the job
// dropped, on the way; any other refusal means the engine no longer holds the job.
function jobRequestFailed(error, sequence, drop) {
  if (error.code !== "stale_revision") {
    if (sequence !== jobSequence) return;
    drop(); renderJobControls(); renderCandidates();
  }
  status(error.message, "err");
}
// The ranking is presentation: every request of a search carries the chosen one.
const jobView = () => ({page: searchPage, sort: el("candidate-sort").value || "discovery"});
async function publishSearch(sequence) {
  if (!interactiveJob || sequence !== jobSequence) return;
  const chosenIndex = (interactiveJob.candidates || []).find(c =>
    `${c.revision}:${c.index}` === selectedCandidate)?.index;
  const next = await api("/api/search/publish", {job_id: interactiveJob.job_id,
    revision: interactiveJob.revision, page_only: true, ...jobView()}, true);
  if (sequence !== jobSequence) return;
  const before = S.revision;
  S = next; interactiveJob = next.search_job;
  retainPublishedPage();
  // Publication changes candidate indices' revision, not the immutable problem
  // or its layout: picks, selectors and a train trace made on it stay valid.
  interactionRevision = S.revision;
  if (navigationRevision === before) navigationRevision = S.revision;
  if (trainTrace?.revision === before) trainTrace.revision = S.revision;
  if (diagnosticsRevision === before) diagnosticsRevision = S.revision;
  selectedCandidate = chosenIndex === undefined ? null : `${S.revision}:${chosenIndex}`;
  redraw();
}
async function driveSearchTicks(sequence) {
  let finalMessage = null, failed = false;
  // A job ends an unfinished end pick: taps wait while it runs, and publishing drops the pick.
  jobLoop = true; jobPauseRequested = false; pickMode = null;
  refreshBusy(); renderJobControls(); refreshStatus(); draw();
  try {
    while (sequence === jobSequence && interactiveJob?.status === "running") {
      if (jobPauseRequested) {
        const paused = await api("/api/search/pause", {job_id: interactiveJob.job_id,
          revision: interactiveJob.revision, ...jobView()}, true);
        if (!jobCurrent(sequence, paused)) return;
        interactiveJob = paused; break;
      }
      const next = await api("/api/search/tick", {job_id: interactiveJob.job_id,
        revision: interactiveJob.revision, ...jobView()}, true);
      if (!jobCurrent(sequence, next)) return;
      interactiveJob = next;
      renderCandidates(); renderJobControls(); draw();
      // Return to the browser event loop between engine checkpoints. A pause
      // never requires worker termination, so undo/history and candidates survive.
      if (next.status === "running") await nextJobTurn();
    }
    if (sequence === jobSequence && interactiveJob) {
      await publishSearch(sequence);
      const job = interactiveJob;
      failed = !job.found && job.status !== "paused";
      finalMessage = searchOutcome(job);
    }
  } catch (error) {
    if (sequence === jobSequence) {
      interactiveJob = null; selectedCandidate = null; preview = null;
      finalMessage = error.message; failed = true;
    } else if (error.code === "stale_revision") {
      // Another tab changed the layout: adopting it discarded this job already.
      status(error.message, "err");
    }
  } finally {
    if (sequence === jobSequence) {
      jobLoop = false; refreshBusy(); renderJobControls(); refreshStatus(); renderCandidates();
      if (finalMessage) status(finalMessage, failed ? "err" : "");
    }
  }
  if (sequence === jobSequence) await followRanking();
}
async function startInteractiveSearch(grow, close, allGaps = false) {
  if (!S || jobLoop || apiBusy) return;
  const sequence = ++jobSequence; jobPauseRequested = false;
  try {
    // Close all gaps plans exact, non-reversing joins only: slop and reversing
    // are settings of Close the loop.
    const body = {grow, close, max_pieces: Number(el("max-pieces").value),
      slop: allGaps ? 0 : Number(el("slop").value),
      reversing: !allGaps && el("reversing").checked, all_gaps: allGaps, options: readSearchOptions()};
    selectTool();
    const response = await api("/api/search/start", body);
    if (!jobCurrent(sequence, response)) return;
    interactiveJob = response; routeAnalysis = null; searchPage = 0;
    selectedCandidate = null; preview = null;
    // The engine withdrew the previous suggestions; only this job's can follow.
    S.candidates = []; delete S.search_job;
    await driveSearchTicks(sequence);
  } catch (error) {
    // A refused start leaves the engine's previous job as it was.
    if (sequence === jobSequence || error.code === "stale_revision") status(error.message, "err");
  }
}
async function continueSearch(harder = false, resume = false) {
  if (!interactiveJob || jobLoop || apiBusy || interactiveJob.revision !== S?.revision) return;
  const sequence = ++jobSequence, {sort} = jobView();
  try {
    const response = await api(resume ? "/api/search/resume" : "/api/search/continue",
      {job_id: interactiveJob.job_id, revision: interactiveJob.revision, harder, ...jobView()});
    if (!jobCurrent(sequence, response)) return;
    interactiveJob = response;
    // A ranking chosen while the request ran applies from the first page.
    if (jobView().sort !== sort) searchPage = 0;
    el("max-pieces").value = response.max_pieces;
    await driveSearchTicks(sequence);
  } catch (error) { jobRequestFailed(error, sequence, () => { interactiveJob = null; }); }
}
async function searchPageTo(page) {
  const pages = interactiveJob || publishedPages();
  if (!pages || jobLoop || apiBusy) return;
  const sequence = jobSequence, {sort} = jobView();
  try {
    const response = await api("/api/search/page", {job_id: pages.job_id,
      revision: pages.revision, ...jobView(), page});
    if (!jobCurrent(sequence, response)) return;
    searchPage = response.page;
    // A job the engine no longer holds is answered from what it published.
    if (response.status === "published") {
      interactiveJob = null; S.search_job = response; S.candidates = response.candidates;
    } else { interactiveJob = response; retainPublishedPage(); }
    renderCandidates(); renderJobControls(); draw();
  } catch (error) {
    jobRequestFailed(error, sequence, () => {
      if (interactiveJob) interactiveJob = null; else delete S.search_job;
    });
    return;
  }
  // The Rank select changed while the request ran, and that change was dropped.
  if (jobView().sort !== sort) await searchPageTo(0);
}
function requestJobPause() {
  jobPauseRequested = true;
  status("Pausing at the next engine checkpoint; results and undo history will be retained.");
}
function showRouteAnalysis() {
  const r = routeAnalysis, out = el("route-report");
  if (!r || r.revision !== S?.revision) return;
  out.replaceChildren();
  const line = text => { const p = document.createElement("p"); p.textContent = text; out.append(p); };
  line(`${r.runs.toLocaleString()} / ${r.required_runs} runs checked (${r.scope === "all" ? "all starts" : "selected start"}, all initial switch settings). ${r.status}.`);
  if (r.best) line(`Best ${r.complete ? "in the complete requested model space" : "among completed runs so far"}: ` +
    `${r.best.visited} / ${r.total_drivable} pieces ever visited; ${r.best.cycle_visited} visited in the repeating cycle.`);
  if (r.classification) {
    const c = r.classification;
    line(`Every checked start/setting loops: ${c.looping ? "yes" : "no"}; every run covers all track: ${c.completely_looping ? "yes" : "no"}; ` +
      `every repeating cycle traverses all track both ways: ${c.perfectly_looping ? "yes" : "no"}.`);
  } else line(`Analysis incomplete. No universal verdict or optimality claim; ${r.step_limited_runs} run(s) reached the step limit.`);
  line("Train-model result only, not a physical-track guarantee. Best route does not modify your layout.");
  renderJobControls();
}
async function driveRouteTicks(sequence) {
  let failure = null;
  jobLoop = true; jobPauseRequested = false; pickMode = null;
  refreshBusy(); refreshStatus(); renderJobControls(); draw();
  try {
    while (sequence === jobSequence && routeAnalysis?.status === "running") {
      const response = await api(jobPauseRequested ? "/api/routes/pause" : "/api/routes/tick",
        {job_id: routeAnalysis.job_id, revision: routeAnalysis.revision}, true);
      if (!jobCurrent(sequence, response)) return;
      routeAnalysis = response; showRouteAnalysis();
      if (response.status === "running") await nextJobTurn();
    }
  } catch (error) {
    if (sequence === jobSequence) {
      // A failed tick ends the analysis, as it ends a search.
      failure = error.message; routeAnalysis = null;
      el("route-report").textContent = "";
    } else if (error.code === "stale_revision") status(error.message, "err");
  } finally { if (sequence === jobSequence) {
    jobLoop = false; refreshBusy(); renderJobControls(); refreshStatus();
    if (failure) status(failure, "err");
  } }
  if (sequence === jobSequence) await followRanking();
}
async function startRouteAnalysis(scope = "all") {
  if (!S || jobLoop || apiBusy) return;
  const sequence = ++jobSequence;
  try {
    const response = await api("/api/routes/start", {scope,
      ...(scope === "selected" ? {start: JSON.parse(el("train-start").value)} : {}),
      goal: el("route-goal").value || "visited", max_runs: Number(el("route-max-runs").value || 20000)});
    if (!jobCurrent(sequence, response)) return;
    retainPublishedPage();
    interactiveJob = null; routeAnalysis = response;
    await driveRouteTicks(sequence);
  } catch (error) {
    if (sequence === jobSequence || error.code === "stale_revision") status(error.message, "err");
  }
}
async function useRouteWitness(counterexample = false) {
  if (jobLoop || apiBusy || routeAnalysis?.revision !== S?.revision) return;
  const witness = counterexample ? routeAnalysis.counterexample : routeAnalysis.best;
  if (!witness) return;
  el("train-start").value = JSON.stringify(witness.start);
  for (const [id, port] of Object.entries(witness.switch_states)) {
    initialSwitches[id] = port;
    if (switchControls.has(Number(id))) switchControls.get(Number(id)).value = port;
  }
  await testTrain();
}
function bindSearchEvents() {
  on("find-more", () => continueSearch());
  on("expand-search", () => continueSearch(true));
  on("resume-search", () => continueSearch(false, true));
  on("pause-search", () => { if (jobLoop) requestJobPause(); });
  on("close-all", () => startInteractiveSearch(null, null, true));
  on("candidate-prev", () => searchPageTo(Math.max(0, searchPage - 1)));
  on("candidate-next", () => searchPageTo(searchPage + 1));
  el("candidate-sort").addEventListener("change", () => {
    updateProjectStatus();
    // A running search re-ranks at its next checkpoint, from the first page. A change
    // made while a search, a route analysis, Test train or Check layout runs is asked
    // for when it ends (followRanking); one made during any other request is dropped.
    if (jobLoop) searchPage = 0; else searchPageTo(0);
  });
  for (const id of ["room-bounds", "keep-out"]) el(id).addEventListener("input", updateProjectStatus);
  const excludeKinds = kind => {
    for (const p of S?.palette || []) {
      if (kind === "bridges" ? p.category === "bridge" : p.junction) exclusions.add(p.id);
    }
    exclusionKey = null; renderSearchOptions(); updateProjectStatus();
  };
  on("avoid-junctions", () => excludeKinds("junctions"));
  on("avoid-bridges", () => excludeKinds("bridges"));
  on("reset-exclusions", () => { exclusions.clear(); exclusionKey = null; renderSearchOptions(); updateProjectStatus(); });
  on("route-best", () => startRouteAnalysis("selected"));
  on("route-all", () => startRouteAnalysis("all"));
  on("route-pause", requestJobPause);
  on("route-resume", async () => {
    if (jobLoop || apiBusy || !routeAnalysis) return;
    const sequence = ++jobSequence;
    try {
      const response = await api("/api/routes/resume", {job_id: routeAnalysis.job_id, revision: routeAnalysis.revision});
      if (!jobCurrent(sequence, response)) return;
      routeAnalysis = response; await driveRouteTicks(sequence);
    } catch (error) {
      jobRequestFailed(error, sequence, () => {
        routeAnalysis = null;
        el("route-report").textContent = "";
      });
    }
  });
  on("route-witness", () => useRouteWitness());
  on("route-counterexample", () => useRouteWitness(true));
}
