"use strict";
// Portable projects and local backup management. The exact API snapshot remains
// owned by editor.js; project baselines and dialogs have a separate lifetime from
// autosave, whose cross-tab safeguards remain in the main editor source.
const PROJECT_FORMAT = "duplotrain-project/1";
const PROJECT_PREFIX = PROJECT_FORMAT + ":" + location.pathname + ":";
let projectBaseline = null, projectBaselineSlot = null, projectManagement = null;
const snapshotKeyCache = new WeakMap();
let projectRows = new Map();


function downloadJSON(data, filename) {
  const blob = new Blob([JSON.stringify(data, null, 2)], {type: "application/json"});
  const url = URL.createObjectURL(blob), anchor = document.createElement("a");
  anchor.href = url; anchor.download = filename; anchor.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
function projectContentKey(data) {
  // Snapshots are immutable API responses. Cache their large serialization;
  // panning/hover frames only serialize the small presentation fields.
  let snapshot = snapshotKeyCache.get(data.session);
  if (snapshot === undefined) { snapshot = JSON.stringify(data.session); snapshotKeyCache.set(data.session, snapshot); }
  const p = data.preferences;
  return {snapshot, settings: JSON.stringify([data.name, p.view.x, p.view.y, p.view.scale,
    p.search.max_pieces, p.search.slop, p.search.reversing, p.search.options || null])};
}
function markProjectSaved(data, slot = null) {
  projectBaseline = projectContentKey(data); projectBaselineSlot = slot;
  updateProjectStatus();
}
function updateProjectStatus() {
  const notice = el("project-status");
  if (!notice) return;
  let message;
  try {
    if (!S?.snapshot) message = "No project loaded.";
    else if (projectBaseline === null) message = "No project copy saved/opened in this tab. Autosave is separate.";
    else {
      const current = projectContentKey(projectSnapshot());
      message = current.snapshot === projectBaseline.snapshot && current.settings === projectBaseline.settings ?
        "Unchanged since last project save/open. Autosave is separate." :
        "Changed since last project save/open — save a new copy. Autosave is separate.";
    }
  } catch (_) { message = "Unsaved project settings are invalid; correct them before saving."; }
  if (notice.textContent !== message) notice.textContent = message;
}
function projectData(strict = false) {
  // Unsaved constraint text may be invalid: a baseline records it as null, a save refuses it.
  let options;
  if (S?.capabilities?.interactive_search) {
    try { options = readSearchOptions(); } catch (error) { if (strict) throw error; options = null; }
  }
  return {format: PROJECT_FORMAT, name: el("project-name").value.trim() || "Untitled track",
    session: S.snapshot, preferences: {view: {...view}, search: {max_pieces: Number(el("max-pieces").value),
      slop: Number(el("slop").value), reversing: el("reversing").checked,
      ...(options === undefined ? {} : {options})}}};
}
function projectSnapshot() {
  if (!S?.snapshot) throw new Error("Wait for the editor to finish loading");
  const data = projectData(true), {max_pieces, slop} = data.preferences.search;
  if (data.name.length > 80 || !Number.isInteger(max_pieces) || max_pieces < 1 || max_pieces > 128 || !Number.isFinite(slop) || slop < 0 || slop > 1e9)
    throw new Error("Use a name up to 80 characters and valid search settings before saving");
  return data;
}
async function openProject(data, revision = S && S.revision) {
  // Emergency session downloads use the already supported session format.
  if (data?.format === "duplotrain-session/1") data = {format: PROJECT_FORMAT, name: "Recovered session", session: data, preferences: {}};
  const next = await api("/api/project/open", {data, revision});
  S = next; clearTransient(); closeProjectManagement();
  el("project-name").value = next.project.name;
  const prefs = next.project.preferences;
  if (prefs.search) {
    el("max-pieces").value = prefs.search.max_pieces; el("slop").value = prefs.search.slop;
    el("reversing").checked = prefs.search.reversing; el("reversing").dataset.touched = "1";
  }
  restoreSearchOptions(prefs.search?.options);
  if (prefs.view) { view = {...prefs.view}; fitted = true; } else fitted = false;
  // The project is open even when this tab's own search fields are invalid;
  // the status then asks for them to be corrected before the next save.
  redraw(); markProjectSaved(projectData()); status(`Opened project: ${next.project.name}`);
}
function readLocalProject(key, raw) {
  if (typeof key !== "string" || !key.startsWith(PROJECT_PREFIX) ||
      typeof raw !== "string" || raw.length > 2 * 1024 * 1024) throw new Error("No readable project selected");
  const data = JSON.parse(raw);
  if (!data || data.format !== PROJECT_FORMAT || typeof data.name !== "string" ||
      !data.name.trim() || data.name.length > 80 || data.session?.format !== "duplotrain-session/1" ||
      !Array.isArray(data.session?.layout?.placements)) throw new Error("Unreadable saved project");
  return data;
}
function closeProjectManagement() {
  projectManagement = null;
  if (el("project-manage")) el("project-manage").hidden = true;
}
function renderProjects() {
  const select = el("project-slots"), previous = select.value;
  const rows = [];
  try {
    for (let i = 0; i < localStorage.length; i++) {
      const key = localStorage.key(i);
      if (typeof key !== "string" || !key.startsWith(PROJECT_PREFIX)) continue;
      const raw = localStorage.getItem(key);
      if (raw === null) continue; // another tab removed it during enumeration
      let data = null, time = 0;
      try {
        data = readLocalProject(key, raw);
        const parsed = typeof data.saved_at === "string" ? Date.parse(data.saved_at) : NaN;
        if (Number.isFinite(parsed)) time = parsed;
      } catch (_) { /* Kept visible; never silently discard an unreadable copy. */ }
      const suffix = key.slice(PROJECT_PREFIX.length);
      const version = suffix.length > 12 ? suffix.slice(0, 8) + "…" + suffix.slice(-4) : suffix;
      const label = data ? `${data.name} · ${time ? new Date(time).toLocaleString() : "date unknown"} · ` +
        `${data.session.layout.placements.length} pieces · ${version}` : `Unreadable saved project (kept) · ${version}`;
      rows.push({key, raw, data, time, label});
    }
    rows.sort((a, b) => b.time - a.time || a.key.localeCompare(b.key));
    projectRows = new Map(rows.map(row => [row.key, row])); select.replaceChildren();
    for (const row of rows) {
      const option = document.createElement("option"); option.value = row.key; option.textContent = row.label;
      select.append(option);
    }
    if (projectRows.has(previous)) select.value = previous;
    if (projectManagement && projectRows.get(projectManagement.key)?.raw !== projectManagement.raw) {
      closeProjectManagement(); status("The selected backup changed in another tab; review its latest copy before editing.", "err");
    }
    if (projectBaselineSlot && !projectRows.has(projectBaselineSlot)) {
      projectBaseline = null; projectBaselineSlot = null; updateProjectStatus();
    }
  } catch (error) { status(`Local projects unavailable: ${error.message}. Download a project instead.`, "err"); }
}
async function saveLocalProject() {
  try {
    const data = {...projectSnapshot(), saved_at: new Date().toISOString()}, raw = JSON.stringify(data);
    if (raw.length > 2 * 1024 * 1024) throw new Error("project larger than 2 MB");
    // New saves stay non-overwriting; only explicit management edits a known key.
    const key = PROJECT_PREFIX + crypto.randomUUID();
    if (localStorage.getItem(key) !== null) throw new Error("Copy ID already exists; retry to create a new copy");
    localStorage.setItem(key, raw); closeProjectManagement(); renderProjects(); el("project-slots").value = key;
    markProjectSaved(data, key);
    status("Saved a new local project copy. Download project for a portable backup.");
  } catch (error) { status(`Project not saved: ${error.message}`, "err"); }
}
function manageLocalProject(action) {
  closeProjectManagement();
  try {
    if (!["rename", "delete"].includes(action)) throw new Error("Unknown backup action");
    const key = el("project-slots").value, row = projectRows.get(key);
    if (!row || localStorage.getItem(key) !== row.raw) throw new Error("Selected backup changed; refresh the list first");
    if (!navigator.locks) throw new Error("Safe backup management unavailable; download or save a new copy instead");
    if (action === "rename" && !row.data) throw new Error("Cannot rename an unreadable backup; existing copy kept");
    const box = el("project-manage"), operation = {key, raw: row.raw, action};
    projectManagement = operation; box.replaceChildren(); box.hidden = false;
    const title = document.createElement("p");
    title.textContent = `${action === "rename" ? "Rename" : "Delete permanently"}: ${row.label}`;
    box.append(title);
    let input;
    if (action === "rename") {
      const label = document.createElement("label"); label.textContent = "New backup name ";
      input = document.createElement("input"); input.value = row.data.name; input.maxLength = 80;
      input.setAttribute("aria-label", "New backup name"); label.append(input); box.append(label);
    }
    const confirm = document.createElement("button"); confirm.textContent = action === "rename" ? "Confirm rename" : "Confirm delete";
    confirm.addEventListener("click", async () => {
      if (projectManagement !== operation) return;
      const name = input?.value.trim();
      if (action === "rename" && (!name || name.length > 80)) { status("Use a backup name of 1–80 characters.", "err"); return; }
      confirm.disabled = true;
      try {
        // All destructive management uses an origin-scoped per-slot lock. The
        // exact selected bytes are rechecked INSIDE the lock (no stale overwrite).
        const changed = await navigator.locks.request(PROJECT_PREFIX + "manage:" + key, () => {
          if (projectManagement !== operation) return false;
          if (localStorage.getItem(key) !== operation.raw) throw new Error("Backup changed in another tab; refresh and review it again");
          if (action === "delete") localStorage.removeItem(key);
          else {
            const data = readLocalProject(key, operation.raw);
            const replacement = JSON.stringify({...data, name});
            if (replacement.length > 2 * 1024 * 1024) throw new Error("Renamed backup exceeds the size limit");
            localStorage.setItem(key, replacement);
          }
          return true;
        });
        if (!changed) return;
        if (projectManagement === operation) closeProjectManagement();
        renderProjects(); updateProjectStatus();
        status(action === "rename" ? "Renamed the selected backup; current design unchanged." : "Deleted only the selected local backup; current design unchanged.");
      } catch (error) { status(`Backup not changed: ${error.message}`, "err"); }
      finally { confirm.disabled = false; }
    });
    const cancel = document.createElement("button"); cancel.textContent = "Cancel backup change";
    cancel.addEventListener("click", () => { if (projectManagement === operation) closeProjectManagement(); });
    box.append(confirm, cancel); (input || cancel).focus();
  } catch (error) { status(error.message, "err"); }
}

async function readProjectFile(event) {
  const file = event.target.files?.[0]; event.target.value = "";
  if (!file) return;
  const sequence = ++importSequence, revision = S && S.revision;
  try {
    if (file.size > 2 * 1024 * 1024) throw new Error("file larger than 2 MB");
    const data = JSON.parse(await file.text());
    if (sequence !== importSequence) return;
    await openProject(data, revision);
  } catch (error) { if (sequence === importSequence) status(`Project not opened: ${error.message}`, "err"); }
}
