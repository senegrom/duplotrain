# Interactive completion and train analysis

The editor's interactive tools advance bounded engine jobs through short requests.
There is one job per session. It owns its immutable starting layout, available
inventory, endpoints and settings; changing the content, restarting the engine or
starting a different job discards its old continuation. No job request edits
the layout.

## Completion controls

**Close the loop** starts with eight alternatives. **Find more** raises that
allowance to 16, 32 and then 50 distinct layouts, retaining the current search's
suspended traversal. Alternatives are told apart by the track as built: each
added piece with the positions and directions of its connectors. The same pieces
found from the other end of the gap have other frames and placement order but
count once. **Search harder** raises both the node
allowance and the maximum added-piece count, up to 16 times the initial stage
budget and 128 added pieces. Its result allowance also increases. Pagination
builds eight candidate cards at a time; sorting never changes the underlying
candidate identity used for Apply.

**Pause at next checkpoint** stops the engine at its next checkpoint, without
destroying its worker or undo history, and publishes the accepted suggestions.
**Resume** continues the stored job. A preview arriving
while the search is running is not directly applicable: the engine must first
publish its candidate revision. Starting a new search withdraws the suggestions
published before it. Applying a suggestion is one normal, undoable edit and
releases the old job.

Ranking choices are discovery order, added-piece count, footprint area, scarce
stock consumption, new junctions and new bridge parts. Exact candidates rank
ahead of forced fits. A ranking selects the best of the candidates found, not a
globally proved optimum. The scarce-stock score sums each added count divided
by the corresponding available count, with a denominator of at least one.
Footprint ranking uses the existing sampled layout dimensions; it is not a
substitute for the width-inclusive room check below. Every request of a search
carries the chosen ranking, so a ranking chosen while the search runs applies
from its next checkpoint, starting at the first page.

Per-piece exclusion checkboxes, and the junction/bridge shortcuts, affect the
next new search's available pieces, not owned inventory or existing track.
A paused search retains its captured exclusions and room constraints. Its
preview displays those captured constraints even when new values have been
typed for the next search. Sorting the current result sample is allowed.

### Room and keep-out rectangles

Enter `xmin, ymin, xmax, ymax` in centimetres; keep-out regions use one rectangle
per line. These opt-in restrictions apply to the whole layout, including its
existing track, at every elevation: they are floor-to-ceiling regions, not
height-specific obstacles. A base already outside the restrictions is rejected
without moving or discarding pieces. The existing track is checked once, when
the search starts; each candidate is then checked for the pieces it adds.

Checks use route samples at 4 mm intervals, half the track width, catalogue end
overhang and an additional half-sampling-interval guard. Segments are tested
against the expanded keep-out boxes. Borderline fits may be conservatively
rejected. This is a sampled model of the track footprint, not a certification
of real-world furniture, support or train clearance. The solver's independent
joint, stock and collision checks remain separate. Up to 32 keep-out rectangles
are accepted; coordinates must be finite and within 10,000,000 mm of the origin.

Optional restrictions and ranking are project preferences. They are not part of
the layout, session or autosave formats, and projects without them open with the
defaults.

## Closing all gaps

**Close all gaps** accepts two to ten open ends and always plans exact,
non-reversing joins; the slop and reversing settings belong to **Close the
loop**. It chooses a constrained end, tries possible mates and alternative
completions, debits the shared remaining stock, and backtracks when a choice
prevents a later gap from closing. Already matching, compatible ends can be
joined without adding pieces. Track that already overlaps itself is refused
before the search starts, since no plan could then be overlap-free as a whole.
Each added piece is audited for overlaps against all the track before it when
its pair is solved, and only a complete plan reducing the open-end count to zero
is offered, after the final exact-joint, unchanged-base, inventory and size
checks.

The plan search tries at most eight distinct alternatives per pair, permits at
most 128 added pieces across the whole plan, and has a shared node allowance.
Each pair's search gets the job's search effort, so Search harder raises its
stage budgets as well as the depth and the shared allowance. This is a
bounded planner, not an exhaustive enumeration of all possible networks. A
limited or finished bounded search with no plan does not establish impossibility.
Pause/Resume retains its current backtracking stack. Raising its depth with
Search harder starts a new bounded outer plan search while retaining prior
accepted plans for deduplication; that operation is not claimed to resume every
outer decision. Ordinary single-pair DFS continues its existing exact stack.

## Engine continuation and limits

`solve_steps` is the cooperative form of the exact solver. A `SearchLimits`
instance supplies mutable node, result and completion-depth bounds. It yields
progress, accepted-solution and limit events. Raising a bound lets the caller
resume the suspended DFS, including its inventory, collision backtracking and
reverse tables. Closing an iterator releases its workspace. The synchronous
`solve` drains this iterator. Fresh-loop enumeration always runs its configured
depth in one pass; raising a piece bound on a continuation applies to
completion mode.

Interactive single-pair jobs run the stages of
[bridge-completion.md](bridge-completion.md) in order.
An exact ordinary stage alternates endpoints; forced fits and reversing
closures are not direction-equivalent, so those stages grow from the chosen end
only and run until their own limits stop them. Stage node budgets are shared
across directions, not multiplied for each direction. Template generation is separate
from DFS and its bounded list is regenerated when a higher depth is requested.
Room restrictions and publication guards run before a solution is streamed.
Each candidate's final placements are audited for overlaps exactly once, by
whatever produced them: the core search's replay audit, the arc oracle, or, for
an expanded bridge macro, a shared incremental auditor before the candidate
counts as a result. The base, stock, size, joint and room checks run once, where
the candidate is produced; the job then keeps one candidate per physical track
and only those its save and import guards accept.

One tick processes at most 32 checkpoint events and aims to return after about
20 ms between checkpoints. This is not a hard execution deadline: preprocessing,
a bridge expansion, validation or one train run can take longer. The editor
keeps its controls busy for the whole job rather than per request, so they do
not flicker between ticks, and it refuses any other engine request until the
job pauses or finishes: an edit, a check or a train run between two ticks would
change the session under the job or take the engine from its next tick. Request IDs,
job IDs, revisions and client generations prevent results from an old problem
from being applied to new content. Jobs expire after 20 minutes without a
request, checked on the next access, and are released on content changes or
explicit discard. The 50-result limit and bounded depth do not constitute a
fixed-byte memory ceiling.

## Finding and checking train routes

**Best settings for this start** tries all initial switch assignments for the
selected inward start, and **Best route / check all starts and settings** does so
for every valid inward start, within the chosen budget. Choose maximum lifetime coverage or maximum repeating-cycle
coverage. The report identifies the checked scope, completed runs, required
runs, best witness and a counterexample where applicable. A counterexample breaks
the weakest property that failed, as the classifier reports it: a run that does
not loop if there is one, else an endless run that misses some track, else one
whose repeating cycle does not traverse every piece both ways. **Load and trace
best route** and **Load counterexample** fill the existing start/switch controls
and run the normal trace without changing track geometry. A failed step ends the
analysis.

The analyser calls the `drive` model, not a second simulator. It
separately counts drivable pieces visited at least once and drivable pieces in
the eventual repeating cycle. A transiently visited bridge is not necessarily
part of the repeating circuit. Default run allowance is 20,000, adjustable from
1 to 100,000; each run has at most 10,000 steps and the job has a shared allowance
of 10 million traversal steps. Work is chunked between runs and can be paused
and resumed. Run or step limits produce an incomplete report, never a universal
verdict. Optimality and the looping classification appear only after every run
in the explicitly requested scope produced a verdict.

A completed analysis concerns that unchanged layout and this model's switch and
stone rules. It says nothing about different topology, later stone additions,
physical obstructions or external intervention during a run. Initial switch
witnesses remain per-run settings, not persistent layout geometry.

## Shared API

Interactive completion uses `/api/search/start`, then `tick`, `page`,
`pause`, `resume`, `continue`, `publish` and `discard`; subsequent requests carry
the job ID and current revision. Train analysis uses `/api/routes/start`, `tick`,
`pause`, `resume` and `discard`.
