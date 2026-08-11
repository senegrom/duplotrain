# Formal proofs (Lean 4)

Three hundred and forty-eight libraries, all self-contained (no
Mathlib), all sorry-free, honestly conditional where marked.  Core
five below, then the satellites:

* `Alternation.lean` — **the alternation seed of the four-beat law.**
  The abstract exhaustion (`../tools/baltern.py`) shows every active
  cycle has exactly four productive writes per period, strictly
  alternating between its two cells.  Machine-checked here: if two
  *consecutive* productive steps write the same cell `C` and the walk
  avoids `C` and `star C` strictly between the arrivals, the stretch
  after the second write **replays** the stretch after the first
  (`consecutive_replay` — every read is the same frozen register),
  the wrap step re-delivers the second slot unproductively, and the
  machine closes a completely quiet loop (`consecutive_avoid_loop`)
  — which contradicts the periodic recurrence of the write itself
  (`productive_periodic`, `state_replay_iter`,
  `productive_iff_of_state_eq`).  Headline
  `consecutive_same_write_visits`: **between two consecutive
  productive writes of one cell, the walk must stand in that cell or
  at its mouth partner strictly in between.**  The two remaining cases
  are now both eliminated: `quiet_return_same_cell_state` and
  `quiet_state_loop_forever` show that a quiet return to the same cell
  is a permanently quiet deterministic loop, while
  `quiet_mouth_unreachable` excludes the mouth visit.  Hence
  `consecutive_productive_write_cells_ne` proves outright that
  **adjacent letters of the productive-writer word are distinct** on
  every periodic tail.  The still-open step is to prove that the next
  letter must return to the preceding pair, rather than introduce a
  third writer.

* `MouthRetrace.lean` — **the four-beat engine: a mouth-stand write
  mirrors its approach, and a mouth-stand pair locks the writer word
  to two letters forever.**  All results are local — no periodicity
  hypotheses anywhere.  A delivery standing at the written cell's
  mouth is automatically productive (`mouth_stand_productive`) and its
  writer differs from the previous one (`mouth_stand_writers_ne`).
  The headline `mouth_retrace`: after a mouth-stand write at `t3`
  following a quiet stretch from the previous write at `t2`, the walk
  retraces its whole approach as the `bar`-mirror of itself,
  `e (t3+1+j) = bar (e (t3+1-j))` for `1 ≤ j ≤ t3-t2`, quietly until
  the last step.  The mirror ends on the previous writer's fresh
  register, so the next productive step occurs at the exactly mirrored
  time `t3 + (t3-t2)` and **writes the previous cell again**
  (`mouth_stand_return`): a third letter cannot follow two mouth-stand
  writes.  Iterating (`MouthPair`, `mouth_pair_step`,
  `mouth_pair_forever`, `mouth_pair_writer_period`): one consecutive
  mouth-stand pair forces productive steps exactly at the arithmetic
  times `b + k*(b-a)`, every delivery a mouth stand, the writer word
  `B C B C …` — two-letter periodic forever with equal spacing, the
  four-beat law's alternation half.  Finally `lobe_delivery_stands` and
  `lobe_pair_seed`: a delivery of a lobe slot *must* stand at the
  written cell's mouth (converse of `mouth_delivery_lobe`), so two
  consecutive productive lobe deliveries form such a pair.  Combined
  with `lobe_or_cross`, the alternation program's open frontier is
  confined to cross-valued (foreign-partnered) writers.  The first
  cross-side theorem is in: `cross_mirror_sails`, the exact dual of
  `mouth_stand_return` — if the write preceding the mouth-stand write
  was a *cross* delivery, the mirrored return step is **quiet**: the
  walk lands on the cross delivery's foreign read cell carrying its
  unchanged register, and the mirror continues into deeper history.
  So after a mouth-stand write the mirrored return is productive if
  and only if the preceding write was a lobe delivery; a cross write
  cannot terminate the retrace, only a stale register further back
  can, and the stale registers are exactly the interim writers'.

* `LobePartnerBounce.lean`, `LobeToggle.lean`, and
  `LobeVariationVisit.lean` — **an occupied lobe is a forced parity
  counter.**  Entering its mouth partner forces a two-step bounce
  `e (k+2) = bar (e k)` and toggles the lobe register exactly; conversely,
  every change of a persistent occupied lobe has such a partner visit.
* `TwoReflectorEdgeTrap.lean` and `TwoReflectorFiniteTrap.lean` — **two
  persistent lobe reflectors facing the endpoints of one occupied support
  edge form an exact four-step trap.**  The endpoint entries repeat every
  four steps and all entries stay in the resulting six-slot alphabet,
  both indefinitely and up to a finite occupancy horizon.  For four
  distinct reflector/support cells, `two_reflector_edge_register_block`
  proves the exact register update: only the two lobe registers toggle;
  after the initialization block, `two_reflector_edge_state_period_eight`
  gives a complete eight-step machine-state recurrence, and
  `two_reflector_edge_snapshots_four` proves that every later family of
  distinct register snapshots has cardinality at most four.
* `StationaryTail.lean` — **a recurrent tail whose complete cell-level routing
  projection has stopped changing has at most four register snapshots.**
  `stationary_recurrent_tail_four_complete` derives a primitive cell period
  internally and handles both the forever-quiet and productive cases; callers
  need only exact entry/register recurrence and projection stationarity.

* `LobeDichotomy.lean` — **every cycle cell is a Gray flipper or
  foreign-valued.**  A slot can only be delivered by reading its
  bar-partner out of that partner's cell (`partner_held`), so:
  foreign-partnered registers are *irreversible* — a cell that holds
  a slot whose partner lies outside can never again hold an
  inside-partnered slot (`cross_stays_cross`) — and while a cell is
  lobe-valued, **every arrival is the Gray flip** `reg := bar reg`
  (the delivered slot's inside partner must equal the current
  register), so the register never leaves `{v₀, bar v₀}`
  (`lobe_gray_lock`): σ ≤ 2 with no writer-set, productivity, or
  `bar`-freeness hypotheses.  Periodicity turns irreversibility into
  a dichotomy (`lobe_or_cross`), and composed with the rho theorem
  (`rho_gray_or_cross`): on every run's eventual cycle, **every cell
  either keeps its register in a two-element bar-orbit — the Gray
  pair — or is foreign-valued at every moment**, where each arrival
  reads a cell other than the written one
  (`cross_delivery_reads_foreign`).  Lemma B's remaining work is
  confined to the foreign-valued cells.

* `LoneWriter.lean` — **m ≠ 1 on cycles: the lone writer freezes.**
  If every productive step of a periodic tail writes into a single
  cell `C`, then every register — including `C`'s own — is constant,
  and there are no productive steps at all.  The engine: foreign
  registers freeze (`lone_frozen_foreign`); the walk can never stand
  at `star C` after visiting `C` (`lone_no_partner`, by the retrace
  palindrome), and a cell is only ever *read* from its partner, so
  the lone writer's variation is invisible to its own steering; any
  two `C`-visits therefore have identical futures (`lone_merge`), and
  periodicity turns merged futures into equal deliveries
  (`lone_arrivals_agree`), freezing `C` too.  Headline:
  `rho_quiet_or_two_mouths` — **every eventual cycle is completely
  quiet or steered from at least two distinct cells**, for every
  machine, every run, every `N`.  The dynamic half of the one-mouth
  theorem, and the death of the lone-alternating-tree case of lemma B.

* `SteeringLaw.lean` — **active cycles stand at active mouths.**
  The generalization of the lone-writer engine to an *arbitrary*
  writer set `S`, needing neither the palindrome nor `bar`-freeness:
  a cell is only ever read from its mouth partner, so if the walk
  never stands at `star C` for any writer `C`, every read is frozen,
  same-cell visits merge (`no_stand_merge`), periodicity equalizes
  all deliveries (`no_stand_arrivals_agree`), every register freezes
  (`no_stand_freeze`) and nothing is productive (`no_stand_quiet`).
  Headline `active_tail_stands_at_mouth` / `rho_steering`: **every
  eventual cycle is completely quiet, or the walk physically stands
  at the mouth partner of one of its active cells** — for
  `S = [C1, C2]`, the two-mouth cycle must visit `star C1` or
  `star C2`, the dogbone's mouth crossings.  Plus the stand anatomy:
  `stand_delivery` (a stand fetches exactly `bar (reg C)` — the only
  way a writer's variation is ever read) and `stand_entry_frozen`
  (if `star C` is not itself a writer, all stands at `star C` carry
  one fixed entry: the cycle is frozen rails between look-alike
  stands, and only the fetched delivery varies).  `stand_flip`: a
  delivery landing back in its writer cell is the Gray move
  (register := its bar); `flip_lock`: **a cell whose every arrival
  is the self-flip keeps its register in the two-element orbit
  `{v₀, bar v₀}` forever** — σ ≤ 2, the two-value half of lemma B
  for pure flipper cells, unconditional.

* `Periodicity.lean` — **every run is a rho**: the state (current
  entry + registers of the listed cells) evolves autonomously and
  ranges over a finite space, so some state recurs within
  `|slots|^(|cells|+1) + 1` steps (`state_repeat`) and determinism
  replays the stretch forever (`run_eventually_periodic`): explicit
  pre-period and period bounds, machine-checked.  `run_rho` adds the
  payoff: on the tail all registers are periodic too, and — via
  `recurrence_emission` — **every productive step on the tail
  re-emits a token**: the eventual cycle's token population is
  conserved, unconditionally.  The cycle-classification theorems
  (`lone_write_no_mouth`, `divergence_names_steer`) now have a
  machine-checked cycle to run on.

* `FutureEntryBound.lean` — **the linear future entry alphabet**:
  every entry from any base time on lies in a fixed alphabet (the base
  entry, bars of base registers, bars of live tokens) of size
  ≤ `2·#cells + 1`; pair-duplicate-free phases are quadratically
  bounded.  Built on `future_register_le`.
* `CellHeat.lean` — **local heat never grows**: each cell's token
  count is individually non-increasing (tokens cannot migrate between
  cells) — so every condition of the Gray-tail token shape
  (tokenless cells, ≤1-token cells) is monotone once reached.
* `TokenState.lean` — occupancy and token-ends *determine* every
  register (`confirmed ↔ occupied ∧ ¬token`): state recurrence is
  finite token motion on the monotone occupied support.
* `PairMultiplicity.lean` — if every consecutive entry pair occurs
  ≤ `r` times in a phase, the phase has length
  ≤ `r·(2·#cells+1)²`: any uniform pair-multiplicity bound gives a
  polynomial state bound.

* The **strict-base campaign** (~70 libraries, from `ReversalFacts` /
  `MonotoneSupport` through `SupportWeightFibres` /
  `CanonicalProjectedEpochFrame` to
  `CanonicalUnconditionalGlobalBound` and the physical bridge) —
  **a snapshot ceiling with exponential base strictly below 2**.
  The engine, proved outright: occupied support only shrinks, so a
  run has ≤ `#edges + 1` support epochs (`support_epoch_bound`) and
  occupied edges inject into cells (`occupied_edges_le_cells`);
  within one fixed support, no-full components freeze, tree
  components replay their whole snapshot from one full-edge choice
  (rooted-rank certificates), active lobes are star-separated before
  any absorption, and the resulting sparse code has capacity²
  ≤ `2^#cells`; the first certified lobe-pair absorption starts a
  ≤ 4-snapshot Gray tail (`absorbed_snapshot_count`).  Headline —
  **unconditional over any complete finite echo frame**
  (`canonical_unconditional_global_bound`,
  `finiteFrame_atMost_N_strict_bound`): any duplicate-free list of
  register snapshots in a window satisfies
  `T^8 ≤ (4N+2)^8 · 2^(7N+18)` — that is,
  `T ≤ (4N+2) · 2^(0.875·N + 2.25)`, strictly below the `2^N`
  pigeonhole for large `N`.  The **physical transfer**
  (`OverwriteDynamics` / `OverwriteLasso` /
  `DeterministicOverwriteReturn` / `EchoConfigCount` /
  `PhysicalPrefixCount` / `ConcreteOverwriteBridge`) rides the
  overwrite lasso — pin words are idempotent, so each recurrent
  echo configuration carries at most two tongue vectors per cascade
  prefix — giving `T^8 ≤ 2^8 (2N)^8 (4N+2)^8 · 2^(7N+18)` for
  concrete tongue vectors at cascade boundaries
  (`strict_boundary_bound_of_overwriteCompilation`).  This last step
  is **conditional on the compilation interface**
  (`OverwriteEchoCompilation`): constructing, for every wiring, an
  echo machine whose configuration-driven pin words reproduce
  `stepN`'s tongue states (the T9 compilation, partially built in
  `ConcreteMachine` / `ConcreteCascadeFacts` / `ConcreteFiniteBounds`)
  is the open step of this route.  Two sharpenings landed since:
  the **Fibonacci capacity** chain (`FibonacciSparseBound` /
  `TreeCapacitySevenTenths` / `RelevantFibonacciNBound` /
  `RelevantFibonacciPhysicalBound`) lowers the per-epoch code to
  no-adjacent sparse words, giving
  `T ≤ (2N+1)·fibBalancedCapacity N + 4` for snapshots and
  `T = O(N³·(√(2φ))^N)` for physical tongue vectors — exponential
  base ≈ **1.79891** — under the same compilation interface; and the
  **concrete compiler chain** (`DescentSimplicity` — landed cascades
  never revisit a switch; `DescentRouteCatalogue` — canonical routes;
  `ConcreteTreeCodes` / `ConcreteTreeRetrace` / `ConcreteAscentTrace`
  / `ConcreteTraceRegisters` / `ConcreteEchoRun` /
  `ConcreteCertifiedEchoRun` — **`certifiedConcreteEcho_isRun`: every
  certified segmented concrete run IS a run of the canonical echo
  machine**, the central compiler theorem) now builds the T9
  instance; what remains is producing the `CertifiedConcreteEchoRun`
  certificate from raw `stepN` dynamics.

* `LinearBound.lean` — **snapshots ≤ #cells + #alts + 1**, for any
  alternation list covering the prefix: the unconditional accounting
  with an arbitrary alternation budget (no Gray tail needed).
* `SlotBound.lean` — **snapshots ≤ #slots + 1 under one hypothesis**,
  `ProductiveSlotReplay` (two productive arrivals at the same slot give
  the same snapshot): the cleanest known single-lemma reduction of the
  O(N) state law.
* `ReplayFacts.lean` — first steps toward proving that hypothesis:
  equal delivered entries force equal registers at the destination and
  source cells.
* `AlternationBound.lean` — forced-predecessor lemmas and a
  conditional two-alternations-per-cell bound.
* `SupportBound.lean` / `SupportMove.lean` — the edge-occupancy
  monovariant: an empty jump edge (neither end confirmed) stays empty
  forever; transfer laws for fully-confirmed edges.
* `EdgeReversal.lean` — the cell-level walk arrow reverses after
  traversal (the LIFO seed at cell level).
* `PairBound.lean` — distinct consecutive-entry pairs number ≤ #slots².

**`GeneralN.lean` — general-N theorems, no exhaustion.** Every result holds
for an arbitrary number of switches and arbitrary wirings, proved by
structural induction (no `native_decide`, no `sorry`):

| theorem | statement |
|---|---|
| `trailing_route`(`_independent`) | a trailing pass's route never reads the tongues (T1/T2) |
| `descent_sound` / `_pins` / `_noop` / `_rebase` | cascades run as recorded, pin exactly their branches, and are tongue-independent no-ops when re-run |
| `retrace` | **T3**: a train entering the last cascade switch's stem walks the cascade *backwards* by pure facing moves — the pins route it home — tongues untouched |
| `lobe_hop` | facing a lobed switch crosses the lobe, flips it, exits the stem (2 steps, both tongue values) |
| `dogbone_halfPeriod` | **the bounce**: lobed `a`, arbitrary trailing cascade, lobed `b` — `2·|ps|+6` steps flip exactly `a`,`b` and return to `a`'s stem |
| `dogbone_period` | two half-periods restore the tongues exactly: the orbit is a genuine cycle whose tongue states are the Gray square |
| `IsReflector` / `lobe_isReflector` | the one-port gadget interface; lobes are its smallest instances |
| `reflector_halfPeriod` / `reflector_period` | **any two reflectors joined by any cascade** bounce forever; for involutive commuting state maps the cycle's tongue states are exactly the Gray orbit — at most 4 |

`dogbone_period` and `reflector_period` cover infinite families of wirings
(any cascade length, any gadget size, any N) — the mechanism that caps every
observed cycle at 4 vectors, formalised.

**Direct physical-track route (`TrackTrace.lean`, `TrackEdge.lean`,
`TrackLobe.lean`, `TrackNormalForm.lean`).**  This is the current shortest
route to the raw state law and does not pass through an assumed echo
compiler.  `TrackEdge.lean` formalises the first-repeated-physical-edge proof
of Chalcraft--Greene and Aaronson directly over `Wiring`:

* `wireEdgeRep_eq_iff`: canonical edge-name equality is exactly equality up
  to reversing the symmetric track edge.
* `PhysicalTrace.switchSimple_of_edgeSimpleFrom`: **Observation 1**, including
  the starting edge: before any physical edge repeats, no switch repeats.
* `PhysicalTrace.edgeSimpleFrom_length_lt` and
  `physical_edge_repeats_of_long_run`: an `N`-switch live run repeats a
  physical edge by step `3*N`; this is a kernel-checked linear cutoff, not a
  finiteness assumption.
* `first_edge_revisit_split_from`, `passageEdgeRep_eq_iff`: the first repeated
  edge is recovered as an actual passage split with its exact same/reverse
  orientation—not merely as a duplicate key.
* `same_oriented_first_edge_settles` and
  `reverse_oriented_first_edge_retraces`: **Observation 2 and the lollipop
  retrace**.  An internal same-oriented repeat is an absorbing simple cycle;
  an internal reverse repeat closes a simple candy and retraces the whole
  earlier runway without further tongue changes.
* `first_edge_outcome_of_long_run`: the complete linear-prefix case split:
  absorbing cycle, exact reverse retrace, one-step return to the start port,
  or one-step exit past the start.

`TrackGlobalRepair.lean` now carries the whole-route repair with the other
reflector's support as an invariant.  `repair_forward_damage_or_facing` says a
switch-simple reference route in an arbitrary tongue state either exposes a
concrete broken passage approached through its stem, or repairs every groove
in one traversal.  Its stronger successor
`repair_preserving_paths_until_conflict` advances one physical passage at a
time and stops at the first facing diversion or the first state-changing
contact with a protected groove family; every earlier passage is proved to
preserve that whole family.
`support_grooves_of_orientedRoute` and
`oriented_data_eq_of_route_grooved` prove that the repaired route restores the
entire manufactured-reflector support and still selects the same far endpoint.
`current_route_reference` aligns only the reflector's private action tongue,
whose reusable support is disjoint, so
`repair_current_route_preserving_until_conflict` replays the route the train
actually selects rather than freezing an obsolete choice.  The local
classifiers `protected_changed_contact_periodic_or_forward` and
`protected_facing_contact_periodic_or_forward` close every backward contact as
an exact grooved cycle.  `return_change_facing_eventuallyPeriodic` closes the
former final-mouth exception by an explicit two-capture period.  Finally,
`completed_route_with_pair_support_periodic` invokes the already proved
complete two-reflector theorem once repair has installed both supports.
Consequently `manufactured_pair_protected_repair_outcomes` eliminates the
old unspecified facing residual and names two concrete **forward merges**.
`FacingForwardMerge.flip_candy` localizes the no-change merge to a reversed
candy passage; `reverse_candy_suffix_absorbs` and
`FacingForwardMerge.eventuallyPeriodic` then close it by an explicit positive
period in all three prefix cases (no action-switch contact, mouth capture, or
trailing self-repair).  Thus
`manufactured_pair_eventuallyPeriodic_or_changed_forward_merge` leaves only
the state-changing, old-passage-self-repairing forward splice.
`ChangedForwardMerge.spliced_lobe_reflector` now proves that this last splice
always manufactures a concrete flip lobe at the merge switch, exposes the
actual reached post-contact state, and retains an exact suffix from the
lobe's outside edge to the original boundary, applying the old reflector
action.  `single_flipped_trailing_repairs` proves that flipping one grooved
trailing passage on a selected reflector route repairs itself and completes
the unchanged suffix.  `suffix_after_runway_passage` packages every strict
runway suffix of an identity reflector as a smaller opposite-facing identity
reflector, with support foreign to the discarded switch.  Consequently
`ChangedForwardMerge.eventuallyPeriodic_of_stay` closes the complete old
identity-reflector branch: a runway splice is a paired-reflector Gray period,
while a splice at the self-linked core closes after two lobe traversals.
For the protected old **flip** reflector,
`ManufacturedFlipReflector.suffix_after_runway_passage`
normalizes either candy orientation and packages the strict runway suffix as
an opposite manufactured flip reflector.  The generic
`manufactured_flip_arbitrary_lobe_theta_half`,
`arbitrary_lobe_reverse_trace`, and
`manufactured_flip_arbitrary_lobe_period` prove the required theta period
without assuming the spliced candy is switch-simple.  Therefore
`manufactured_flip_runway_splice_periodic` closes both the disjoint-action
and intersecting-action runway cases, while
`ChangedForwardMerge.eventuallyPeriodic_or_flip_candy` and
`nonrunway_oriented_branch_entry_is_candy` reduce the sole remaining case to
an explicitly oriented passage strictly inside the old candy.  That final
candy residual is now closed too.  `candy_completion_latched` proves that the
untouched old tail becomes idempotent after its action is pinned.  If the
fresh approach avoids the old action,
`manufactured_flip_candy_splice_periodic_of_approach_foreign` gives one
settling lap followed by an explicit fixed macro-period.  If it meets the old
action, `physicalTrace_endpoints_eq_before_avoided_switch` and
`facing_approach_to_candy_splice_impossible` show that the first meeting
cannot be facing—the fresh and old routes would otherwise reach the splice
switch through the same arm.  The remaining trailing meeting repairs the old
action and closes by
`manufactured_flip_candy_splice_periodic_of_approach_contact`.
Consequently `ChangedForwardMerge.eventuallyPeriodic` closes both old
reflector kinds, and
`manufactured_pair_protected_repair_eventuallyPeriodic` closes every outcome
of protected two-reflector repair.

The raw global structural result is now complete:
`long_run_eventually_periodic` states that, on every arbitrary `N`-switch
wiring, any run live for `3*N+2` steps from a known incoming physical edge is
eventually periodic.  It is proved directly over `Wiring`/`stepN`, with no
finite-`N` enumeration and no planarity assumption.
The capstone `repair_or_facing_diversion` therefore completes a damaged
reflector all the way to the opposite boundary unless that one explicit
facing-first diversion occurs.  The endpoint-strengthened
`tails_endpoint_dichotomy` also retains an actual `PhysicalTrace` along the
unmatched tail between the old-route and fresh-exploration endpoints, rather
than only their prefix-comparability.  The global capstone lifts the repaired
journey back to the original train start while retaining the forward-fault
certificate.  All new reductions are unconditional and general-`N`; the open
global track case is now the state-changing forward splice strictly inside
an old flip reflector's candy, not the former facing-first diversion,
identity-reflector case, or flip-reflector runway case.

* `first_revisit_of_long_run`: every live `N+1`-passage run has a first
  revisited switch after a switch-simple prefix of length at most `N`.
* `first_revisit_fork`: the first repeated edge has the complete raw-track
  dichotomy — same-direction closure is an absorbing simple cycle; crossed
  closure retraces the whole runway exactly (or falls off at its far edge).
* `stem_lobe_isReflector`, `crossed_revisit_full_reflector`, and
  `same_exit_revisit_full_reflector`: every crossed closure, including the
  self-edge corner case allowed by abstract `Wiring`, is a universal
  identity/one-switch-flip reflector behind its arbitrary simple runway.
* `first_revisit_cycle_or_supported_reflector`: every first revisit is now
  packaged as either a simple cycle or a reflector carrying its exact grooved
  support paths.
* `SupportedReflector.paired_period`: two opposite supported reflectors whose
  local actions avoid one another's supports have a genuine period, by the
  four-corner Gray composition.
* `ManufacturedReflector.manufacturing_journey_distinct_le_N_add_two`: the
  complete first-reflector construction, including its arbitrarily long exact
  retrace, exposes at most `N+2` distinct restricted tongue vectors.
* `ManufacturedReflector.travel_two_phase_tongues`: every intermediate time
  in one concrete reflector traversal has exactly the incoming vector or its
  one local-action image.
* `manufactured_pair_all_time_four_phase_tongues` and
  `manufactured_pair_four_novelty_cover`: a compatible opposite manufactured
  pair has only the four Gray-corner tongue vectors at **every** future time,
  not merely at the period endpoints.
* `manufacturing_journey_then_pair_distinct_le_N_add_six`: once a first
  manufactured journey reaches such a compatible pair, the complete raw
  trajectory satisfies the target `N+6` bound, with future liveness derived
  from the pair period rather than assumed.
* `manufactured_flip_candy_splice_absolute_one_novelty`: the foreign-candy
  repair residual contributes at most one genuinely new vector, including
  its eventual paired-reflector tail.
* `ChangedForwardMerge.runway_or_candy_absolute_four_novelty`: every
  changed-forward contact—runway or candy, with disjoint or intersecting
  suffix actions—has an absolute four-vector Gray cover.  The local runway
  novelty branch now has no residual case.
* `cyclic_minimal_stable_blocker_lobe_or_recurrent_six_chip_nest`: cyclic
  restoration-frame descent eliminates the wraparound blocker; its only
  non-lobe residue is a strict six-chip nest with a fresh third root.
* `strictly_nested_repeated_writer_novel_openings_le_switches`: every
  repeated-writer novel opening in one strict nested restoration family is
  charged injectively to a physical switch, giving a coefficient-one bound
  for that branch.
* `collapsed_geometry_recurrent_snapshots_four`: under the recurrent closed
  component certificate, both collapsed visible-chip geometries have at most
  four snapshots.

The coefficient-one `StateLaw` remains **OPEN**, but the direct-track argument
now proves an unconditional general linear theorem.
`GeneralN.state_law_linear_three_sharp`
(`StateLawThreeSharp.lean`) says that any one-train
run on an `N`-switch wiring visits at most `3*N+7`
pairwise-distinct tongue vectors, superseding the earlier
`state_law_linear_four` (`4*N+9`), `state_law_linear_five` (`5*N+9`),
`state_law_linear_eight` (`8*N+7`), `state_law_linear_eleven`
(`11*N+8`), `state_law_linear_fourteen` (`14*N+9`),
`state_law_linear_fifteen` (`15*N+7`), `state_law_linear_seventeen`
(`17*N+5`), `state_law_linear_eighteen` (`18*N+3`),
`state_law_linear_twenty_four` (`24*N+5`) and
`state_law_linear_twenty_six` (`26*N+3`).  The theorem is
stated over raw `Wiring`/`stepN`, with no small-`N` enumeration and no
conditional hypothesis.
The repository does **not** claim the sharper `N+6` state law.

Four layers of improvement feed the current constant.  The novelty-aware
lasso (`FirstActivatedExact.lean`, `NoveltyAwareLasso.lean`): the two
manufacturing journeys of the repaired pair are charged for their
*construction history* — whose dimension is explicit — rather than
their full travel.  The overlap-aware count
(`NoveltyAwareLassoOverlap.lean`): boundary vectors between journey A,
journey B and the tail are shared, so one copy is erased at each seam.
The sharp repair caps (`TrackThetaCaptureSharp/Tighter.lean`,
`TrackStaySpliceSharp.lean`, `TrackQuantitativeRepairSeventeen/Fifteen.lean`):
theta captures cost `2*N+1`, a theta half `6*N+1`, the reflector pair
`14*N+2`, the changed-forward splice `13*N` (`9*N` stay, `13*N` flip),
protected repair `15*N+2`.  Direct tongue counting
(`PairTongueCountSharp.lean`, `CompleteRepairTongueCountSharp.lean`,
`TwoJourneyTailCountSharp.lean`, `KnownEdgeFifteen.lean`): tongue-vector
novelty replaces physical travel where the two diverge — a complete
traversal has two tongue phases regardless of its length, so the pair
lasso counts `12*N+3` distinct vectors and complete repair `13*N+3`;
`known_edge_long_run_distinct_le_fifteen` gives `15*N+6` known-edge and
the entry-free assembly pays `+1` for time zero.

**The pointwise theta program** (`TrackThetaPointwiseCore.lean`,
`TrackThetaAllTime.lean`) pushes that trade to its limit for flip/flip
reflector pairs.  The support-fault dichotomy is proved *pointwise* and
without any switch-count hypothesis: every step of a capture shows one of
two tongue phases, every step of a repairing traversal one of three
(`manufactured_support_fault_dichotomy_pointwise`, over the six contact
geometries runway/candy-forward/candy-reverse × facing/trailing).
Composed around the theta cycles this yields absolute laws:
a one-sided intersection visits at most four tongue vectors ever
(`manufactured_one_sided_theta_all_time_four_phase`), a mutual
intersection at most three, and — the capstone —
`manufactured_flip_pair_all_time_four_phase`: **any** flip/flip
manufactured pair, however its supports intersect (disjoint, one-sided,
or mutual), is live forever and visits only the four corners
`state, state+A, state+B, state+A+B`; `manufactured_flip_pair_distinct_le_four`
turns this into a liveness-free count of four.

The counting assembly absorbs the phase laws in
`PairTongueCountFour.lean` and `KnownEdgeFourteen.lean` (the
reflector-pair count drops to `8*N+4`, complete repair to `9*N+4`, the
changed flip splice to `2*N+5` by position-counting its lead window),
which the stay-side program (`TrackStayContactAllTime.lean`,
`TrackStaySpliceAllTime.lean`, `PairTongueCountAbsoluteFour.lean`,
`TrackEarlyRepairSharp.lean`) then flattens completely: **every**
manufactured reflector pair counts four tongue vectors, complete repair
`N+4`, the changed stay splice `N+2`, and the early repair exits close
within `6*N+3` — the coefficient-8 law of `KnownEdgeEight.lean`.

`TrackEarlyRepairCount.lean` and `FacingMergeCount.lean` finish the
protected-repair side: the early exits are not just short, they are
vector-trivial.  A backward contact retraces and replays entirely at the
post-contact state (its cycle carries **one** vector, so the exit counts
its route window plus one, `N+2`); the final-mouth capture alternates
between exactly **two** phases after its window (`N+2`); and the
facing-forward merge is its route window plus the single alternate phase
(`N+2`, replacing the `4*N+1` lead window).  Protected repair therefore
counts `2*N+5` — bound by the changed flip splice — and the
two-reflector component `4*N+8` (`known_edge_long_run_distinct_le_five`
recorded the intermediate `5*N+8` stage, with the first periodic
outcome still charged its `5*N+1` time cap).

The constant-count program (`FirstCycleCount/Sharp.lean`,
`TrackEarlyRepairConstant.lean`, `EarlyFacingConstant.lean`,
`ChangedStayCountConstant.lean`, `ChangedFlipCountActual/Constant.lean`,
`CompleteRepairConstant.lean`, `ProtectedRepairThree.lean`,
`OneJourneyTailCount.lean`, `TwoJourneyBoundaryTailCount.lean`,
`KnownEdgeLift.lean`) then removes the last window-shaped charges: the
first simple-cycle settle counts `N+2`, the changed flip splice is
charged for its *actual* route lead, complete repair compresses to five
vectors and the changed stay splice to three, so protected repair costs
`N+4`; the journey boundaries are shared (`2*N+2` for two histories),
giving `known_edge_long_run_distinct_le_three_sharp` at `3*N+6` and the
entry-free `3*N+7`.  The remaining slack on the way to `N+O(1)` sits in
the `N+2`-sized construction histories and first-cycle windows
themselves — the sharp program's single-history `N+1` accounting is the
endgame.

`TrackQuantitative.lean` completes the extraction with a checked bounded-lasso
interface.  `EventuallyPeriodicWithin w c cap` retains `lead + period ≤ cap`;
`reduce_time`, `configuration_count`, and `tongue_vector_count` prove that
such a lasso admits at most `cap` distinct sampled configurations or tongue
vectors.  The first-revisit proof now has a quantitative sibling:
`first_activated_quantitative_outcome` gives either a lasso of size `3*N` or
an activated manufactured reflector reached within `2*N+1` steps.  Moreover
every manufactured reflector has travel at most `2*N`, and a disjoint pair's
explicit four-corner period fits within `8*N`.
`TrackQuantitativeTight.lean` exports the exact runway-prefix and
suffix-travel identities: shortening at a runway contact removes twice the
discarded prefix plus the contacted passage.  This tightens changed flip
merges to `18*N`, protected repair to `22*N`, and an entry-free global
lasso to `26*N+3`.  `state_law_linear_twenty_six` handles both live long
runs and runs that fall off early to obtain the same `26*N+3` vector bound.

**`EchoMachine.lean` — the abstracted cycle dynamics** (T9 in
../lazy-point-theory.md): any wiring's trailing structure compiles to a
forest of trees; the cycle dynamics reduces to a register machine (one
register per tree = slot of its last ascent; step = write own register,
read mouth-partner's, jump through its bar-involution).  General-N
theorems, no `native_decide`, no `sorry`:

| theorem | statement |
|---|---|
| `reg_write` / `reg_skip` / `reg_stable` / `reg_last_write` | a register holds exactly the slot of its cell's most recent ascent |
| `return_jump` | the step identity: the next entry is `bar` of the partner cell's last ascent entry |
| `echo` | the repetition identity: an entry produced by two nested returns **literally repeats an earlier entry** (the LIFO seed) |
| `succ_repeat` / `entry_change_read_change` | alternation propagation: same-cell ascents produce the same successor unless the partner register changed in between |
| `bounce_step` / `bounce_orbit` | a partner-alternating orbit obeys `e(k+2) = bar(e k)` and visits **at most 4 distinct entries** — the Gray square, for all N |
| `unproductive_stall` | a write that re-stores the current value changes **no** register: states move only through productive writes |
| `productive_first_or_alternation` | **the accounting theorem**: every productive write is the *first* write of its cell (≤ N over a run) or an *alternation* — the unconditional skeleton of f(N) ≤ N + O(1) |
| `absorb` / `absorb_entries` | **absorption**: a doubly-lobed mouth pair entered compatibly traps the walk forever — every later entry lies in `{a, bar a, b, bar b}`, so all subsequent alternations are confined to the two cells (the lobed case of lemma B, as an attractor) |
| `reg_cell` / `witness` | registers stay in their own cells, and **every entry names its delivery**: `cell (bar (e (k+1))) = star (cell (e k))` with the partner register equal to `bar (e (k+1))` — the predecessor structure is forced (seed of the T10 nesting argument) |
| `succ_of_reg_eq` | merge at the mouth, direct form: same cell + equal partner registers ⇒ identical successors — variation cannot steer itself |
| `snap_stall` / `snap_between` | register snapshots move only at productive steps and are constant across productive-free stretches |
| `state_law` | conditional counting scaffold — **not the state law**: IF a run has a ≤4-element Gray tail and ≤1 alternation before it (both **open** — the hard core of the problem), THEN ≤ `#cells + 6` distinct snapshots. Contributes only the counting around the open core |
| `confirmed_step` / `head_confirmed` | the confirmation dynamics: each cell confirms exactly its register slot, and every step's read value is confirmed — the walk always leaves a confirmed slot |
| `arrival_token` / `token_step` | a productive step lands exactly on a **token** (unconfirmed slot, confirmed partner) and can create at most one new token, at the evicted slot of the same cell |
| `tokens_nonincreasing` / `tokens_le_cells` | **heat never grows**: the number of tokens — the machine's capacity for future alternations — is non-increasing along any run and at most one per cell at every moment. (Does NOT bound alternation *events*: a token can be consumed and re-emitted forever — the Gray flip — so the open core stands) |
| `freezeout` | **freeze-out**: a cell with no tokens never changes its register again — productive arrivals need a token of the written cell, and fresh tokens appear only at the written cell's own evicted slot |
| `singleton_lock` / `singleton_lock_reg` | **the singleton lock**: a cell whose tokens are contained in `{t}` keeps its register in `{current register, t}` **forever** — single-token cells alternate between at most two slots: the σ ≤ 2 half of lemma B for singleton cells, unconditional |
| `token_pedigree` / `future_register` | **the repertoire collapse — the machine can never invent values**: every token traces back to a base-time token or to an evicted register, so every value a cell's register will *ever* hold is either its value now or the slot of a token alive now.  The current token profile spans the entire future state space, and it only shrinks |
| `repertoire_count` / `fresh_values_le_tokens` | the collapse, counted: σ(C) ≤ 1 + #tokens(C) for every cell, and **at most `#cells` fresh values ever appear in the whole run** — Σ(σ−1) ≤ #tokens ≤ #cells across all cells and all future time, unconditional |
| `tokens_antitone` / `no_emission_drop` | heat decreases over arbitrary intervals; a productive step whose evicted slot does not come out a token **strictly** cools the machine |
| `recurrence_emission` | **conservation on cycles**: inside any register recurrence every productive step re-emits — the eventual cycle's tokens are a conserved population, handed from evicted slot to evicted slot, never destroyed.  With the collapse, the cycle's whole value repertoire is spanned by that fixed population |
| `recurrence_dichotomy` | **the cycle dichotomy**: inside a recurrence every productive step either flips its own edge (evicted = bar of arrival — the Gray move) or hands off through a foreign edge that was fully confirmed before the step |
| `change_has_productive`(`_le`) | registers move only through productive writes of their own cell |
| `variation_needs_variation` | **the steering seed (T10 brick 1)**: two different deliveries with a common witness cell force a productive write of that witness cell strictly between them — a cell's variation must be steered by somebody's variation |
| `trajectory_merge` | **trajectory determinism**: two moments at the same cell whose subsequent reads all agree produce identical entry sequences — the walk branches only where a read differs |
| `token_shape_tail` / `gray_tail` | **the Gray tail from the token shape**: under the shape every exhaustion exhibits — ≤1 token in each of two cells, none anywhere else — every later snapshot is one of **four explicit candidates**, so at most 4 distinct snapshots occur, ever: the quantitative half of lemma B |
| `state_law_of_token_shape` | the conditional scaffold re-based: token shape at `K` + ≤1 alternation before `K` ⇒ ≤ `#cells + 6` snapshots.  The open core is now exactly *reaching* the token shape within one alternation |
| `divergence_names_steer` | **the steering locator**: a recurring entry that later diverges names a moment where the entries still agree and a productive write of `star(cellOf ·)` lands strictly between the visits — steering is never anonymous |
| `mouth_entry_productive` / `mouth_delivery_lobe` | mouth crossings are always productive; deliveries across a mouth hand out the entered cell's own lobe slots (witness + involution) |
| `quiet_mouth_unreachable` | **the quiet mouth is unreachable**: no productive-free stretch can lead from a cell to its mouth partner — the quiet path is forced to be its own `bar`-reflection (the machine-level retrace), whose middle is a `star` fixed point or an unproductive mouth crossing, both impossible |
| `read_back_productive` / `lone_write_no_mouth` | **a lone alternating cell cannot steer itself**: reading a cell's variation back costs a productive step in between, and a walk whose every productive write lands in its start cell can *never* reach that cell's mouth partner — for every machine, every run, every `N` |

**`TrackFiniteAlternation.lean` / `TrackEndpointMatching.lean` — the exact
finite raw target.**  A productive raw pass is proved to be precisely an
unmatched-endpoint pivot.  First productive writers contribute at most `N`
novel vectors, so the open sharp problem is isolated as
`FiveRepeatedWriterNovelty`: every finite prefix has at most five globally
novel productive rewrites by an already-used writer.  The proved theorem
`stateLaw_of_fiveRepeatedWriterNovelty` closes the actual `StateLaw` from that
single proposition; the proposition itself remains **OPEN**.

**`TrackCurveGrowth.lean` — selected-curve monotonicity.**  `CurveEdge` and
`CurveReach` model the curves formed by ordinary track edges and the currently
selected stem–branch passages.  `unmatched_pivot_strict_curve_growth` proves
that a productive non-self pivot preserves the complete old train curve and
strictly adds the switch stem.  This formalizes the curve-shrinking invariant;
the complementary self-pivot nesting case is still the transient obstacle.

**`KoizumiCurveInvariant.lean` — finite empty-curve descent.**  The selected
internal matching is symmetric, the resulting curve graph has degree at most
two, and `flipAt_is_curve_endpoint_pivot` identifies the exact local surgery.
For an extracted `TrainFreeCurveShrinkHistory`,
`trainFreeCurve_affects_le_switches` gives at most `N` strict replacements and
`no_infinite_trainFreeCurve_shrink` rules out an infinite descent.  Extracting
that history uniformly from raw trajectories—and charging self-pivots before
later merges—remains open.

**`KoizumiRawExtraction.lean` / `TrackCurveShrinkGlobal.lean` — raw curve
surgery and its finite budget.**  Every productive `stepN` event is now
classified as either a self-pivot or strict growth of the selected train
curve.  Nonproductive live steps preserve that curve exactly.  Consequently,
any finite live prefix in which all productive pivots are non-self contains at
most `3*N` productive pivots.  This is unconditional general-`N` progress, but
does not yet control self-pivot epochs.

**`RepeatedNoveltyDecomposition.lean` / `SharpStateLawAssembly.lean` — the
raw sharp residual.**  A globally novel repeated writer has a last-writer
frame and an interior rerouter; choosing a changed coordinate yields a fresh
or interlacing rerouting frame with immutable stem successors.  The exact open
known-edge statement is `KnownEdgeFourRepeatedWriterNovelty`: five such novel
closing frames cannot coexist.  That proposition implies the public `N+6`
`StateLaw`, but it is not asserted as proved.

**`TripleInterlacementObstruction.lean` — cyclic-minimal crossing
obstruction.**  In an irreflexive physical wiring, a certified cyclic-minimal
endpoint-empty `ABCABC` restoration pattern forces either a lobe or an earlier
complete-state replay.  The theorem is compiled and unconditional under its
explicit recurrence/minimality hypotheses.  Extracting those certificates
from every finite raw novelty history is still the global gap.

**`RunwayHistoricalThree.lean` — the local runway residual is closed.**
When the first corner of the explicit four-phase runway/candy cover is already
historical, at most three phases can be globally fresh.  Both intersecting and
disjoint changed-forward merges therefore manufacture an existing
`KnownEdgeSharpRepairCertificate`; their local distinct-state bound is
`N+4`.  This does not itself extract such a merge from every raw run.

**`SelfEpochFour.lean` / `EndpointEpochExtraction.lean` — arbitrary self-only
epochs.**  If every productive write in an interval is a train-curve
self-pivot, the unmatched-branch endpoint carrier can only shrink and contains
at most two switch names.  The extraction theorem chooses those two fixed
writers, proves every other tongue stable, and places the whole interval in
four explicit Gray-square vectors.  Thus any duplicate-free sample from an
arbitrary live self-only epoch has length at most four.  The remaining global
step is to amortize strict self-shrinks against the non-self growth epochs.

**`KoizumiFramePersistence.lean` — repeated writers force self-pivots.**
Selected-curve reachability persists through every step until a productive
self-pivot occurs.  Hence two productive visits to the same switch force a
self-pivot either at the closing visit or strictly between the visits.  A
self-pivot-free prefix has only first writers and therefore at most `N+1`
distinct restricted tongue vectors.

**`UnlinkedCounterObstruction.lean` — reusable-counter audit.**  A raw step
changes at most one independent tongue; same-mouth switch-simple calls become
idempotent, while repaired two-reflector tails have the existing four-state
bound.  In particular, the raw model cannot realize the mechanically linked
updates used by exponential cooperative-point layouts.  The general
`26*N+3` theorem also rules out a reusable binary counter above that capacity;
this audit does not by itself prove the sharper `N+6` law.

**`StateLaw.lean` — the target theorem, in the language of tracks and
switches.**  `GeneralN.StateLaw` states the actual claim — a single
train on any `N`-switch lazy-point layout ever sees at most `N + 6`
distinct tongue vectors — directly over `Wiring`/`stepN`, decodable
piece by piece as track, switches and the lazy-point rule.  **It is
OPEN: nothing in this repository proves that coefficient-one bound.**
`GeneralN.state_law_linear_seventeen` proves the identical
raw-track statement with `17*N+5` in place of `N+6`
(superseding the `18*N+3`, `24*N+5` and `26*N+3` predecessors);
`state_law_two_pow` is the older elementary pigeonhole ceiling.  The
remaining problem is the global assembly: every arbitrary repair branch must
be covered by the `N+2` manufactured-prefix history plus at most four tail
vectors without double-charging overlapping support.  The local runway and
candy novelty branches are now discharged; the strict nested-restoration /
raw repeated-writer decomposition is not yet connected to that sharp
certificate.  Closing that assembly would
improve `17*N+5` to `N+6` (the conjectured sharp form remains `N+4`).

**`VectorCount.lean` — the unconditional ceiling, f(N) ≤ 2^N**: a real
pigeonhole proof (induction on N, splitting on the first coordinate),
no `native_decide`:

| theorem | statement |
|---|---|
| `pigeonhole` | a duplicate-free list of length-N boolean vectors has at most 2^N elements |
| `vector_count_le` / `trajectory_count_le` | **no run of any N-switch wiring, of any length, visits more than 2^N distinct tongue vectors** |

The remaining unproved core of the full cycle theorem is two lemmas
about the echo machine (see ../lazy-point-theory.md): **B** (every
machine cycle has Σ(σ−1) ≤ 2 — this is C\*) and **C** (O(1) transient
alternations).  Modulo B + C, the accounting theorem closes the state
count to f(N) ≤ N + O(1); unconditionally, f(N) ≤ min(2^N, N + 1 + A)
with A the run's alternation count.  The lobed case of B is proved
outright (`absorb`).  The eventual cycle itself is no longer
hypothetical: `Periodicity.run_rho` proves every run enters one, with
explicit bounds, periodic registers, and conserved tokens on the tail.
On that cycle the single-mouth case is now dead:
`LoneWriter.rho_quiet_or_two_mouths` proves every cycle is quiet or
steered from ≥ 2 cells — a lone alternating cell freezes outright.
The pedigree/conservation theorems reduce B to a
single sharp question: the cycle's conserved, repertoire-spanning
token population (`recurrence_emission` + `future_register`) — can
**three or more** of its tokens actually be consumed on the cycle?
Every exhaustion says no (profiles `()` and `(2,2)` only).  B and C are exhaustively verified across all
machines with ≤ 6 cells and ≤ 10 slots — 10.4M runs — plus climbs at
8–12 cells (max actives 2, max transient alternations 1, everywhere;
every cycle's σ-profile is `()` or `(2,2)` — functional collapse or the
dogbone Gray square, never a lone alternating tree, never three).

**`DuplotrainProofs.lean` — exhaustive small-N theorems** (`native_decide`):
the wiring enumerator, the perfection automaton (reflecting caps) and the
state-counting automaton (fall-off caps, including port-entry starts).

Verified by `native_decide`:

| theorem | statement |
|---|---|
| `no_perfect_three` / `no_perfect_four` | no connected 3- or 4-switch wiring is perfectly looping |
| `unique_perfect_one` / `unique_perfect_two` | the teardrop and the dogbone are the unique perfect wirings |
| `states_one..four` | max distinct tongue vectors = 2, 4, 7, 8 = min(2^N, N+4) |
| `cycle_cap_two..four` | eventual cycles carry at most 4 tongue vectors (the Gray square) |
| `count_two..four` | enumeration sizes 76 / 2,620 / 140,152 |

Build: `lake build` (needs elan; toolchain pinned in `lean-toolchain`).
The n ≤ 3 theorems check in seconds; the four n = 4 exhaustions bring the
full build to ~12 minutes.

Scope note: the theorems quantify over `allWirings n` as defined by the
enumerator; its completeness is by construction of the pairing recursion,
cross-checked by the count theorems. Formalising enumerator completeness
itself is the natural next step.
