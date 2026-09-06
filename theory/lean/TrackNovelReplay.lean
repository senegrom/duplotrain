import TrackTheta

/-!
# Pointwise novelty control for a completed reverse frame

The endpoint theorem `physicalTrace_contact_retraces_prefix` says that a
contact with the exit of an old grooved prefix traverses that prefix in
reverse.  This file records the pointwise strengthening needed for novelty
counting: after the contact step, every intermediate configuration on that
reverse traversal has exactly the contact tongue vector.

Everything here is over the raw `Wiring` / `stepN` dynamics and is valid for
an arbitrary number of switches.
-/

namespace GeneralN

/-- Every prefix of a grooved physical trace runs with the specified tongue
vector.  The endpoint port is intentionally existential: novelty accounting
cares about the complete tongue vector, not the particular plain-track edge.
-/
theorem PhysicalTrace.grooved_prefix_tongues
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (state : Tongues)
    (hgrooved : PassagesGrooved state passages)
    {d : Nat} (hd : d ≤ passages.length) :
    ∃ port, stepN w d (start.1, state) = some (port, state) := by
  have htrace' : PhysicalTrace w start
      (passages.take d ++ passages.drop d) finish := by
    simpa only [List.take_append_drop] using htrace
  obtain ⟨middle, hprefix, _hsuffix⟩ := htrace'.split_append
  have hprefixGrooved : PassagesGrooved state (passages.take d) := by
    intro passage hp
    exact hgrooved passage (List.mem_of_mem_take hp)
  have hreplay := hprefix.replay_grooved state hprefixGrooved
  have hsound := hreplay.sound
  rw [List.length_take_of_le hd] at hsound
  exact ⟨middle.1, hsound⟩

/-- Any nonempty closed spatial route grooved at `state` runs forever with
that vector. The recorded witness need not be simple or have equal endpoints. -/
theorem PhysicalTrace.grooved_loop_all_time
    {w : Wiring} {p : Nat} {u v state : Tongues} {route : List Passage}
    (htrace : PhysicalTrace w (p, u) route (p, v))
    (hpositive : 0 < route.length) (hgrooved : PassagesGrooved state route)
    (d : Nat) : ∃ port, stepN w d (p, state) = some (port, state) := by
  obtain ⟨port, phase, hr, hp⟩ := htrace.spatial_loop_invariant
    (fun current => current = state) hpositive
    (by
      intro passage hmem current heq
      subst current
      exact ⟨state, groove_forward (hgrooved passage hmem), rfl⟩) rfl d
  exact ⟨port, by simpa only [hp] using hr⟩

/-- A backward contact and replay close a grooved loop at the post-contact
vector. The original run synchronizes with that stable loop at its first
step; no transient-lap or modular-time analysis is needed. -/
theorem backward_contact_all_time_two_phase
    {w : Wiring} {g e p oldEntry : Nat}
    {oldBase oldEnd u v : Tongues} {recorded approach : List Passage}
    (hrecorded : PhysicalTrace w (g, oldBase) recorded (oldEntry, oldEnd))
    (hrecordedGrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (happroach : PhysicalTrace w (e, u) approach (p, u))
    (happroachGrooved : PassagesGrooved v approach) :
    ∀ m, ∃ port phase, stepN w m (p, u) = some (port, phase) ∧
      (phase = u ∨ phase = v) := by
  have hback := physicalTrace_contact_retraces_prefix
    hrecorded hrecordedGrooved hentry hcontact
  have hforward := happroach.replay_grooved v happroachGrooved
  let cycle := (p, oldEntry) :: reversePassages recorded ++ approach
  have hcycle : PhysicalTrace w (p, u) cycle (p, v) := by
    simpa [cycle, List.append_assoc] using hback.append hforward
  have hgrooved : PassagesGrooved v cycle := by
    intro passage hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simpa only [hcontact] using arrive_back u p
    · rcases List.mem_append.mp hp with hp | hp
      · exact reversePassages_grooved hrecordedGrooved passage hp
      · exact happroachGrooved passage hp
  intro m
  cases m with
  | zero => exact ⟨p, u, rfl, Or.inl rfl⟩
  | succ n =>
      obtain ⟨port, hr⟩ := hcycle.grooved_loop_all_time (by simp [cycle]) hgrooved (n + 1)
      exact ⟨port, v, (stepN_after_arrival hcontact (by omega)).trans hr, Or.inr rfl⟩

/-- Pointwise completed-retrace novelty theorem.

At depth zero the original tongue vector is still present.  At every depth
from the contact step through the final reverse passage (inclusive), the
tongue vector is exactly `v`.  Moreover the contact either changed no tongue
or flipped exactly the tongue of the contacted switch.
-/
theorem physicalTrace_contact_retraces_prefix_pointwise
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v)) :
    (v = u ∨ v = flipAt u (p / 3)) ∧
      ∀ d, d ≤ recorded.length + 1 →
        ∃ port, stepN w d (p, u) =
          some (port, if d = 0 then u else v) := by
  have hcontactShape : v = u ∨ v = flipAt u (p / 3) := by
    by_cases hchanged : v (p / 3) ≠ u (p / 3)
    · exact Or.inr (changed_arrival_eq_flipAt hcontact hchanged)
    · left
      have hsame : v (p / 3) = u (p / 3) := by
        cases hv : v (p / 3) <;> cases hu : u (p / 3) <;>
          simp_all
      funext j
      by_cases hj : j = p / 3
      · simpa [hj] using hsame
      · exact arrive_preserves_other hcontact hj
  refine ⟨hcontactShape, ?_⟩
  intro d hd
  cases d with
  | zero =>
      exact ⟨p, by simp [stepN]⟩
  | succ n =>
      have hback := physicalTrace_contact_retraces_prefix hrecorded hgrooved hentry hcontact
      have hallGrooved : PassagesGrooved v ((p, oldEntry) :: reversePassages recorded) := by
        intro passage hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simpa only [hcontact] using arrive_back u p
        · exact reversePassages_grooved hgrooved passage hp
      obtain ⟨port, hr⟩ := hback.grooved_prefix_tongues v hallGrooved
        (by simpa only [List.length_cons, reversePassages_length] using hd)
      exact ⟨port, by simpa using (stepN_after_arrival hcontact (by omega)).trans hr⟩

/-- Positive-time projection of
`physicalTrace_contact_retraces_prefix_pointwise`: every configuration from
the contact through the end of the reverse traversal has tongue vector `v`.
-/
theorem physicalTrace_contact_retraces_prefix_positive
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    {d : Nat} (hpos : 1 ≤ d) (hd : d ≤ recorded.length + 1) :
    ∃ port, stepN w d (p, u) = some (port, v) := by
  obtain ⟨port, hrun⟩ :=
    (physicalTrace_contact_retraces_prefix_pointwise
      hrecorded hgrooved hentry hcontact).2 d hd
  have hd0 : d ≠ 0 := by omega
  exact ⟨port, by simpa [hd0] using hrun⟩

end GeneralN
