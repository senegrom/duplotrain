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

/-- A backward contact with the selected route settles into the contact's
 two tongue phases. Both approaches avoid the contacted switch, so the
 arrival preserves every groove needed by the closed retrace. -/
theorem ManufacturedReflector.backward_contact_two_phase
    {w : Wiring} {g e p entry x : Nat} {base u v : Tongues}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths u)
    (hmem : (entry, x) ∈ A.orientedRoute u)
    {approach : List Passage}
    (happroach : PhysicalTrace w (e, base) approach (p, u))
    (hsimple : SwitchSimple (approach ++ [(p, entry)]))
    (hcontact : arrive u p = (entry, v)) :
    ∀ d, ∃ port phase, stepN w d (p, u) = some (port, phase) ∧
      (phase = u ∨ phase = v) := by
  obtain ⟨recorded, tail, hsplit⟩ := List.append_of_mem hmem
  have hroute := A.orientedRoute_trace u hpaths
  have hs := A.orientedRoute_simple u
  have hg := hroute.grooved_of_switchSimple hs
  obtain ⟨_, _, hrecorded, _⟩ := (hsplit ▸ hroute).split_grooved_at (hsplit ▸ hg)
  have hswitch : entry / 3 = p / 3 := by
    simpa only [hcontact] using arrive_exit_switch u p
  have hrecordedV : PassagesGrooved v recorded := by
    apply (show PassagesGrooved u recorded from
      fun passage hp => hg passage (by rw [hsplit]; simp [hp])).transfer
    intro passage hp
    apply arrive_preserves_other hcontact
    rw [hsplit] at hs
    grind [SwitchSimple, passageSwitch]
  have ha := happroach.grooved_of_switchSimple (show SwitchSimple approach by grind [SwitchSimple])
  apply backward_contact_all_time_two_phase hrecorded hrecordedV A.entryEdge hcontact
    (happroach.replay_grooved u ha)
  apply ha.transfer
  intro passage hp
  apply arrive_preserves_other hcontact
  grind [SwitchSimple, passageSwitch]

/-- Pointwise completed-retrace novelty theorem.

At depth zero the original tongue vector is still present.  At every depth
from the contact step through the final reverse passage (inclusive), the
tongue vector is exactly `v`.
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
    ∀ d, d ≤ recorded.length + 1 →
      ∃ port, stepN w d (p, u) =
        some (port, if d = 0 then u else v) := by
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

end GeneralN
