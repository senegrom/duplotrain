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
      have hn : n ≤ recorded.length := by omega
      have hback := physicalTrace_contact_retraces_prefix
        hrecorded hgrooved hentry hcontact
      have hback' : PhysicalTrace w (p, u)
          ([(p, oldEntry)] ++ reversePassages recorded) (e, v) := by
        simpa using hback
      obtain ⟨middle, hfirst, hreverse⟩ := hback'.split_append
      have hone : stepN w 1 (p, u) = some middle := by
        simpa using hfirst.sound
      have honeStep : step w (p, u) = some middle := by
        simpa [stepN] using hone
      have hmiddleTongues : middle.2 = v := by
        have hparts := step_some_parts honeStep
        calc
          middle.2 = arrivedTongues (p, u) := hparts.2
          _ = v := by simp [arrivedTongues, hcontact]
      have hmiddle : middle = (middle.1, v) := by
        apply Prod.ext
        · rfl
        · exact hmiddleTongues
      rw [hmiddle] at hone hreverse
      have hreverseGrooved :
          PassagesGrooved v (reversePassages recorded) :=
        reversePassages_grooved hgrooved
      have hnReverse : n ≤ (reversePassages recorded).length := by
        rw [reversePassages_length]
        exact hn
      obtain ⟨port, htail⟩ :=
        hreverse.grooved_prefix_tongues v hreverseGrooved hnReverse
      refine ⟨port, ?_⟩
      have hsum : n + 1 = 1 + n := by omega
      have hrun : stepN w (n + 1) (p, u) = some (port, v) := by
        rw [hsum, stepN_add, hone]
        exact htail
      simpa using hrun

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
