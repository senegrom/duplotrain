import VectorCount
import TrackNovelReplay

/-!
# Novelty covers for completed physical retraces

`TrackNovelReplay` proves the pointwise fact behind novelty accounting: once
a train contacts the exit of an old grooved physical trace, every positive
time on the completed reverse traversal carries the one contact tongue
vector.

This file packages that fact as an exact cover and as a counting theorem.
The semantic premise `PassagesGrooved v recorded` is essential.  Mere switch
simplicity of the old trace does not imply that an arbitrary contact vector
still grooves it, so no theorem below hides that premise.

The global coefficient-one state law remains open.  What is closed here is
the local step needed by a global four-novelty argument: a completed retrace
whose initial vector is already historical contributes at most one genuinely
new restricted tongue vector, regardless of the length of the retraced path.
-/

namespace GeneralN

/-- The first `N` tongue bits at time `k` of a run. -/
def restrictedTonguesAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : List Bool :=
  VectorCount.restrict N (tonguesAt w start k)

/-- On the selected times, every restricted tongue vector is either already
in `history` or belongs to a list of at most `budget` exceptional vectors. -/
def NoveltyCoverOn (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (times : List Nat) (history : List (List Bool)) (budget : Nat) : Prop :=
  ∃ fresh : List (List Bool),
    fresh.length ≤ budget ∧
    ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history ++ fresh

/-- A novelty cover converts directly into a count of distinct sampled
vectors.  This is the generic final bookkeeping step of a novelty proof. -/
theorem noveltyCoverOn_distinct_count
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat} {history : List (List Bool)} {budget : Nat}
    (hcover : NoveltyCoverOn w N start times history budget)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ history.length + budget := by
  obtain ⟨fresh, hfreshLength, hmem⟩ := hcover
  have hsubset :
      ∀ x ∈ times.map (restrictedTonguesAt w N start),
        x ∈ history ++ fresh := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact hmem k hk
  have hbound := nodup_subset_length_nat hnd hsubset
  simp only [List.length_map, List.length_append] at hbound
  omega


/-- The with-extra form: one additional historical vector is counted on top
of a cover, provided the extended sample list is duplicate-free. -/
theorem noveltyCoverOn_distinct_count_with_extra
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat} {history : List (List Bool)} {budget : Nat}
    (hcover : NoveltyCoverOn w N start times history budget)
    {extra : List Bool} (hextra : extra ∈ history)
    (hnd : (extra :: times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length + 1 ≤ history.length + budget := by
  obtain ⟨fresh, hfreshLength, hmem⟩ := hcover
  have hsubset :
      ∀ x ∈ extra :: times.map (restrictedTonguesAt w N start),
        x ∈ history ++ fresh := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_append_left _ hextra
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact hmem k hk
  have hbound := nodup_subset_length_nat hnd hsubset
  simp only [List.length_cons, List.length_map,
    List.length_append] at hbound
  omega


theorem completed_retrace_at_vector_mem_history_or_contact
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some (p, u))
    (N : Nat) (history : List (List Bool))
    (hu : VectorCount.restrict N u ∈ history)
    {j : Nat} (hlower : K ≤ j)
    (hupper : j ≤ K + recorded.length + 1) :
    restrictedTonguesAt w N start j ∈ history ∨
      restrictedTonguesAt w N start j =
        VectorCount.restrict N v := by
  let d := j - K
  have hd : d ≤ recorded.length + 1 := by
    dsimp [d]
    omega
  obtain ⟨port, hlocal⟩ :=
    (physicalTrace_contact_retraces_prefix_pointwise
      hrecorded hgrooved hentry hcontact).2 d hd
  have hj : j = K + d := by
    dsimp [d]
    omega
  have hglobal :
      stepN w j start =
        some (port, if d = 0 then u else v) := by
    rw [hj, stepN_add, hreach]
    exact hlocal
  have hvector :
      restrictedTonguesAt w N start j =
        VectorCount.restrict N (if d = 0 then u else v) := by
    simp [restrictedTonguesAt, tonguesAt, hglobal]
  by_cases hzero : d = 0
  · left
    rw [hvector, if_pos hzero]
    exact hu
  · right
    rw [hvector, if_neg hzero]
end GeneralN
