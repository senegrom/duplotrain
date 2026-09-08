import VectorCount
import TrackNovelReplay

/-!
# Restricted-vector covers and finite sample counts

A cover separates already historical vectors from a bounded list of new
vectors. Distinct samples cannot outnumber the cover. A dead horizon also
bounds distinct live samples by the number of preceding times.
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


/-- If the train is off-track at time `L`, a list of live sample times whose
restricted tongue vectors are pairwise distinct has length at most `L`.

The conclusion is positional, not dynamical: every live sample lies in the
finite interval `[0,L)`, and vector-nodup implies time-nodup. -/
theorem dead_horizon_live_distinct_le
    {w : Wiring} {N L : Nat} {start : Nat × Tongues}
    (hdead : stepN w L start = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ L := by
  have htimesNodup : times.Nodup :=
    List.Pairwise.of_map (restrictedTonguesAt w N start)
      (fun _ _ hne hEq => hne (congrArg _ hEq)) hnd
  have hlt : ∀ k ∈ times, k < L := by
    intro k hk
    by_cases hsmall : k < L
    · exact hsmall
    · have hkLive := hlive k hk
      rw [show k = L + (k - L) by omega, stepN_add, hdead] at hkLive
      simp at hkLive
  exact nodup_nat_lt_length htimesNodup hlt

end GeneralN
