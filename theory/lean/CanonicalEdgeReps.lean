import EndpointAccountingStandalone

/-!
# Canonical representatives of finite jump edges

Given a duplicate-free finite slot list closed under `bar`, with no fixed
`bar` endpoints, retain precisely the slots satisfying `s < bar s`.  This gives
exactly one representative from each jump edge.  Its two-endpoint expansion is
duplicate-free, every original slot belongs to a represented edge, and every
represented endpoint remains in the original slot list.
-/

namespace Echo

variable (m : Machine)

/-- One ordered representative per jump edge. -/
def canonicalEdgeReps (slots : List Nat) : List Nat :=
  slots.filter (fun s => s < m.bar s)

/-- Membership implies original membership and the ordering property. -/
theorem mem_canonicalEdgeReps_iff {slots : List Nat} {s : Nat} :
    s ∈ canonicalEdgeReps m slots ↔
      s ∈ slots ∧ s < m.bar s := by
  simp [canonicalEdgeReps]

/-- Canonical representatives remain duplicate-free. -/
theorem canonicalEdgeReps_nodup {slots : List Nat}
    (hnd : slots.Nodup) :
    (canonicalEdgeReps m slots).Nodup := by
  exact hnd.filter _

/-- Recover the represented edge from endpoint-list membership. -/
theorem canonical_mem_edgeEnds_cases
    {edges : List Nat} {x : Nat} :
    x ∈ standaloneEdgeEnds m edges →
      ∃ s, s ∈ edges ∧ (x = s ∨ x = m.bar s) := by
  induction edges with
  | nil => simp [standaloneEdgeEnds]
  | cons s rest ih =>
      intro hx
      simp only [standaloneEdgeEnds, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨s, List.mem_cons_self, Or.inl rfl⟩
      · rcases hx with rfl | hx
        · exact ⟨s, List.mem_cons_self, Or.inr rfl⟩
        · rcases ih hx with ⟨t, ht, hxt⟩
          exact ⟨t, List.mem_cons_of_mem _ ht, hxt⟩

/-- Ordered, duplicate-free representatives have duplicate-free endpoint
expansion. -/
theorem orderedEdgeEnds_nodup :
    ∀ edges : List Nat,
      edges.Nodup →
      (∀ s ∈ edges, s < m.bar s) →
      (standaloneEdgeEnds m edges).Nodup := by
  intro edges
  induction edges with
  | nil =>
      intro _ _
      simp [standaloneEdgeEnds]
  | cons s rest ih =>
      intro hnd hord
      rw [List.nodup_cons] at hnd
      have hslt := hord s List.mem_cons_self
      have hrestOrd : ∀ t ∈ rest, t < m.bar t := by
        intro t ht
        exact hord t (List.mem_cons_of_mem _ ht)
      have htail := ih hnd.2 hrestOrd
      rw [standaloneEdgeEnds, List.nodup_cons, List.nodup_cons]
      refine ⟨?_, ?_, htail⟩
      · intro hm
        simp only [List.mem_cons] at hm
        rcases hm with heq | hm
        · omega
        · rcases canonical_mem_edgeEnds_cases m hm with
            ⟨t, ht, hst | hst⟩
          · exact hnd.1 (hst ▸ ht)
          · have htlt := hrestOrd t ht
            have hbars : m.bar s = t := by
              calc
                m.bar s = m.bar (m.bar t) := by rw [hst]
                _ = t := m.bar_invol t
            have hstlt : s < t := by
              simpa [hbars] using hslt
            have hts : t < s := by
              simpa [← hst] using htlt
            omega
      · intro hm
        rcases canonical_mem_edgeEnds_cases m hm with
          ⟨t, ht, hst | hst⟩
        · have htlt := hrestOrd t ht
          have hts : m.bar s < s := by
            calc
              m.bar s = t := hst
              _ < m.bar t := htlt
              _ = s := by
                have hb := congrArg m.bar hst
                simpa [m.bar_invol] using hb.symm
          omega
        · have heq : s = t := by
            have hb := congrArg m.bar hst
            simpa [m.bar_invol] using hb
          exact hnd.1 (heq ▸ ht)

/-- Canonical representatives have duplicate-free endpoint expansion. -/
theorem canonicalEdgeEnds_nodup {slots : List Nat}
    (hnd : slots.Nodup) :
    (standaloneEdgeEnds m (canonicalEdgeReps m slots)).Nodup := by
  apply orderedEdgeEnds_nodup m (canonicalEdgeReps m slots)
    (canonicalEdgeReps_nodup m hnd)
  intro s hs
  exact (mem_canonicalEdgeReps_iff.mp hs).2

/-- Every slot is represented by one canonical edge. -/
theorem slot_has_canonical_rep
    {slots : List Nat}
    (hclosed : ∀ s ∈ slots, m.bar s ∈ slots)
    (hfixed : ∀ s ∈ slots, m.bar s ≠ s)
    {s : Nat} (hs : s ∈ slots) :
    ∃ g, g ∈ canonicalEdgeReps m slots ∧ SameEdge m s g := by
  by_cases hlt : s < m.bar s
  · exact ⟨s, mem_canonicalEdgeReps_iff.mpr ⟨hs, hlt⟩,
      Or.inl rfl⟩
  · have hbarMem := hclosed s hs
    have hbarLt : m.bar s < s := by
      have hle : m.bar s ≤ s := Nat.le_of_not_gt hlt
      have hne : m.bar s ≠ s := hfixed s hs
      omega
    have hbarOrdered : m.bar s < m.bar (m.bar s) := by
      simpa [m.bar_invol] using hbarLt
    exact ⟨m.bar s,
      mem_canonicalEdgeReps_iff.mpr ⟨hbarMem, hbarOrdered⟩,
      Or.inr rfl⟩

/-- Every canonical endpoint lies in the original bar-closed slot list. -/
theorem canonicalEdgeEnds_mem_slots
    {slots : List Nat}
    (hclosed : ∀ s ∈ slots, m.bar s ∈ slots)
    {x : Nat}
    (hx : x ∈ standaloneEdgeEnds m (canonicalEdgeReps m slots)) :
    x ∈ slots := by
  rcases canonical_mem_edgeEnds_cases m hx with
    ⟨s, hs, rfl | rfl⟩
  · exact (mem_canonicalEdgeReps_iff.mp hs).1
  · exact hclosed s (mem_canonicalEdgeReps_iff.mp hs).1

/-- Every original slot occurs in the canonical endpoint expansion. -/
theorem slot_mem_canonicalEdgeEnds
    {slots : List Nat}
    (hclosed : ∀ s ∈ slots, m.bar s ∈ slots)
    (hfixed : ∀ s ∈ slots, m.bar s ≠ s)
    {s : Nat} (hs : s ∈ slots) :
    s ∈ standaloneEdgeEnds m (canonicalEdgeReps m slots) := by
  rcases slot_has_canonical_rep m hclosed hfixed hs with
    ⟨g, hg, hsg⟩
  induction canonicalEdgeReps m slots with
  | nil => cases hg
  | cons x rest ih =>
      simp only [standaloneEdgeEnds, List.mem_cons]
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · rcases hsg with rfl | hsg
        · exact Or.inl rfl
        · exact Or.inr (Or.inl hsg.symm)
      · exact Or.inr (Or.inr (ih hg))

end Echo
