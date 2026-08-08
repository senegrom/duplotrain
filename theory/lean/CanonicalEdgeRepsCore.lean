import EndpointAccountingStandalone

/-!
# Canonical finite jump-edge representatives

For a duplicate-free finite slot list closed under `bar`, with no fixed
endpoints, keep exactly the slots satisfying `s < bar s`.  The resulting list
contains one representative per edge and has a duplicate-free two-endpoint
expansion.
-/

namespace Echo

variable (m : Machine)

/-- Ordered edge representatives. -/
def canonicalEdgesCore (slots : List Nat) : List Nat :=
  slots.filter (fun s => s < m.bar s)

theorem mem_canonicalEdgesCore_iff {slots : List Nat} {s : Nat} :
    s ∈ canonicalEdgesCore m slots ↔
      s ∈ slots ∧ s < m.bar s := by
  simp [canonicalEdgesCore]

theorem canonicalEdgesCore_nodup {slots : List Nat}
    (hnd : slots.Nodup) :
    (canonicalEdgesCore m slots).Nodup := by
  exact hnd.filter _

/-- Endpoint membership identifies a represented edge. -/
theorem core_mem_edgeEnds_cases
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

/-- An edge representative and its opposite endpoint occur in the endpoint
expansion. -/
theorem core_rep_endpoints_mem :
    ∀ {edges : List Nat} {s : Nat}, s ∈ edges →
      s ∈ standaloneEdgeEnds m edges ∧
        m.bar s ∈ standaloneEdgeEnds m edges := by
  intro edges s hs
  induction edges generalizing s with
  | nil => cases hs
  | cons x rest ih =>
      simp only [List.mem_cons] at hs
      rcases hs with hxs | hs
      · subst s
        simp [standaloneEdgeEnds]
      · have ht := ih hs
        constructor
        · exact List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ ht.1)
        · exact List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ ht.2)

/-- Ordered duplicate-free representatives have duplicate-free endpoints. -/
theorem orderedEdgeEndsCore_nodup :
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
        · rcases core_mem_edgeEnds_cases m hm with
            ⟨t, ht, hst | hst⟩
          · apply hnd.1
            simpa [hst] using ht
          · have htlt := hrestOrd t ht
            have hbars : m.bar s = t := by
              calc
                m.bar s = m.bar (m.bar t) :=
                  congrArg m.bar hst
                _ = t := m.bar_invol t
            have hstlt : s < t := by
              calc
                s < m.bar s := hslt
                _ = t := hbars
            have hts : t < s := by
              calc
                t < m.bar t := htlt
                _ = s := hst.symm
            omega
      · intro hm
        rcases core_mem_edgeEnds_cases m hm with
          ⟨t, ht, hst | hst⟩
        · have htlt := hrestOrd t ht
          have hbt : m.bar t = s := by
            have hb := congrArg m.bar hst
            simpa [m.bar_invol] using hb.symm
          have hts : m.bar s < s := by
            calc
              m.bar s = t := hst
              _ < m.bar t := htlt
              _ = s := hbt
          omega
        · have heq : s = t := by
            have hb := congrArg m.bar hst
            simpa [m.bar_invol] using hb
          apply hnd.1
          simpa [heq] using ht

/-- Canonical endpoint expansion is duplicate-free. -/
theorem canonicalEdgeEndsCore_nodup {slots : List Nat}
    (hnd : slots.Nodup) :
    (standaloneEdgeEnds m (canonicalEdgesCore m slots)).Nodup := by
  apply orderedEdgeEndsCore_nodup m
    (canonicalEdgesCore m slots)
    (canonicalEdgesCore_nodup m hnd)
  intro s hs
  have hs' : s ∈ slots ∧ s < m.bar s := by
    simpa [canonicalEdgesCore] using hs
  exact hs'.2

/-- Every original slot has a canonical same-edge representative. -/
theorem slot_has_canonicalEdgeCore
    {slots : List Nat}
    (hclosed : ∀ s ∈ slots, m.bar s ∈ slots)
    (hfixed : ∀ s ∈ slots, m.bar s ≠ s)
    {s : Nat} (hs : s ∈ slots) :
    ∃ g, g ∈ canonicalEdgesCore m slots ∧ SameEdge m s g := by
  by_cases hlt : s < m.bar s
  · refine ⟨s, ?_, Or.inl rfl⟩
    simpa [canonicalEdgesCore, hs, hlt]
  · have hbarMem := hclosed s hs
    have hbarLt : m.bar s < s := by
      have hle : m.bar s ≤ s := Nat.le_of_not_gt hlt
      have hne : m.bar s ≠ s := hfixed s hs
      omega
    have hbarOrdered : m.bar s < m.bar (m.bar s) := by
      simpa [m.bar_invol] using hbarLt
    refine ⟨m.bar s, ?_, Or.inr rfl⟩
    simpa [canonicalEdgesCore, hbarMem, hbarOrdered]

/-- Every original slot occurs in the endpoint expansion. -/
theorem slot_mem_canonicalEdgeEndsCore
    {slots : List Nat}
    (hclosed : ∀ s ∈ slots, m.bar s ∈ slots)
    (hfixed : ∀ s ∈ slots, m.bar s ≠ s)
    {s : Nat} (hs : s ∈ slots) :
    s ∈ standaloneEdgeEnds m (canonicalEdgesCore m slots) := by
  rcases slot_has_canonicalEdgeCore m hclosed hfixed hs with
    ⟨g, hg, hsg⟩
  have hends := core_rep_endpoints_mem m hg
  rcases hsg with hsg | hsg
  · simpa [hsg] using hends.1
  · have hb := hends.2
    simpa [hsg, m.bar_invol] using hb

/-- Every canonical endpoint lies in the original bar-closed list. -/
theorem canonicalEdgeEndsCore_mem_slots
    {slots : List Nat}
    (hclosed : ∀ s ∈ slots, m.bar s ∈ slots)
    {x : Nat}
    (hx : x ∈ standaloneEdgeEnds m (canonicalEdgesCore m slots)) :
    x ∈ slots := by
  rcases core_mem_edgeEnds_cases m hx with ⟨s, hs, hcase⟩
  have hs' : s ∈ slots ∧ s < m.bar s := by
    simpa [canonicalEdgesCore] using hs
  rcases hcase with hxs | hxs
  · rw [hxs]
    exact hs'.1
  · rw [hxs]
    exact hclosed s hs'.1

end Echo
