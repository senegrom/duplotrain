import ExternalLobeReflectionCore

/-!
# The paired-router roundtrip

The extremal static configuration for the `2/3` component estimate has one
non-reflecting router cell in each support component, with all remaining cells
carrying external lobe reflectors.  Mouth pairing makes the two routers read
one another.

This configuration is itself a trap.  If router `u` currently stores support
slot `s` and its mouth partner stores `t`, then the walk is

    s at u
      -> bar t in the partner component
      -> external lobe
      -> t at star u
      -> bar s in the original component
      -> external lobe
      -> s at u.

Thus the support entry returns after six echo steps.  The theorem below
isolates the exact register-machine calculation; component separation is
packaged as the hypothesis that the first three intervening writes do not
write `u`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Paired-router six-step roundtrip.** -/
theorem paired_router_roundtrip
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k s t : Nat}
    (hstart : e k = s)
    (ht : reg m e r0 k (m.star (m.cellOf s)) = t)
    (hreflectB : LobeEntryAt m e (k+2))
    (hreflectA : LobeEntryAt m e (k+5))
    (hnoU : ∀ i, k < i → i ≤ k+3 →
      m.cellOf (e i) ≠ m.cellOf s) :
    e (k+1) = m.bar t ∧
    e (k+3) = t ∧
    e (k+4) = m.bar s ∧
    e (k+6) = s := by
  have h1 : e (k+1) = m.bar t := by
    rw [hrun k, hstart, ht]
  have h3raw := lobe_entry_reflects
    m e r0 hrun hr0 (k := k+1) hreflectB
  have h3 : e (k+3) = t := by
    rw [h1, m.bar_invol] at h3raw
    exact h3raw
  have hwriteU : reg m e r0 k (m.cellOf s) = s := by
    apply reg_write m e r0
    rw [hstart]
  have hstableU :
      reg m e r0 (k+3) (m.cellOf s) =
        reg m e r0 k (m.cellOf s) := by
    have h := reg_stable m e r0 (i := k)
      (c := m.cellOf s) 3
      (fun i hi hbound => hnoU i hi (by omega))
    simpa using h
  have htCell : m.cellOf t = m.star (m.cellOf s) := by
    rw [← ht]
    exact reg_cell m e r0 hr0 k (m.star (m.cellOf s))
  have h4 : e (k+4) = m.bar s := by
    calc
      e (k+4) = m.bar
          (reg m e r0 (k+3)
            (m.star (m.cellOf (e (k+3))))) := hrun (k+3)
      _ = m.bar (reg m e r0 (k+3) (m.cellOf s)) := by
            rw [h3, htCell, m.star_invol]
      _ = m.bar s := by rw [hstableU, hwriteU]
  have h6raw := lobe_entry_reflects
    m e r0 hrun hr0 (k := k+4) hreflectA
  have h6 : e (k+6) = s := by
    rw [h4, m.bar_invol] at h6raw
    exact h6raw
  exact ⟨h1, h3, h4, h6⟩

/-- The same theorem with the partner register named internally. -/
theorem paired_router_roundtrip_current
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k s : Nat}
    (hstart : e k = s)
    (hreflectB : LobeEntryAt m e (k+2))
    (hreflectA : LobeEntryAt m e (k+5))
    (hnoU : ∀ i, k < i → i ≤ k+3 →
      m.cellOf (e i) ≠ m.cellOf s) :
    let t := reg m e r0 k (m.star (m.cellOf s))
    e (k+1) = m.bar t ∧
    e (k+3) = t ∧
    e (k+4) = m.bar s ∧
    e (k+6) = s := by
  intro t
  exact paired_router_roundtrip m e r0 hrun hr0
    hstart rfl hreflectB hreflectA hnoU

end Echo
