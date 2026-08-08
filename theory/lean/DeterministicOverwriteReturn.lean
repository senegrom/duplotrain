import OverwriteLasso

/-!
# Recurrent deterministic configurations have at most two tongue states

Suppose an abstract configuration sequence is deterministic: equal
configurations replay equal futures.  Each abstract configuration emits a
fixed finite word of branch-pin assignments, and the concrete tongue state is
obtained by executing those words.

Choose the least positive return time `p` of a recurrent configuration.  Every
other return time is a multiple of `p`.  The corresponding period word is an
overwrite map, hence idempotent.  Therefore every positive return to that
configuration has the same concrete tongue vector.  A configuration can carry
at most two vectors over the whole run: its first-visit vector and its
stabilised recurrent vector.
-/

namespace GeneralN

private theorem exists_minimal_positive {P : Nat → Prop} :
    ∀ d : Nat,
      (∃ r, 0 < r ∧ r ≤ d ∧ P r) →
      ∃ p, 0 < p ∧ p ≤ d ∧ P p ∧
        ∀ r, 0 < r → r < p → ¬ P r := by
  intro d
  induction d with
  | zero =>
      intro h
      obtain ⟨r, hr, hrd, _⟩ := h
      omega
  | succ n ih =>
      intro h
      by_cases hprev : ∃ r, 0 < r ∧ r ≤ n ∧ P r
      · obtain ⟨p, hp0, hpn, hPp, hmin⟩ := ih hprev
        exact ⟨p, hp0, by omega, hPp, hmin⟩
      · obtain ⟨r, hr, hrle, hPr⟩ := h
        have hre : r = n + 1 := by
          by_cases hrn : r ≤ n
          · exact False.elim (hprev ⟨r, hr, hrn, hPr⟩)
          · omega
        subst r
        refine ⟨n + 1, by omega, Nat.le_refl _, hPr, ?_⟩
        intro s hs hslt hPs
        apply hprev
        exact ⟨s, hs, by omega, hPs⟩

/-- Iterating one period any number of times preserves a deterministic
periodic sequence. -/
theorem sequence_shift_mul
    {α : Type} (cfg : Nat → α)
    (start period : Nat)
    (hperiod : ∀ r,
      cfg (start + period + r) = cfg (start + r)) :
    ∀ q r,
      cfg (start + q * period + r) = cfg (start + r) := by
  intro q
  induction q with
  | zero =>
      intro r
      simp
  | succ q ih =>
      intro r
      calc
        cfg (start + (q + 1) * period + r)
            = cfg (start + period + (q * period + r)) := by
                congr 1
                rw [Nat.succ_mul]
                omega
        _ = cfg (start + (q * period + r)) :=
          hperiod (q * period + r)
        _ = cfg (start + r) := by
          simpa [Nat.add_assoc] using ih r

/-- Under a least return period, every return offset is a multiple of that
period. -/
theorem return_offset_multiple
    {α : Type} (cfg : Nat → α)
    (start period : Nat)
    (hpos : 0 < period)
    (hperiod : ∀ r,
      cfg (start + period + r) = cfg (start + r))
    (hmin : ∀ r, 0 < r → r < period →
      cfg (start + r) ≠ cfg start)
    {d : Nat}
    (hreturn : cfg (start + d) = cfg start) :
    ∃ q, d = q * period := by
  let q := d / period
  let r := d % period
  have hrlt : r < period := by
    dsimp [r]
    exact Nat.mod_lt d hpos
  have hdecomp : d = q * period + r := by
    dsimp [q, r]
    have h := Nat.mod_add_div d period
    have hc : d / period * period = period * (d / period) :=
      Nat.mul_comm _ _
    omega
  have hreduce := sequence_shift_mul cfg start period hperiod q r
  have hrreturn : cfg (start + r) = cfg start := by
    calc
      cfg (start + r) = cfg (start + q * period + r) :=
        hreduce.symm
      _ = cfg (start + d) := by
        rw [hdecomp]
        congr 1
        omega
      _ = cfg start := hreturn
  have hrzero : r = 0 := by
    by_cases hr : r = 0
    · exact hr
    · exact False.elim
        ((hmin r (by omega) hrlt) hrreturn)
  refine ⟨q, ?_⟩
  rw [hdecomp, hrzero]
  omega

/-- Periodicity from `start` also holds after shifting the start by any whole
number of periods. -/
theorem pinBlock_period_shift_mul
    (actions : Nat → List Nat) (start period : Nat)
    (hperiod : ∀ k, start ≤ k →
      actions (k + period) = actions k) :
    ∀ q len,
      pinBlock actions (start + q * period) len =
        pinBlock actions start len := by
  intro q
  induction q with
  | zero =>
      intro len
      simp
  | succ q ih =>
      intro len
      have hperiodQ : ∀ k, start + q * period ≤ k →
          actions (k + period) = actions k := by
        intro k hk
        exact hperiod k (by omega)
      have hone := pinBlock_period_shift actions
        (start + q * period) period hperiodQ len
      have hidx : start + (q + 1) * period =
          start + q * period + period := by
        rw [Nat.succ_mul]
        omega
      rw [hidx, hone]
      exact ih len

/-- Every positive whole number of traversals of one periodic overwrite block
has the same endpoint. -/
theorem pinTrajectory_positive_period_multiple
    (actions : Nat → List Nat) (t0 : Tongues)
    (start period : Nat)
    (hperiod : ∀ k, start ≤ k →
      actions (k + period) = actions k) :
    ∀ q,
      pinTrajectory actions t0 (start + (q + 1) * period) =
        pinList (pinBlock actions start period)
          (pinTrajectory actions t0 start) := by
  intro q
  induction q with
  | zero =>
      simpa using pinTrajectory_add actions t0 start period
  | succ q ih =>
      let previous := start + (q + 1) * period
      have hadd := pinTrajectory_add actions t0 previous period
      have hblock : pinBlock actions previous period =
          pinBlock actions start period := by
        dsimp [previous]
        exact pinBlock_period_shift_mul actions start period
          hperiod (q + 1) period
      have hidx : start + (q + 1 + 1) * period =
          previous + period := by
        dsimp [previous]
        rw [Nat.succ_mul]
        omega
      rw [hidx, hadd, hblock, ih]
      exact pinList_idempotent
        (pinBlock actions start period)
        (pinTrajectory actions t0 start)

/-- Equal deterministic configurations have equal future configurations. -/
def Replays {α : Type} (cfg : Nat → α) : Prop :=
  ∀ i j, cfg i = cfg j → ∀ r, cfg (i + r) = cfg (j + r)

/-- **All positive returns to one deterministic configuration carry the same
concrete tongue vector.** -/
theorem positive_returns_same_tongues
    {α : Type} (cfg : Nat → α) (actionOf : α → List Nat)
    (t0 : Tongues)
    (hreplay : Replays cfg)
    {start d₁ d₂ : Nat}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hret₁ : cfg (start + d₁) = cfg start)
    (hret₂ : cfg (start + d₂) = cfg start) :
    pinTrajectory (fun k => actionOf (cfg k)) t0 (start + d₁) =
      pinTrajectory (fun k => actionOf (cfg k)) t0 (start + d₂) := by
  let P : Nat → Prop := fun d => cfg (start + d) = cfg start
  obtain ⟨period, hperiodPos, hperiodLe, hperiodRet, hminimal⟩ :=
    exists_minimal_positive (P := P) d₁
      ⟨d₁, hd₁, Nat.le_refl _, hret₁⟩
  have hcfgPeriod : ∀ r,
      cfg (start + period + r) = cfg (start + r) := by
    intro r
    exact (hreplay start (start + period)
      hperiodRet.symm r).symm
  have hactionPeriod : ∀ k, start ≤ k →
      actionOf (cfg (k + period)) = actionOf (cfg k) := by
    intro k hk
    obtain ⟨r, rfl⟩ : ∃ r, k = start + r :=
      ⟨k - start, by omega⟩
    congr 1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hcfgPeriod r
  have hminimal' : ∀ r, 0 < r → r < period →
      cfg (start + r) ≠ cfg start := by
    intro r hr hrp
    exact hminimal r hr hrp
  obtain ⟨q₁, hq₁⟩ := return_offset_multiple
    cfg start period hperiodPos hcfgPeriod hminimal' hret₁
  obtain ⟨q₂, hq₂⟩ := return_offset_multiple
    cfg start period hperiodPos hcfgPeriod hminimal' hret₂
  have hq₁Pos : 0 < q₁ := by
    rcases Nat.eq_zero_or_pos q₁ with h0 | hpos
    · rw [h0] at hq₁
      rw [hq₁] at hd₁
      simp at hd₁
    · exact hpos
  have hq₂Pos : 0 < q₂ := by
    rcases Nat.eq_zero_or_pos q₂ with h0 | hpos
    · rw [h0] at hq₂
      rw [hq₂] at hd₂
      simp at hd₂
    · exact hpos
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, q₁ = r₁ + 1 :=
    ⟨q₁ - 1, by omega⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r₂, q₂ = r₂ + 1 :=
    ⟨q₂ - 1, by omega⟩
  rw [hq₁, hq₂, hr₁, hr₂]
  exact (pinTrajectory_positive_period_multiple
    (fun k => actionOf (cfg k)) t0 start period
    hactionPeriod r₁).trans
      (pinTrajectory_positive_period_multiple
        (fun k => actionOf (cfg k)) t0 start period
        hactionPeriod r₂).symm

/-- Three ordered visits to one deterministic configuration force equality of
the concrete vectors at the second and third visits. -/
theorem three_config_visits_second_eq_third
    {α : Type} (cfg : Nat → α) (actionOf : α → List Nat)
    (t0 : Tongues)
    (hreplay : Replays cfg)
    {i j k : Nat}
    (hij : i < j) (hjk : j < k)
    (hijCfg : cfg i = cfg j)
    (hikCfg : cfg i = cfg k) :
    pinTrajectory (fun n => actionOf (cfg n)) t0 j =
      pinTrajectory (fun n => actionOf (cfg n)) t0 k := by
  let d₁ := j - i
  let d₂ := k - i
  have hd₁ : 0 < d₁ := by dsimp [d₁]; omega
  have hd₂ : 0 < d₂ := by dsimp [d₂]; omega
  have hi₁ : i + d₁ = j := by dsimp [d₁]; omega
  have hi₂ : i + d₂ = k := by dsimp [d₂]; omega
  have hret₁ : cfg (i + d₁) = cfg i := by
    rw [hi₁]
    exact hijCfg.symm
  have hret₂ : cfg (i + d₂) = cfg i := by
    rw [hi₂]
    exact hikCfg.symm
  have h := positive_returns_same_tongues
    cfg actionOf t0 hreplay hd₁ hd₂ hret₁ hret₂
  rwa [hi₁, hi₂] at h

end GeneralN
