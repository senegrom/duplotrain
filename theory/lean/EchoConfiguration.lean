import EchoMachine
import OverwriteLasso

/-!
# Deterministic replay of finite echo configurations

A register snapshot alone does not include the currently ascended slot, so it
need not determine the next step.  The pair

    (current entry, finite register snapshot)

is the correct finite abstract configuration.  If the finite cell list
contains every partner cell read by the run, equality of configurations at
two times propagates forever.

When cascade actions are fixed by the current entry, a repeated echo
configuration therefore supplies the periodic action hypothesis required by
`pinTrajectory_eventually_periodic`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Current entry together with the finite register snapshot. -/
def configSnap (cells : List Nat) (k : Nat) : Nat × List Nat :=
  (e k, snap m e r0 cells k)

private theorem map_eq_at_mem
    {α β : Type} {xs : List α} {f g : α → β}
    (h : xs.map f = xs.map g) {x : α} (hx : x ∈ xs) :
    f x = g x := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hh := congrArg List.head? h
        simpa using hh
      · have ht := congrArg List.tail h
        simp only [List.map_cons, List.tail_cons] at ht
        exact ih ht hx

/-- Equality of finite snapshots gives equality of the register at each
listed cell. -/
theorem reg_eq_of_snap_eq
    (cells : List Nat) {i j c : Nat}
    (hsnap : snap m e r0 cells i = snap m e r0 cells j)
    (hc : c ∈ cells) :
    reg m e r0 i c = reg m e r0 j c := by
  unfold snap at hsnap
  exact map_eq_at_mem hsnap hc

/-- One-step determinism of the finite echo configuration. -/
theorem configSnap_succ_eq
    (hrun : IsRun m e r0) (cells : List Nat)
    (hcover : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    {i j : Nat}
    (hcfg : configSnap m e r0 cells i =
      configSnap m e r0 cells j) :
    configSnap m e r0 cells (i + 1) =
      configSnap m e r0 cells (j + 1) := by
  have hentry : e i = e j := congrArg Prod.fst hcfg
  have hsnap : snap m e r0 cells i = snap m e r0 cells j :=
    congrArg Prod.snd hcfg
  let partner := m.star (m.cellOf (e i))
  have hpartner : partner ∈ cells := by
    dsimp [partner]
    exact hcover i
  have hold : ∀ c ∈ cells,
      reg m e r0 i c = reg m e r0 j c := by
    intro c hc
    exact reg_eq_of_snap_eq m e r0 cells hsnap hc
  have hnext : e (i + 1) = e (j + 1) := by
    calc
      e (i + 1) = m.bar (reg m e r0 i partner) := by
        simpa [partner] using hrun i
      _ = m.bar (reg m e r0 j partner) :=
        congrArg m.bar (hold partner hpartner)
      _ = m.bar (reg m e r0 j
          (m.star (m.cellOf (e j)))) := by rw [hentry]
      _ = e (j + 1) := by simpa using (hrun j).symm
  have hsnapNext : snap m e r0 cells (i + 1) =
      snap m e r0 cells (j + 1) := by
    unfold snap
    apply List.map_congr_left
    intro c hc
    by_cases hi : m.cellOf (e (i + 1)) = c
    · have hj : m.cellOf (e (j + 1)) = c := by
        rw [← hnext]
        exact hi
      simp [reg, hi, hj, hnext]
    · have hj : m.cellOf (e (j + 1)) ≠ c := by
        intro h
        apply hi
        rwa [hnext]
      simp [reg, hi, hj, hold c hc]
  apply Prod.ext
  · exact hnext
  · exact hsnapNext

/-- Equal finite configurations replay equally for every number of future
steps. -/
theorem configSnap_add_eq
    (hrun : IsRun m e r0) (cells : List Nat)
    (hcover : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    {i j : Nat}
    (hcfg : configSnap m e r0 cells i =
      configSnap m e r0 cells j) :
    ∀ r,
      configSnap m e r0 cells (i + r) =
        configSnap m e r0 cells (j + r) := by
  intro r
  induction r with
  | zero => simpa using hcfg
  | succ n ih =>
      have hs := configSnap_succ_eq m e r0
        hrun cells hcover ih
      simpa [Nat.add_assoc] using hs

/-- A repeated configuration makes the entry sequence periodic from the
first occurrence onward. -/
theorem entry_periodic_of_config_repeat
    (hrun : IsRun m e r0) (cells : List Nat)
    (hcover : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    (start period : Nat)
    (hrepeat : configSnap m e r0 cells start =
      configSnap m e r0 cells (start + period)) :
    ∀ r, e (start + period + r) = e (start + r) := by
  intro r
  have hcfg := configSnap_add_eq m e r0 hrun cells hcover
    hrepeat r
  exact (congrArg Prod.fst hcfg).symm

/-- If a concrete cascade word is determined by the current echo entry, a
repeated finite configuration makes those overwrite words periodic. -/
theorem entryActions_periodic_of_config_repeat
    (hrun : IsRun m e r0) (cells : List Nat)
    (hcover : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    (actionOf : Nat → List Nat)
    (start period : Nat)
    (hrepeat : configSnap m e r0 cells start =
      configSnap m e r0 cells (start + period)) :
    ∀ k, start ≤ k →
      actionOf (e (k + period)) = actionOf (e k) := by
  intro k hk
  obtain ⟨r, rfl⟩ : ∃ r, k = start + r :=
    ⟨k - start, by omega⟩
  congr 1
  have hentry := entry_periodic_of_config_repeat
    m e r0 hrun cells hcover start period hrepeat r
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hentry

end Echo
