import ConcreteCertifiedEchoRun
import FiniteListBounds
import StateLaw
import StationaryTail

/-!
# Raw-track bridge for stationary recurrent echo tails

`StationaryTail.stationary_recurrent_tail_four_complete` is an abstract echo-
machine theorem.  This file supplies the strongest sound bridge currently
available to the raw `Wiring` / `stepN` dynamics.

There are two ingredients.

1.  A reachable-state version of the rho theorem.  Unlike `run_rho`, it does
    not require one finite list to contain the cell and register values of
    every *unreachable* natural-number slot.  It asks only for the entries and
    registers that the run can actually use.
2.  An explicit concrete compiler interface.  Its `snapshot_replay` field is
    the precise missing semantic obligation: equality of compiled register
    snapshots must force equality of the corresponding restricted raw tongue
    vectors.  No such compiler is silently assumed here.

Once those premises are supplied, every sufficiently late family of pairwise
distinct raw tongue vectors has cardinality at most four.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A register outside the cells ever written by the reachable entry stream
keeps its initial value forever. -/
theorem reg_foreign_reachable
    (cells : List Nat)
    (hentryCells : ∀ k, m.cellOf (e k) ∈ cells)
    {c : Nat} (hc : c ∉ cells) :
    ∀ k, reg m e r0 k c = r0 c := by
  intro k
  induction k with
  | zero =>
      show (if m.cellOf (e 0) = c then e 0 else r0 c) = r0 c
      rw [if_neg (fun h : m.cellOf (e 0) = c =>
        hc (h ▸ hentryCells 0))]
  | succ n ih =>
      rw [reg_skip m e r0
        (fun h : m.cellOf (e (n+1)) = c =>
          hc (h ▸ hentryCells (n+1)))]
      exact ih

/-- Pigeonhole helper for a trajectory in a finite list universe. -/
private theorem exists_repeat_reachable_aux :
    ∀ (n : Nat) (F : Nat → List Nat) (U : List (List Nat)),
      (∀ t, t ≤ n → F t ∈ U) → U.length < n →
      ∃ i j, i < j ∧ j ≤ n ∧ F i = F j := by
  intro n
  induction n with
  | zero =>
      intro F U _ hlen
      exact absurd hlen (Nat.not_lt_zero _)
  | succ n ih =>
      intro F U hmem hlen
      by_cases h : ∃ k, 1 ≤ k ∧ k ≤ n+1 ∧ F k = F 0
      · obtain ⟨k, hk1, hkn, hkF⟩ := h
        exact ⟨0, k, hk1, hkn, hkF.symm⟩
      · have hne : ∀ k, 1 ≤ k → k ≤ n+1 → F k ≠ F 0 :=
          fun k h1 h2 heq => h ⟨k, h1, h2, heq⟩
        have hmem0 : F 0 ∈ U := hmem 0 (Nat.zero_le _)
        have hmem' : ∀ t, t ≤ n → F (t+1) ∈ U.erase (F 0) := by
          intro t ht
          refine (List.mem_erase_of_ne ?_).mpr (hmem (t+1) (by omega))
          exact hne (t+1) (by omega) (by omega)
        have hpos : 0 < U.length := by
          cases U with
          | nil => cases hmem0
          | cons _ _ => simp
        have hlen' : (U.erase (F 0)).length < n := by
          rw [List.length_erase_of_mem hmem0]
          omega
        obtain ⟨i, k, hik, hkn, hF⟩ :=
          ih (fun t => F (t+1)) (U.erase (F 0)) hmem' hlen'
        exact ⟨i+1, k+1, by omega, by omega, hF⟩

/-- Finite-state repetition using only the entry alphabet and the registers
of the listed reachable cells. -/
theorem state_repeat_reachable
    (cells slots : List Nat)
    (hentrySlots : ∀ k, e k ∈ slots)
    (hregSlots : ∀ k c, c ∈ cells → reg m e r0 k c ∈ slots) :
    ∃ i j, i < j ∧
      j ≤ slots.length ^ (cells.length + 1) + 1 ∧
      stateCode m e r0 cells i = stateCode m e r0 cells j := by
  have hmem : ∀ t, stateCode m e r0 cells t ∈
      listPow slots (cells.length + 1) := by
    intro t
    apply mem_listPow
    · show (e t :: cells.map (reg m e r0 t)).length = cells.length + 1
      rw [List.length_cons, List.length_map]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hentrySlots t
      · obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hx'
        exact hregSlots t C hC
  obtain ⟨i, j, hij, hjle, hstate⟩ := exists_repeat_reachable_aux
    ((listPow slots (cells.length + 1)).length + 1)
    (fun t => stateCode m e r0 cells t)
    (listPow slots (cells.length + 1))
    (fun t _ => hmem t) (Nat.lt_succ_self _)
  refine ⟨i, j, hij, ?_, hstate⟩
  rw [listPow_length] at hjle
  exact hjle

/-- **Reachable rho theorem.**  Finite coverage of the actual entry stream
and the registers of reachable cells gives exact entry and all-register
recurrence.  No premise ranges over unreachable machine slots. -/
theorem run_reachable_rho
    (hrun : IsRun m e r0)
    (cells slots : List Nat)
    (hentryCells : ∀ k, m.cellOf (e k) ∈ cells)
    (hpartnerCells : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    (hentrySlots : ∀ k, e k ∈ slots)
    (hregSlots : ∀ k c, c ∈ cells → reg m e r0 k c ∈ slots) :
    ∃ K p, 0 < p ∧
      K + p ≤ slots.length ^ (cells.length + 1) + 1 ∧
      (∀ t, K ≤ t → e (t+p) = e t) ∧
      (∀ t c, K ≤ t → reg m e r0 (t+p) c = reg m e r0 t c) := by
  obtain ⟨i, j, hij, hjle, hstate⟩ :=
    state_repeat_reachable m e r0 cells slots hentrySlots hregSlots
  have hp : 0 < j - i := by omega
  have hreplay := state_replay m e r0 hrun cells hpartnerCells hstate
  have hentry : ∀ t, i ≤ t → e (t + (j-i)) = e t := by
    intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = i+s := ⟨t-i, by omega⟩
    have h := stateCode_entry_eq m e r0 cells (hreplay s)
    have harith : i+s+(j-i) = j+s := by omega
    rw [harith]
    exact h.symm
  have hregs : ∀ t c, i ≤ t →
      reg m e r0 (t+(j-i)) c = reg m e r0 t c := by
    intro t c ht
    obtain ⟨s, rfl⟩ : ∃ s, t = i+s := ⟨t-i, by omega⟩
    have harith : i+s+(j-i) = j+s := by omega
    rw [harith]
    by_cases hc : c ∈ cells
    · exact (stateCode_reg_eq m e r0 cells (hreplay s) c hc).symm
    · rw [reg_foreign_reachable m e r0 cells hentryCells hc,
        reg_foreign_reachable m e r0 cells hentryCells hc]
  exact ⟨i, j-i, hp, by omega, hentry, hregs⟩

end Echo

namespace GeneralN

/-- A raw train run is recurrent from `K` with positive period `q`: it stays
on the track and its complete `(port, tongues)` configuration repeats. -/
def RawRecurrentTail
    (w : Wiring) (c0 : Nat × Tongues) (K q : Nat) : Prop :=
  0 < q ∧
  (∀ t, K ≤ t → (stepN w t c0).isSome) ∧
  ∀ t, K ≤ t → stepN w (t+q) c0 = stepN w t c0

/-- Exact compiler contract for transporting a stationary canonical echo tail
back to raw train times.

`clock_cofinal` says that sufficiently late raw times are represented
sufficiently late in the echo run.  `snapshot_replay` is deliberately
explicit: it is the unresolved compiler fact that equal canonical register
snapshots determine equal restricted raw tongue vectors. -/
structure RecurrentStationaryCompilation
    (w : Wiring) (N : Nat) (c0 : Nat × Tongues) where
  rawStart : Nat
  rawPeriod : Nat
  rawRecurrent : RawRecurrentTail w c0 rawStart rawPeriod
  certified : CertifiedConcreteEchoRun w
  cells : List Nat
  slots : List Nat
  entry_cells : ∀ k,
    (canonicalEchoMachine w).cellOf
      (encodedEntries certified.entry k) ∈ cells
  partner_cells : ∀ k,
    (canonicalEchoMachine w).star
      ((canonicalEchoMachine w).cellOf
        (encodedEntries certified.entry k)) ∈ cells
  register_slots : ∀ k c, c ∈ cells →
    Echo.reg (canonicalEchoMachine w)
      (encodedEntries certified.entry) certified.initialRegister k c ∈ slots
  stationaryStart : Nat
  stationary : ∀ t, stationaryStart ≤ t → ∀ c,
    Echo.nextCell (canonicalEchoMachine w)
        (encodedEntries certified.entry) certified.initialRegister (t+1) c =
      Echo.nextCell (canonicalEchoMachine w)
        (encodedEntries certified.entry) certified.initialRegister t c
  clock : Nat → Nat
  clock_cofinal : ∀ E, ∃ R, rawStart ≤ R ∧
    ∀ t, R ≤ t → E ≤ clock t
  snapshot_replay : ∀ i j, rawStart ≤ i → rawStart ≤ j →
    Echo.snap (canonicalEchoMachine w)
        (encodedEntries certified.entry) certified.initialRegister
        cells (clock i) =
      Echo.snap (canonicalEchoMachine w)
        (encodedEntries certified.entry) certified.initialRegister
        cells (clock j) →
    VectorCount.restrict N (tonguesAt w c0 i) =
      VectorCount.restrict N (tonguesAt w c0 j)

/-- Every sample beyond the raw tail threshold is live. -/
theorem RecurrentStationaryCompilation.live
    {w : Wiring} {N : Nat} {c0 : Nat × Tongues}
    (comp : RecurrentStationaryCompilation w N c0)
    {t : Nat} (ht : comp.rawStart ≤ t) :
    (stepN w t c0).isSome :=
  comp.rawRecurrent.2.1 t ht

/-- **Raw stationary-tail bridge.**  For a recurrent raw train run satisfying
the explicit canonical compiler contract, there is a raw time after which any
pairwise-distinct family of restricted tongue vectors has size at most four.

This is unconditional from the displayed premises: recurrence of the echo
state is derived internally by `run_reachable_rho`, and the complete
stationary-tail theorem supplies the four-snapshot bound. -/
theorem recurrent_stationary_compilation_eventually_four
    {w : Wiring} {N : Nat} {c0 : Nat × Tongues}
    (comp : RecurrentStationaryCompilation w N c0) :
    ∃ R, comp.rawStart ≤ R ∧
      ∀ sample : List Nat,
        (∀ t ∈ sample, R ≤ t) →
        (sample.map (fun t =>
          VectorCount.restrict N (tonguesAt w c0 t))).Nodup →
        sample.length ≤ 4 := by
  let m := canonicalEchoMachine w
  let e := encodedEntries comp.certified.entry
  let r0 := comp.certified.initialRegister
  have hrun : Echo.IsRun m e r0 := by
    simpa [m, e, r0] using certifiedConcreteEcho_isRun comp.certified
  have hr0 : ∀ c, m.cellOf (r0 c) = c := by
    intro c
    simpa [m, r0] using comp.certified.initialWellFormed c
  have hentrySlots : ∀ k, e k ∈ comp.slots := by
    intro k
    have hstored := comp.register_slots k (m.cellOf (e k))
      (comp.entry_cells k)
    have hwrite : Echo.reg m e r0 k (m.cellOf (e k)) = e k :=
      Echo.reg_write m e r0 rfl
    rwa [hwrite] at hstored
  obtain ⟨K, p, hp, _hsize, hentryPeriod, hregPeriod⟩ :=
    Echo.run_reachable_rho m e r0 hrun comp.cells comp.slots
      comp.entry_cells comp.partner_cells hentrySlots
      comp.register_slots
  let E := max K comp.stationaryStart
  obtain ⟨R, hrawR, hclock⟩ := comp.clock_cofinal E
  refine ⟨R, hrawR, ?_⟩
  intro sample hsample hndRaw
  have hrawTimes : ∀ t ∈ sample, comp.rawStart ≤ t := by
    intro t ht
    exact Nat.le_trans hrawR (hsample t ht)
  have hclockTimes : ∀ t ∈ sample, E ≤ comp.clock t := by
    intro t ht
    exact hclock t (hsample t ht)
  have hndAtRawTimes :
      (sample.map (fun t =>
        Echo.snap m e r0 comp.cells (comp.clock t))).Nodup := by
    exact FiniteListBounds.nodup_map_of_fibre sample
      (fun t => Echo.snap m e r0 comp.cells (comp.clock t))
      (fun t => VectorCount.restrict N (tonguesAt w c0 t))
      (fun i hi j hj hs =>
        comp.snapshot_replay i j
          (hrawTimes i hi) (hrawTimes j hj) (by simpa [m, e, r0] using hs))
      hndRaw
  have hndAtEchoTimes :
      ((sample.map comp.clock).map
        (Echo.snap m e r0 comp.cells)).Nodup := by
    simpa [List.map_map, Function.comp_def] using hndAtRawTimes
  have hentryFromE : ∀ t, E ≤ t → e (t+p) = e t := by
    intro t ht
    exact hentryPeriod t (by
      dsimp [E] at ht
      omega)
  have hregFromE : ∀ t c, E ≤ t →
      Echo.reg m e r0 (t+p) c = Echo.reg m e r0 t c := by
    intro t c ht
    exact hregPeriod t c (by
      dsimp [E] at ht
      omega)
  have hstationaryFromE : ∀ t, E ≤ t → ∀ c,
      Echo.nextCell m e r0 (t+1) c = Echo.nextCell m e r0 t c := by
    intro t ht c
    apply comp.stationary t
    dsimp [E] at ht
    omega
  have hclockMap : ∀ j ∈ sample.map comp.clock, E ≤ j := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
    exact hclockTimes t ht
  have hfour := Echo.stationary_recurrent_tail_four_complete
    (m := m) (e := e) (r0 := r0) hrun hr0
    (K := E) (q := p) hp hentryFromE hregFromE hstationaryFromE
    comp.cells (sample.map comp.clock) hclockMap hndAtEchoTimes
  simpa using hfour

end GeneralN
