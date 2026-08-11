import ConcreteEchoRun

/-!
# A finite raw-to-echo bridge, without an infinite physical run

`Echo.IsRun` is deliberately an infinite recurrence.  A concrete track
calculation, however, normally supplies only a finite live prefix; extending
the *physical* train beyond that prefix would silently assume total links or
periodicity.  This file removes that assumption.

First, any finite echo recurrence through time `H` is extended canonically to
an infinite abstract echo run.  The extension agrees with the supplied entries
and registers at every time `k ≤ H`.  Consequently the unconditional token
calculus applies to the finite prefix exactly, not approximately.

Second, the physical recurrence is stated using actual `Wiring.link` facts.
Thus an unlinked port cannot be smuggled through the total helper `wireBar`:
the latter is used only after `wireBar_of_link` has proved that the physical
edge exists.  Encoding this finite physical recurrence gives the canonical
echo recurrence.

What this file does **not** claim is that arbitrary raw step times are already
cascade boundaries.  `RawBoundaryEchoPrefix` records that exact segmentation.
Constructing such a certificate for every finite live raw trajectory (or
handling a non-landing trailing cycle separately) is the remaining concrete
forest-decomposition obligation.
-/

namespace Echo

/-- The echo recurrence is valid for transitions `0, ..., H-1`.  Entries
through time `H` are therefore fixed; no assertion is made after `H`. -/
def IsRunThrough (m : Machine) (e r0 : Nat → Nat) (H : Nat) : Prop :=
  ∀ k, k < H →
    e (k + 1) = m.bar (reg m e r0 k (m.star (m.cellOf (e k))))

/-- Runtime state after the current entry has already been written. -/
structure PrefixRuntime where
  entry : Nat
  registers : Nat → Nat

/-- Write one entry into its cell. -/
def writeRegister (m : Machine) (x : Nat) (r : Nat → Nat) : Nat → Nat :=
  fun c => if m.cellOf x = c then x else r c

/-- One total abstract echo transition. -/
def prefixNext (m : Machine) (s : PrefixRuntime) : PrefixRuntime :=
  let next := m.bar (s.registers (m.star (m.cellOf s.entry)))
  ⟨next, writeRegister m next s.registers⟩

/-- Canonical infinite runtime generated from one first entry and initial
registers.  This is an abstract continuation only; it makes no claim that the
physical track remains live after a chosen finite horizon. -/
def prefixRuntime (m : Machine) (first : Nat) (r0 : Nat → Nat) :
    Nat → PrefixRuntime
  | 0 => ⟨first, writeRegister m first r0⟩
  | k + 1 => prefixNext m (prefixRuntime m first r0 k)

/-- Entry sequence of the canonical abstract continuation. -/
def extendEntry (m : Machine) (first : Nat) (r0 : Nat → Nat) : Nat → Nat :=
  fun k => (prefixRuntime m first r0 k).entry

/-- The runtime register component is exactly `Echo.reg` for the generated
entry sequence. -/
theorem prefixRuntime_register (m : Machine) (first : Nat) (r0 : Nat → Nat) :
    ∀ k c,
      (prefixRuntime m first r0 k).registers c =
        reg m (extendEntry m first r0) r0 k c := by
  intro k
  induction k with
  | zero =>
      intro c
      rfl
  | succ n ih =>
      intro c
      simp [prefixRuntime, prefixNext, writeRegister, extendEntry, reg, ih]

/-- The canonical continuation is a genuine infinite echo run. -/
theorem extendEntry_isRun (m : Machine) (first : Nat) (r0 : Nat → Nat) :
    IsRun m (extendEntry m first r0) r0 := by
  intro k
  rw [← prefixRuntime_register m first r0 k
    (m.star (m.cellOf (extendEntry m first r0 k)))]
  rfl

/-- Registers depend only on entries up to their time index. -/
theorem reg_congr_through (m : Machine) (r0 : Nat → Nat)
    {e f : Nat → Nat} :
    ∀ k, (∀ j, j ≤ k → e j = f j) →
      ∀ c, reg m e r0 k c = reg m f r0 k c := by
  intro k
  induction k with
  | zero =>
      intro h c
      simp [reg, h 0 (Nat.zero_le _)]
  | succ n ih =>
      intro h c
      have hhead : e (n + 1) = f (n + 1) := h _ (Nat.le_refl _)
      have htail : ∀ j, j ≤ n → e j = f j := by
        intro j hj
        exact h j (Nat.le_trans hj (Nat.le_succ n))
      simp only [reg]
      rw [hhead, ih htail c]

/-- A finite valid prefix agrees entry-for-entry with its canonical abstract
continuation. -/
theorem extendEntry_eq_of_isRunThrough
    (m : Machine) (e r0 : Nat → Nat) {H : Nat}
    (hrun : IsRunThrough m e r0 H) :
    ∀ k, k ≤ H → extendEntry m (e 0) r0 k = e k := by
  have aux : ∀ k, k ≤ H → ∀ j, j ≤ k →
      extendEntry m (e 0) r0 j = e j := by
    intro k
    induction k with
    | zero =>
        intro hk j hj
        have hj0 : j = 0 := by omega
        subst j
        rfl
    | succ n ih =>
        intro hk j hj
        by_cases hjn : j ≤ n
        · exact ih (by omega) j hjn
        · have hjEq : j = n + 1 := by omega
          subst j
          have hprefix : ∀ ell, ell ≤ n →
              extendEntry m (e 0) r0 ell = e ell :=
            ih (by omega)
          have hn := hprefix n (Nat.le_refl _)
          calc
            extendEntry m (e 0) r0 (n + 1) =
                m.bar (reg m (extendEntry m (e 0) r0) r0 n
                  (m.star (m.cellOf (extendEntry m (e 0) r0 n)))) :=
              extendEntry_isRun m (e 0) r0 n
            _ = m.bar (reg m e r0 n
                  (m.star (m.cellOf (e n)))) := by
              rw [hn]
              rw [reg_congr_through m r0 n hprefix]
            _ = e (n + 1) := (hrun n (by omega)).symm
  intro k hk
  exact aux k hk k (Nat.le_refl _)

/-- Register agreement on the represented finite prefix. -/
theorem extendReg_eq_of_isRunThrough
    (m : Machine) (e r0 : Nat → Nat) {H k c : Nat}
    (hrun : IsRunThrough m e r0 H) (hk : k ≤ H) :
    reg m (extendEntry m (e 0) r0) r0 k c = reg m e r0 k c := by
  apply reg_congr_through m r0 k
  intro j hj
  exact extendEntry_eq_of_isRunThrough m e r0 hrun j
    (Nat.le_trans hj hk)

/-- Confirmation is represented exactly at every finite prefix time. -/
theorem extendConfirmed_iff
    (m : Machine) (e r0 : Nat → Nat) {H k s : Nat}
    (hrun : IsRunThrough m e r0 H) (hk : k ≤ H) :
    Confirmed m (extendEntry m (e 0) r0) r0 k s ↔
      Confirmed m e r0 k s := by
  unfold Confirmed
  rw [extendReg_eq_of_isRunThrough m e r0 hrun hk]

/-- Token ends are represented exactly at every finite prefix time. -/
theorem extendTokenEnd_iff
    (m : Machine) (e r0 : Nat → Nat) {H k s : Nat}
    (hrun : IsRunThrough m e r0 H) (hk : k ≤ H) :
    TokenEnd m (extendEntry m (e 0) r0) r0 k s ↔
      TokenEnd m e r0 k s := by
  unfold TokenEnd
  rw [extendConfirmed_iff m e r0 hrun hk,
    extendConfirmed_iff m e r0 hrun hk]

/-- Cell-token lists are literally equal on the finite prefix. -/
theorem extendCellTokens_eq
    (m : Machine) (e r0 : Nat → Nat) (slots : List Nat)
    {H k C : Nat} (hrun : IsRunThrough m e r0 H) (hk : k ≤ H) :
    cellTokens m (extendEntry m (e 0) r0) r0 slots C k =
      cellTokens m e r0 slots C k := by
  unfold cellTokens
  apply List.filter_congr
  intro s _
  exact decide_eq_decide.mpr (by
    rw [extendTokenEnd_iff m e r0 hrun hk])

/-- Register snapshots are literally equal on the finite prefix. -/
theorem extendSnap_eq
    (m : Machine) (e r0 : Nat → Nat) (cells : List Nat)
    {H k : Nat} (hrun : IsRunThrough m e r0 H) (hk : k ≤ H) :
    snap m (extendEntry m (e 0) r0) r0 cells k =
      snap m e r0 cells k := by
  unfold snap
  apply List.map_congr_left
  intro c _
  exact extendReg_eq_of_isRunThrough m e r0 hrun hk

/-- **Finite-prefix repertoire collapse.**  No infinite physical run is
needed: for `K ≤ j ≤ H`, every register value at `j` is its value at `K`
or the slot of a token already alive at `K`. -/
theorem finite_future_register
    (m : Machine) (e r0 : Nat → Nat) {H K C j : Nat}
    (hrun : IsRunThrough m e r0 H)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hKj : K ≤ j) (hjH : j ≤ H) :
    reg m e r0 j C = reg m e r0 K C ∨
      TokenEnd m e r0 K (reg m e r0 j C) := by
  let ee := extendEntry m (e 0) r0
  have hfull : IsRun m ee r0 := extendEntry_isRun m (e 0) r0
  have hfuture := future_register_le m ee r0 hfull hr0 (C := C) hKj
  have hK : K ≤ H := Nat.le_trans hKj hjH
  have hjEq : reg m ee r0 j C = reg m e r0 j C :=
    extendReg_eq_of_isRunThrough m e r0 hrun hjH
  have hKEq : reg m ee r0 K C = reg m e r0 K C :=
    extendReg_eq_of_isRunThrough m e r0 hrun hK
  rcases hfuture with hsame | htoken
  · exact Or.inl (by simpa [ee, hjEq, hKEq] using hsame)
  · apply Or.inr
    have hiff := extendTokenEnd_iff m e r0 hrun hK
      (s := reg m e r0 j C)
    apply hiff.mp
    rwa [hjEq] at htoken

private theorem finite_nodup_subset_length
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    ∀ {l S : List alpha},
      l.Nodup → (∀ x ∈ l, x ∈ S) → l.length ≤ S.length := by
  intro l
  induction l with
  | nil => intro S hnd hsub; exact Nat.zero_le _
  | cons x rest ih =>
      intro S hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ S.erase x := by
        intro y hy
        have hyS : y ∈ S := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- **Finite-prefix repertoire count.**  A duplicate-free list of register
values observed between `K` and `H` has size at most one plus the number of
`K`-tokens of that cell.  Unlike the original infinite theorem, slot coverage
is required only for the values actually listed. -/
theorem finite_repertoire_count
    (m : Machine) (e r0 : Nat → Nat) (slots : List Nat)
    {H K C : Nat}
    (hrun : IsRunThrough m e r0 H)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (values : List Nat) (hnd : values.Nodup)
    (hslots : ∀ v ∈ values, v ∈ slots)
    (hvalues : ∀ v ∈ values, ∃ j,
      K ≤ j ∧ j ≤ H ∧ reg m e r0 j C = v) :
    values.length ≤ (cellTokens m e r0 slots C K).length + 1 := by
  have hsub : ∀ v ∈ values,
      v ∈ reg m e r0 K C :: cellTokens m e r0 slots C K := by
    intro v hv
    obtain ⟨j, hKj, hjH, hval⟩ := hvalues v hv
    rcases finite_future_register m e r0 hrun hr0 hKj hjH with hsame | htoken
    · rw [hval] at hsame
      rw [hsame]
      exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      rw [cellTokens, List.mem_filter]
      have hcell : m.cellOf v = C := by
        rw [← hval]
        exact reg_cell m e r0 hr0 j C
      rw [hval] at htoken
      exact ⟨hslots v hv, decide_eq_true ⟨htoken, hcell⟩⟩
  exact finite_nodup_subset_length hnd hsub

/-- Finite-prefix freezeout at one observed time.  Only the observed register
value must belong to the finite slot catalogue; no slot coverage after `H` is
assumed. -/
theorem finite_freezeout_at
    (m : Machine) (e r0 : Nat → Nat) (slots : List Nat)
    {H K C j : Nat}
    (hrun : IsRunThrough m e r0 H)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hKj : K ≤ j) (hjH : j ≤ H)
    (hslot : reg m e r0 j C ∈ slots)
    (h0 : ∀ s, s ∉ cellTokens m e r0 slots C K) :
    reg m e r0 j C = reg m e r0 K C := by
  rcases finite_future_register m e r0 hrun hr0 hKj hjH with hsame | htoken
  · exact hsame
  · exfalso
    apply h0 (reg m e r0 j C)
    rw [cellTokens, List.mem_filter]
    have hcell : m.cellOf (reg m e r0 j C) = C :=
      reg_cell m e r0 hr0 j C
    exact ⟨hslot, decide_eq_true ⟨htoken, hcell⟩⟩

/-- Finite-prefix singleton lock at one observed time. -/
theorem finite_singleton_lock_at
    (m : Machine) (e r0 : Nat → Nat) (slots : List Nat)
    {H K C t j : Nat}
    (hrun : IsRunThrough m e r0 H)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hKj : K ≤ j) (hjH : j ≤ H)
    (hslot : reg m e r0 j C ∈ slots)
    (h1 : ∀ s ∈ cellTokens m e r0 slots C K, s = t) :
    reg m e r0 j C = reg m e r0 K C ∨ reg m e r0 j C = t := by
  rcases finite_future_register m e r0 hrun hr0 hKj hjH with hsame | htoken
  · exact Or.inl hsame
  · apply Or.inr
    apply h1 (reg m e r0 j C)
    rw [cellTokens, List.mem_filter]
    have hcell : m.cellOf (reg m e r0 j C) = C :=
      reg_cell m e r0 hr0 j C
    exact ⟨hslot, decide_eq_true ⟨htoken, hcell⟩⟩

/-- Under the two-singleton token shape at `K`, one finite-prefix snapshot is
one of the same four Gray candidates as in the infinite theorem. -/
theorem finite_token_shape_at
    (m : Machine) (e r0 : Nat → Nat) (slots cells : List Nat)
    {H K C1 C2 t1 t2 j : Nat}
    (hrun : IsRunThrough m e r0 H)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hKj : K ≤ j) (hjH : j ≤ H)
    (hC1 : C1 ∈ cells) (hC2 : C2 ∈ cells)
    (hregslots : ∀ c ∈ cells, reg m e r0 j c ∈ slots)
    (h1 : ∀ s ∈ cellTokens m e r0 slots C1 K, s = t1)
    (h2 : ∀ s ∈ cellTokens m e r0 slots C2 K, s = t2)
    (h0 : ∀ C, C ≠ C1 → C ≠ C2 →
      ∀ s, s ∉ cellTokens m e r0 slots C K) :
    snap m e r0 cells j ∈
      [cells.map (fun c => if c = C1 then reg m e r0 K C1
          else if c = C2 then reg m e r0 K C2 else reg m e r0 K c),
       cells.map (fun c => if c = C1 then reg m e r0 K C1
          else if c = C2 then t2 else reg m e r0 K c),
       cells.map (fun c => if c = C1 then t1
          else if c = C2 then reg m e r0 K C2 else reg m e r0 K c),
       cells.map (fun c => if c = C1 then t1
          else if c = C2 then t2 else reg m e r0 K c)] := by
  have hfrozen : ∀ c ∈ cells, c ≠ C1 → c ≠ C2 →
      reg m e r0 j c = reg m e r0 K c := by
    intro c hc hc1 hc2
    exact finite_freezeout_at m e r0 slots hrun hr0 hKj hjH
      (hregslots c hc) (h0 c hc1 hc2)
  have hcand : snap m e r0 cells j =
      cells.map (fun c => if c = C1 then reg m e r0 j C1
        else if c = C2 then reg m e r0 j C2
        else reg m e r0 K c) := by
    unfold snap
    apply List.map_congr_left
    intro c hc
    by_cases hc1 : c = C1
    · rw [if_pos hc1, hc1]
    · rw [if_neg hc1]
      by_cases hc2 : c = C2
      · rw [if_pos hc2, hc2]
      · rw [if_neg hc2]
        exact hfrozen c hc hc1 hc2
  rw [hcand]
  have hL1 := finite_singleton_lock_at m e r0 slots hrun hr0
    hKj hjH (hregslots C1 hC1) h1
  have hL2 := finite_singleton_lock_at m e r0 slots hrun hr0
    hKj hjH (hregslots C2 hC2) h2
  rcases hL1 with ha | ha <;> rcases hL2 with hb | hb <;> rw [ha, hb]
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **Finite Gray tail.**  The four-state conclusion applies to any bounded
prefix whose observed register values are covered by the finite slot list.
No physical continuation or periodicity is assumed after `H`. -/
theorem finite_gray_tail
    (m : Machine) (e r0 : Nat → Nat) (slots cells ks : List Nat)
    {H K C1 C2 t1 t2 : Nat}
    (hrun : IsRunThrough m e r0 H)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (htimes : ∀ j ∈ ks, K ≤ j ∧ j ≤ H)
    (hC1 : C1 ∈ cells) (hC2 : C2 ∈ cells)
    (hregslots : ∀ j ∈ ks, ∀ c ∈ cells,
      reg m e r0 j c ∈ slots)
    (h1 : ∀ s ∈ cellTokens m e r0 slots C1 K, s = t1)
    (h2 : ∀ s ∈ cellTokens m e r0 slots C2 K, s = t2)
    (h0 : ∀ C, C ≠ C1 → C ≠ C2 →
      ∀ s, s ∉ cellTokens m e r0 slots C K)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ 4 := by
  have hle := finite_nodup_subset_length hnd
    (fun v hv => by
      obtain ⟨j, hjks, rfl⟩ := List.mem_map.mp hv
      exact finite_token_shape_at m e r0 slots cells hrun hr0
        (htimes j hjks).1 (htimes j hjks).2
        hC1 hC2 (hregslots j hjks) h1 h2 h0)
  rw [List.length_map] at hle
  exact hle

end Echo

namespace GeneralN

/-- A physical entry prefix satisfies the exact echo recurrence through `H`
when every register read is connected by an *actual* track edge to the next
entry.  This deliberately uses `Wiring.link`, not totalized `wireBar`. -/
def IsLinkedPhysicalEchoPrefix (w : Wiring)
    (entry initial : Nat → Nat) (H : Nat) : Prop :=
  ∀ k, k < H →
    w.link
      (physicalReg w entry initial k
        (mateNat (physicalCell w (entry k)))) =
      some (entry (k + 1))

/-- Actual physical links imply the finite physical echo recurrence.  Partial
links are handled soundly: an unlinked register cannot satisfy the premise. -/
theorem linkedPhysicalEchoPrefix_isPhysicalRunThrough
    {w : Wiring} {entry initial : Nat → Nat} {H : Nat}
    (hlink : IsLinkedPhysicalEchoPrefix w entry initial H) :
    ∀ k, k < H →
      entry (k + 1) =
        wireBar w
          (physicalReg w entry initial k
            (mateNat (physicalCell w (entry k)))) := by
  intro k hk
  exact (wireBar_of_link (hlink k hk)).symm

/-- Encoding a finite physical link recurrence gives exactly the canonical
finite echo recurrence. -/
theorem canonicalEcho_isRunThrough
    (w : Wiring) (entry initial : Nat → Nat) {H : Nat}
    (hlink : IsLinkedPhysicalEchoPrefix w entry initial H) :
    Echo.IsRunThrough (canonicalEchoMachine w)
      (encodedEntries entry) (encodedInitial initial) H := by
  intro k hk
  have hphysical :=
    linkedPhysicalEchoPrefix_isPhysicalRunThrough hlink k hk
  have hencoded := congrArg encodeSlot hphysical
  simp only [encodedEntries]
  rw [encoded_reg_eq]
  simpa [canonicalEchoMachine, encodedMachine, physicalCell,
    canonicalPhysicalCellOf, encodedBar_encodeSlot,
    encodedCellOf_encodeSlot] using hencoded

/-- A finite sequence of genuine raw cascade boundaries together with the
actual physical last-register links that drive the next boundary.  No field
mentions raw times after `H`. -/
structure RawBoundaryEchoPrefix
    (w : Wiring) (c0 : Nat × Tongues) (H : Nat) where
  entry : Nat → Nat
  boundary : Nat → Tongues
  clock : Nat → Nat
  initial : Nat → Nat
  rawAt : ∀ k, k ≤ H →
    stepN w (clock k) c0 = some (entry k, boundary k)
  initialWellFormed : ∀ c, physicalCell w (initial c) = c
  linkedRegister : IsLinkedPhysicalEchoPrefix w entry initial H

/-- Canonical abstract continuation of a bounded raw boundary certificate. -/
noncomputable def RawBoundaryEchoPrefix.echoEntry
    {w : Wiring} {c0 : Nat × Tongues} {H : Nat}
    (p : RawBoundaryEchoPrefix w c0 H) : Nat → Nat :=
  Echo.extendEntry (canonicalEchoMachine w)
    (encodeSlot (p.entry 0)) (encodedInitial p.initial)

/-- The canonical continuation is an infinite echo run, although the physical
certificate itself remains strictly finite. -/
theorem RawBoundaryEchoPrefix.echoRun
    {w : Wiring} {c0 : Nat × Tongues} {H : Nat}
    (p : RawBoundaryEchoPrefix w c0 H) :
    Echo.IsRun (canonicalEchoMachine w)
      p.echoEntry (encodedInitial p.initial) :=
  Echo.extendEntry_isRun _ _ _

/-- Encoded abstract entries agree exactly with the raw physical entries
through the certified horizon. -/
theorem RawBoundaryEchoPrefix.echoEntry_eq
    {w : Wiring} {c0 : Nat × Tongues} {H k : Nat}
    (p : RawBoundaryEchoPrefix w c0 H) (hk : k ≤ H) :
    p.echoEntry k = encodeSlot (p.entry k) := by
  apply Echo.extendEntry_eq_of_isRunThrough
    (canonicalEchoMachine w) (encodedEntries p.entry)
      (encodedInitial p.initial)
      (canonicalEcho_isRunThrough w p.entry p.initial p.linkedRegister)
      k hk

/-- Raw boundary tongues are exactly the certified physical state; this is a
direct `stepN` fact, not an inferred replay claim. -/
theorem RawBoundaryEchoPrefix.raw_tongues
    {w : Wiring} {c0 : Nat × Tongues} {H k : Nat}
    (p : RawBoundaryEchoPrefix w c0 H) (hk : k ≤ H) :
    (stepN w (p.clock k) c0).map (fun q => q.2) = some (p.boundary k) := by
  simp [p.rawAt k hk]

/-- **Physical finite-prefix repertoire collapse.**  Every future physical
root-register value through `H` is its value at `K`, or its even encoding is a
token already alive at `K` in the canonical echo machine. -/
theorem RawBoundaryEchoPrefix.physical_future_register
    {w : Wiring} {c0 : Nat × Tongues} {H K C j : Nat}
    (p : RawBoundaryEchoPrefix w c0 H)
    (hKj : K ≤ j) (hjH : j ≤ H) :
    physicalReg w p.entry p.initial j C =
        physicalReg w p.entry p.initial K C ∨
      Echo.TokenEnd (canonicalEchoMachine w)
        p.echoEntry (encodedInitial p.initial) K
        (encodeSlot (physicalReg w p.entry p.initial j C)) := by
  have hprefix := canonicalEcho_isRunThrough
    w p.entry p.initial p.linkedRegister
  have hr0 := encodedInitial_wellFormed w p.initial p.initialWellFormed
  have hfuture := Echo.finite_future_register
    (canonicalEchoMachine w) (encodedEntries p.entry)
      (encodedInitial p.initial) (C := C) hprefix hr0 hKj hjH
  rw [encoded_reg_eq, encoded_reg_eq] at hfuture
  rcases hfuture with hsame | htoken
  · exact Or.inl (encodeSlot_injective hsame)
  · apply Or.inr
    have hK : K ≤ H := Nat.le_trans hKj hjH
    have htoken' := (Echo.extendTokenEnd_iff
      (canonicalEchoMachine w) (encodedEntries p.entry)
        (encodedInitial p.initial) hprefix hK
        (s := encodeSlot (physicalReg w p.entry p.initial j C))).mpr htoken
    simpa [RawBoundaryEchoPrefix.echoEntry, encodedEntries] using htoken'

end GeneralN
