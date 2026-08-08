import ConcreteAscentTrace
import ConcreteEchoRun

/-!
# Register cases for a concrete ascent trace

For a finite read time `k` and cell `c`, either some ascent up to `k` wrote
`c`, in which case a greatest such index exists and the canonical echo
register contains that encoded entry, or no ascent wrote `c`, in which case
the register is exactly its initial value.

The file also records the complete prefix of ascent entries through time `k`
and its accumulated boundary-tongue equation, for the initial-register
retrace case.
-/

namespace GeneralN

/-- A finite nonempty set of natural indices has a greatest member. -/
theorem exists_last_le {P : Nat → Prop} :
    ∀ k, (∃ j, j ≤ k ∧ P j) →
      ∃ j, j ≤ k ∧ P j ∧
        ∀ i, j < i → i ≤ k → ¬ P i := by
  intro k
  induction k with
  | zero =>
      intro h
      obtain ⟨j, hj, hp⟩ := h
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst j
      exact ⟨0, Nat.le_refl _, hp,
        fun i hi hle _ => by omega⟩
  | succ n ih =>
      intro h
      by_cases htop : P (n + 1)
      · exact ⟨n + 1, Nat.le_refl _, htop,
          fun i hi hle _ => by omega⟩
      · obtain ⟨j, hj, hp⟩ := h
        have hjn : j ≤ n := by
          by_cases hjeq : j = n + 1
          · exact False.elim (htop (hjeq ▸ hp))
          · omega
        obtain ⟨r, hrn, hrP, hrLast⟩ :=
          ih ⟨j, hjn, hp⟩
        refine ⟨r, Nat.le_trans hrn (Nat.le_succ n), hrP, ?_⟩
        intro i hri hik hiP
        by_cases hitop : i = n + 1
        · exact htop (hitop ▸ hiP)
        · exact hrLast i hri (by omega) hiP

/-- With no write to `c` through time `k`, the echo register remains its
initial value. -/
theorem reg_eq_initial_of_no_write
    (m : Echo.Machine) (e r0 : Nat → Nat) :
    ∀ k c,
      (∀ i, i ≤ k → m.cellOf (e i) ≠ c) →
      Echo.reg m e r0 k c = r0 c := by
  intro k
  induction k with
  | zero =>
      intro c hno
      have h0 := hno 0 (Nat.zero_le 0)
      simp [Echo.reg, h0]
  | succ n ih =>
      intro c hno
      have htop : m.cellOf (e (n + 1)) ≠ c :=
        hno (n + 1) (Nat.le_refl _)
      rw [Echo.reg_skip m e r0 htop]
      apply ih
      intro i hi
      exact hno i (Nat.le_trans hi (Nat.le_succ n))

/-- A last physical ascent of cell `c` is stored as its even encoded slot. -/
theorem canonical_reg_last_entry
    {w : Wiring} (entry : Nat → Nat) (r0 : Nat → Nat)
    {j k c : Nat}
    (hc : physicalCell w (entry j) = c)
    (hjk : j ≤ k)
    (hno : ∀ i, j < i → i ≤ k →
      physicalCell w (entry i) ≠ c) :
    Echo.reg (canonicalEchoMachine w)
      (encodedEntries entry) r0 k c = encodeSlot (entry j) := by
  apply Echo.reg_last_write
  · simpa [encodedEntries, physicalCell] using hc
  · exact hjk
  · intro i hij hik
    simpa [encodedEntries, physicalCell] using hno i hij hik

/-- If no physical ascent wrote cell `c`, its canonical echo register equals
its arbitrary initial encoded slot. -/
theorem canonical_reg_initial
    {w : Wiring} (entry : Nat → Nat) (r0 : Nat → Nat)
    (k c : Nat)
    (hno : ∀ i, i ≤ k → physicalCell w (entry i) ≠ c) :
    Echo.reg (canonicalEchoMachine w)
      (encodedEntries entry) r0 k c = r0 c := by
  apply reg_eq_initial_of_no_write
  intro i hi
  simpa [encodedEntries, physicalCell] using hno i hi

/-- All ascent entries from time zero through `k`. -/
def entriesThrough (entry : Nat → Nat) (k : Nat) : List Nat :=
  entry 0 :: entriesAfter entry 0 k

/-- Membership in a complete prefix gives an index at most `k`. -/
theorem mem_entriesThrough
    (entry : Nat → Nat) (k : Nat) {q : Nat}
    (hq : q ∈ entriesThrough entry k) :
    ∃ i, i ≤ k ∧ q = entry i := by
  unfold entriesThrough at hq
  rcases List.mem_cons.mp hq with hq | hq
  · subst q
    exact ⟨0, Nat.zero_le _, rfl⟩
  · obtain ⟨i, hiLo, hiHi, rfl⟩ :=
      mem_entriesAfter entry 0 hq
    exact ⟨i, by simpa using hiHi, rfl⟩

/-- Every entry in a trace prefix is realised. -/
theorem entriesThrough_realised
    {w : Wiring} (trace : ConcreteAscentTrace w) (k : Nat) :
    ∀ q ∈ entriesThrough trace.entry k,
      IsDescentEntry w q := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ :=
    mem_entriesThrough trace.entry k hq
  exact (trace.freeSlot i).1

/-- The boundary after ascent `k` is the accumulated execution of every
canonical action through `k`. -/
theorem trace_boundary_through
    {w : Wiring} (trace : ConcreteAscentTrace w) (k : Nat) :
    trace.boundary (k + 1) =
      runEntryActions w (entriesThrough trace.entry k)
        (trace.boundary 0) := by
  unfold entriesThrough
  rw [runEntryActions]
  have hafter := trace_boundary_after trace 0 k
  have hfirst := trace_boundary_succ trace 0
  simpa using hafter.trans (by
    rw [hfirst])

/-- If no ascent through `k` has the root of an initial physical slot `f`,
then the complete trace prefix preserves all of `f`'s initial pins. -/
theorem trace_initial_writer_agrees
    {w : Wiring} (trace : ConcreteAscentTrace w)
    (f : Nat) (hf : IsDescentEntry w f)
    (k : Nat)
    (hno : ∀ i, i ≤ k →
      entryRoot w f ≠ entryRoot w (trace.entry i))
    (hinitial : Agrees (trace.boundary 0) (entryAction w f)) :
    Agrees (trace.boundary (k + 1)) (entryAction w f) := by
  have hentries : ∀ q ∈ entriesThrough trace.entry k,
      IsDescentEntry w q :=
    entriesThrough_realised trace k
  have hroots : ∀ q ∈ entriesThrough trace.entry k,
      entryRoot w f ≠ entryRoot w q := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ :=
      mem_entriesThrough trace.entry k hq
    exact hno i hi
  rw [trace_boundary_through]
  exact runEntryActions_preserves_agrees hf
    (entriesThrough trace.entry k) hentries hroots hinitial

end GeneralN
