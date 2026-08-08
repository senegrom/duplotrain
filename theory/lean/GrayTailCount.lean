import FixedSupportBound

/-!
# The absorbed Gray tail carries at most four register snapshots

`absorb_entries` bounds the entry labels after a lobed two-cell trap.  For the
state-count problem we need the slightly stronger statement that the complete
finite register snapshot also has at most four possibilities.

Only the two trapped cells can ever be written.  Each of their registers is
one of the two endpoints of its lobe edge, and every other register remains
frozen at its value at the absorption time.  Hence the whole state is encoded
by a pair of binary choices.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Register invariant of an absorbed lobed pair. -/
def AbsorbedRegisters (a b k0 k : Nat) : Prop :=
  (reg m e r0 k (m.cellOf a) = a ∨
    reg m e r0 k (m.cellOf a) = m.bar a) ∧
  (reg m e r0 k (m.cellOf b) = b ∨
    reg m e r0 k (m.cellOf b) = m.bar b) ∧
  ∀ c, c ≠ m.cellOf a → c ≠ m.cellOf b →
    reg m e r0 k c = reg m e r0 k0 c

/-- After absorption, the two lobe registers stay binary and all other
registers stay frozen. -/
theorem absorbed_registers
    (hrun : IsRun m e r0) {a b k0 : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hAB : m.star (m.cellOf a) = m.cellOf b)
    (hstart : e k0 = a)
    (hreg : reg m e r0 k0 (m.cellOf b) = b ∨
      reg m e r0 k0 (m.cellOf b) = m.bar b) :
    ∀ d, AbsorbedRegisters m e r0 a b k0 (k0+d) := by
  intro d
  induction d with
  | zero =>
      have hcell0 : m.cellOf (e k0) = m.cellOf a := by rw [hstart]
      have hA0 : reg m e r0 k0 (m.cellOf a) = a :=
        (reg_write m e r0 hcell0).trans hstart
      exact ⟨Or.inl hA0, hreg, fun c _ _ => rfl⟩
  | succ n ih =>
      let k := k0 + n
      have hnext : AbsorbedRegisters m e r0 a b k0 (k+1) := by
        have hne : m.cellOf a ≠ m.cellOf b := by
          intro h
          apply m.star_ne (m.cellOf a)
          exact hAB.trans h.symm
        have hentry := absorb_entries m e r0 hrun ha hb hAB hstart hreg
          (k+1) (by dsimp [k]; omega)
        have hstepOther : ∀ c, c ≠ m.cellOf a → c ≠ m.cellOf b →
            reg m e r0 (k+1) c = reg m e r0 k0 c := by
          intro c hca hcb
          have hforeign : m.cellOf (e (k+1)) ≠ c := by
            rcases hentry with h | h | h | h
            · rw [h]
              exact hca.symm
            · rw [h, ha]
              exact hca.symm
            · rw [h]
              exact hcb.symm
            · rw [h, hb]
              exact hcb.symm
          exact (reg_skip m e r0 hforeign).trans (ih.2.2 c hca hcb)
        rcases hentry with h | h | h | h
        · have hcell : m.cellOf (e (k+1)) = m.cellOf a := by rw [h]
          have hA : reg m e r0 (k+1) (m.cellOf a) = a :=
            (reg_write m e r0 hcell).trans h
          have hB : reg m e r0 (k+1) (m.cellOf b) =
              reg m e r0 k (m.cellOf b) :=
            reg_skip m e r0 (by rw [hcell]; exact hne)
          refine ⟨Or.inl hA, ?_, hstepOther⟩
          rw [hB]
          exact ih.2.1
        · have hcell : m.cellOf (e (k+1)) = m.cellOf a := by rw [h, ha]
          have hA : reg m e r0 (k+1) (m.cellOf a) = m.bar a :=
            (reg_write m e r0 hcell).trans h
          have hB : reg m e r0 (k+1) (m.cellOf b) =
              reg m e r0 k (m.cellOf b) :=
            reg_skip m e r0 (by rw [hcell]; exact hne)
          refine ⟨Or.inr hA, ?_, hstepOther⟩
          rw [hB]
          exact ih.2.1
        · have hcell : m.cellOf (e (k+1)) = m.cellOf b := by rw [h]
          have hB : reg m e r0 (k+1) (m.cellOf b) = b :=
            (reg_write m e r0 hcell).trans h
          have hA : reg m e r0 (k+1) (m.cellOf a) =
              reg m e r0 k (m.cellOf a) :=
            reg_skip m e r0 (by rw [hcell]; exact hne.symm)
          refine ⟨?_, Or.inl hB, hstepOther⟩
          rw [hA]
          exact ih.1
        · have hcell : m.cellOf (e (k+1)) = m.cellOf b := by rw [h, hb]
          have hB : reg m e r0 (k+1) (m.cellOf b) = m.bar b :=
            (reg_write m e r0 hcell).trans h
          have hA : reg m e r0 (k+1) (m.cellOf a) =
              reg m e r0 k (m.cellOf a) :=
            reg_skip m e r0 (by rw [hcell]; exact hne.symm)
          refine ⟨?_, Or.inr hB, hstepOther⟩
          rw [hA]
          exact ih.1
      simpa [k, Nat.add_assoc] using hnext

/-- Binary code of an absorbed state. -/
def absorbedCode (a b k : Nat) : Nat × Nat :=
  (reg m e r0 k (m.cellOf a), reg m e r0 k (m.cellOf b))

/-- The four possible binary register codes. -/
def absorbedUniverse (a b : Nat) : List (Nat × Nat) :=
  [(a,b), (a,m.bar b), (m.bar a,b), (m.bar a,m.bar b)]

theorem absorbedCode_mem {a b k0 k : Nat}
    (h : AbsorbedRegisters m e r0 a b k0 k) :
    absorbedCode m e r0 a b k ∈ absorbedUniverse m a b := by
  rcases h.1 with hA | hA <;> rcases h.2.1 with hB | hB <;>
    simp [absorbedCode, absorbedUniverse, hA, hB]

/-- Equal absorbed binary codes force equal finite register snapshots. -/
theorem absorbedCode_eq_snap_eq
    {a b k0 i j : Nat}
    (hi : AbsorbedRegisters m e r0 a b k0 i)
    (hj : AbsorbedRegisters m e r0 a b k0 j)
    (cells : List Nat)
    (hcode : absorbedCode m e r0 a b i =
      absorbedCode m e r0 a b j) :
    snap m e r0 cells i = snap m e r0 cells j := by
  have hA := congrArg Prod.fst hcode
  have hB := congrArg Prod.snd hcode
  unfold absorbedCode at hA hB
  unfold snap
  apply List.map_congr_left
  intro c hc
  by_cases hca : c = m.cellOf a
  · rw [hca]
    exact hA
  · by_cases hcb : c = m.cellOf b
    · rw [hcb]
      exact hB
    · exact (hi.2.2 c hca hcb).trans (hj.2.2 c hca hcb).symm

private theorem nodup_transfer_absorbed
    {f : Nat → List Nat} {g : Nat → Nat × Nat} :
    ∀ {ks : List Nat},
      (∀ i, i ∈ ks → ∀ j, j ∈ ks → g i = g j → f i = f j) →
      (ks.map f).Nodup → (ks.map g).Nodup := by
  intro ks
  induction ks with
  | nil => intro _ _; simp
  | cons k rest ih =>
      intro hinj hnd
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      constructor
      · intro hm
        obtain ⟨j, hj, hgj⟩ := List.mem_map.mp hm
        have hfj := hinj k List.mem_cons_self j
          (List.mem_cons_of_mem _ hj) hgj.symm
        exact hnd.1 (List.mem_map.mpr ⟨j, hj, hfj.symm⟩)
      · exact ih
          (fun i hi j hj => hinj i (List.mem_cons_of_mem _ hi)
            j (List.mem_cons_of_mem _ hj)) hnd.2

private theorem nodup_subset_length_pairs
    {l S : List (Nat × Nat)}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) :
    l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
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

/-- **The Gray tail has at most four complete register snapshots.** -/
theorem absorbed_snapshot_count
    (hrun : IsRun m e r0) {a b k0 : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hAB : m.star (m.cellOf a) = m.cellOf b)
    (hstart : e k0 = a)
    (hreg : reg m e r0 k0 (m.cellOf b) = b ∨
      reg m e r0 k0 (m.cellOf b) = m.bar b)
    (cells ks : List Nat)
    (hks : ∀ k ∈ ks, k0 ≤ k)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ 4 := by
  have hstate : ∀ k ∈ ks, AbsorbedRegisters m e r0 a b k0 k := by
    intro k hk
    have hk0 : k0 ≤ k := hks k hk
    obtain ⟨d, rfl⟩ : ∃ d, k = k0+d := ⟨k-k0, by omega⟩
    exact absorbed_registers m e r0 hrun ha hb hAB hstart hreg d
  have hcodes : (ks.map (absorbedCode m e r0 a b)).Nodup :=
    nodup_transfer_absorbed
      (fun i hi j hj hc =>
        absorbedCode_eq_snap_eq m e r0
          (hstate i hi) (hstate j hj) cells hc)
      hnd
  have hsub : ∀ z ∈ ks.map (absorbedCode m e r0 a b),
      z ∈ absorbedUniverse m a b := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact absorbedCode_mem m e r0 (hstate k hk)
  have hle := nodup_subset_length_pairs hcodes hsub
  simpa [absorbedUniverse] using hle

end Echo
