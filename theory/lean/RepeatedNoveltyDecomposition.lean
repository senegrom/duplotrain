import TrackEndpointMatching

/-!
# Raw repeated-novelty decomposition

This file works directly over `GeneralN.Wiring` and `stepN`.  It isolates the
extra physical fact which is absent from an arbitrary word of bit flips:
every productive write to switch `C` leaves over the one fixed plain-track
edge `link (3*C)`.  Consequently all productive writes to the same switch
have the same post-write entry port.

The flip-label argument is formalised in two stages.

* A last-previous occurrence of a repeated novel writer cannot close with a
  productive-free interior.  Two flips of the same switch would restore the
  complete restricted tongue vector to the vector immediately before the
  first flip, contradicting novelty.
* Choose the last productive event in that interior.  Its writer is a
  different switch and its next entry is fixed by that switch's stem edge.
  Looking backwards to that rerouter's last previous write gives exactly
  three possibilities: a genuinely first writer, a crossing writer frame,
  or a strictly nested writer frame.

Thus the artificial word `1,...,N,1,...,N` cannot remain an unstructured
source of `N` repeated novelties: after its first repeated event, each next
rerouter exposes a crossing frame.  The remaining global theorem is to map
the raw crossing/nesting alternatives to the already proved restoration and
reflector novelty bounds.  No finite-`N` exhaustion is used here.
-/

namespace GeneralN

/-- A productive event and its last earlier productive event with the same
writer.  Other switches may be productive in the open interval. -/
structure RawLastWriterFrame
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (left right : Nat) : Prop where
  order : left < right
  open_productive : RawProductiveAt w N start left
  close_productive : RawProductiveAt w N start right
  same_writer : rawWriterAt w start left = rawWriterAt w start right
  no_same_writer_between : ∀ j, left < j → j < right →
    RawProductiveAt w N start j →
    rawWriterAt w start j ≠ rawWriterAt w start right

inductive RawReroutingShape
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (left reroute right : Nat) : Prop where
  | fresh
      (first : RawFirstWriterAt w N start reroute) :
      RawReroutingShape w N start left reroute right
  | crossing {b : Nat}
      (frame : RawLastWriterFrame w N start b reroute)
      (order : b < left ∧ left < reroute ∧ reroute < right) :
      RawReroutingShape w N start left reroute right
  | nested {b : Nat}
      (frame : RawLastWriterFrame w N start b reroute)
      (order : left < b ∧ b < reroute ∧ reroute < right) :
      RawReroutingShape w N start left reroute right

/-- A parity-witness rerouter has no nested alternative.  It is chosen as
the first interior write to a tongue which really differs across the outer
frame.  Its preceding write is therefore either absent or lies before the
outer opening. -/
inductive RawOpenReroutingShape
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (left reroute right : Nat) : Prop where
  | fresh
      (first : RawFirstWriterAt w N start reroute) :
      RawOpenReroutingShape w N start left reroute right
  | crossing {b : Nat}
      (frame : RawLastWriterFrame w N start b reroute)
      (order : b < left ∧ left < reroute ∧ reroute < right) :
      RawOpenReroutingShape w N start left reroute right

private theorem exists_last_lt_of_exists
    (P : Nat → Prop) [DecidablePred P] :
    ∀ {bound : Nat}, (∃ i, i < bound ∧ P i) →
      ∃ i, i < bound ∧ P i ∧
        ∀ j, i < j → j < bound → ¬ P j := by
  intro bound
  induction bound with
  | zero =>
      rintro ⟨i, hi, _⟩
      omega
  | succ n ih =>
      intro hex
      by_cases hn : P n
      · exact ⟨n, by omega, hn, by omega⟩
      · have hbelow : ∃ i, i < n ∧ P i := by
          obtain ⟨i, hi, hPi⟩ := hex
          by_cases hin : i = n
          · exact (hn (hin ▸ hPi)).elim
          · exact ⟨i, by omega, hPi⟩
        obtain ⟨i, hi, hPi, hlast⟩ := ih hbelow
        exact ⟨i, by omega, hPi, fun j hij hj => by
          by_cases hjn : j = n
          · subst j
            exact hn
          · exact hlast j hij (by omega)⟩

/-- A non-first productive event has a last previous productive occurrence
of the same writer.  This is pure finite order, not periodicity. -/
theorem last_writer_frame_of_productive_not_first
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {right : Nat}
    (hprod : RawProductiveAt w N start right)
    (hnotFirst : ¬ RawFirstWriterAt w N start right) :
    ∃ left, RawLastWriterFrame w N start left right := by
  classical
  have hprevious : ∃ i, i < right ∧
      RawProductiveAt w N start i ∧
      rawWriterAt w start i = rawWriterAt w start right := by
    apply Classical.byContradiction
    intro hnone
    apply hnotFirst
    refine ⟨hprod, ?_⟩
    intro j hj hjprod heq
    exact hnone ⟨j, hj, hjprod, heq⟩
  let P : Nat → Prop := fun i =>
    RawProductiveAt w N start i ∧
    rawWriterAt w start i = rawWriterAt w start right
  have hP : ∃ i, i < right ∧ P i := by
    simpa [P] using hprevious
  obtain ⟨left, hopen, hPo, hlast⟩ :=
    exists_last_lt_of_exists P hP
  exact ⟨left, {
    order := hopen
    open_productive := hPo.1
    close_productive := hprod
    same_writer := hPo.2
    no_same_writer_between := by
      intro j hoj hjc hjprod heq
      exact hlast j hoj hjc ⟨hjprod, heq⟩
  }⟩

/-- Every repeated-writer novelty has a canonical last-writer frame. -/
theorem RawRepeatedWriterNovelAt.last_writer_frame
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {right : Nat}
    (h : RawRepeatedWriterNovelAt w N start right) :
    ∃ left, RawLastWriterFrame w N start left right :=
  last_writer_frame_of_productive_not_first h.1 h.2.1

/-- If a live raw step is not productive, its represented tongue vector is
unchanged. -/
theorem restrictedTonguesAt_succ_eq_of_not_productive
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome)
    (hquiet : ¬ RawProductiveAt w N start k) :
    restrictedTonguesAt w N start (k+1) =
      restrictedTonguesAt w N start k := by
  apply Classical.byContradiction
  intro hne
  exact hquiet ⟨hlive, hne⟩

/-- Every prefix of a successful finite run is successful. -/
private theorem stepN_prefix_some_local
    {w : Wiring} {start finish : Nat × Tongues} {d K : Nat}
    (hd : d ≤ K) (hfinish : stepN w K start = some finish) :
    ∃ middle, stepN w d start = some middle := by
  let rest := K - d
  have hsplit : K = d + rest := by
    dsimp [rest]
    omega
  rw [hsplit, stepN_add] at hfinish
  cases hprefix : stepN w d start with
  | none => simp [hprefix] at hfinish
  | some middle => exact ⟨middle, rfl⟩

/-- A live interval containing no productive event preserves the represented
tongue vector pointwise. -/
theorem restrictedTonguesAt_eq_of_quiet_interval
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {first span : Nat}
    (hfinish : stepN w (first + span) start = some finish)
    (hquiet : ∀ j, first ≤ j → j < first + span →
      ¬ RawProductiveAt w N start j) :
    restrictedTonguesAt w N start (first + span) =
      restrictedTonguesAt w N start first := by
  induction span generalizing finish with
  | zero => simp
  | succ n ih =>
      have hprefix : ∃ middle,
          stepN w (first + n) start = some middle :=
        stepN_prefix_some_local (by omega) hfinish
      obtain ⟨middle, hmiddle⟩ := hprefix
      have hprev := ih hmiddle
        (fun j hfirst hj => hquiet j hfirst (by omega))
      have hlive : (stepN w (first + n + 1) start).isSome := by
        have harith : first + (n+1) = first + n + 1 := by omega
        rw [← harith, hfinish]
        simp
      have hstep := restrictedTonguesAt_succ_eq_of_not_productive
        hlive (hquiet (first+n) (by omega) (by omega))
      have harith : first + (n+1) = first+n+1 := by omega
      rw [harith]
      exact hstep.trans hprev

/-- Restriction commutes with flipping a represented coordinate, even when
the two full tongue functions may differ outside the first `N` switches. -/
theorem restrict_flipAt_congr
    {N C : Nat} {u v : Tongues}
    (h : VectorCount.restrict N u = VectorCount.restrict N v) :
    VectorCount.restrict N (flipAt u C) =
      VectorCount.restrict N (flipAt v C) := by
  unfold VectorCount.restrict
  apply List.map_congr_left
  intro j hj
  have hjN : j < N := List.mem_range.mp hj
  have huv : u j = v j := restrict_eq_apply h hjN
  unfold flipAt
  by_cases hjC : j = C
  · subst j
    simp [huv]
  · simp [hjC, huv]

/-- A productive raw step flips exactly the represented bit named by its
writer. -/
theorem rawProductiveAt_restricted_flip
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    restrictedTonguesAt w N start (k+1) =
      VectorCount.restrict N
        (flipAt (tonguesAt w start k) (rawWriterAt w start k)) := by
  obtain ⟨cur, next, C, hC, hcur, hnext, _hstep,
      _hentry, _hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  subst C
  simp [restrictedTonguesAt, tonguesAt, hcur, hnext, hflip]

/-- The physical fixed-stem law: every productive write to `C` leaves over
the same external edge `link (3*C)`. -/
theorem rawProductiveAt_fixed_stem_successor
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ next,
      stepN w (k+1) start = some next ∧
      w.link (3 * rawWriterAt w start k) = some next.1 := by
  obtain ⟨cur, next, C, hC, _hcur, hnext, hstep,
      _hentry, hexit, _hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hparts := step_some_parts hstep
  subst C
  exact ⟨next, hnext, by simpa [hexit] using hparts.1⟩

/-- Hence two productive occurrences of the same writer have literally the
same post-write entry port. -/
theorem same_raw_writer_post_entries_eq
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {i k : Nat}
    (hi : RawProductiveAt w N start i)
    (hk : RawProductiveAt w N start k)
    (hsame : rawWriterAt w start i = rawWriterAt w start k) :
    rawEntryAt w start (i+1) = rawEntryAt w start (k+1) := by
  obtain ⟨nextI, hnextI, hlinkI⟩ :=
    rawProductiveAt_fixed_stem_successor hN hi
  obtain ⟨nextK, hnextK, hlinkK⟩ :=
    rawProductiveAt_fixed_stem_successor hN hk
  have hport : nextI.1 = nextK.1 := by
    rw [hsame, hlinkK] at hlinkI
    injection hlinkI with hEq
    exact hEq.symm
  simp [rawEntryAt, hnextI, hnextK, hport]

/-- If a last-writer frame had no productive event in its interior, its two
endpoint flips would restore the complete represented tongue vector to the
vector immediately before the opening event. -/
theorem RawLastWriterFrame.closes_vector_of_quiet
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {left right : Nat}
    (F : RawLastWriterFrame w N start left right)
    (hquiet : ∀ j, left < j → j < right →
      ¬ RawProductiveAt w N start j) :
    restrictedTonguesAt w N start (right+1) =
      restrictedTonguesAt w N start left := by
  have horder : left < right := F.order
  have hopenFlip := rawProductiveAt_restricted_flip hN F.open_productive
  have hcloseFlip := rawProductiveAt_restricted_flip hN F.close_productive
  cases hcloseState : stepN w right start with
  | none =>
      have hlive := F.close_productive.1
      have hsplit := stepN_add w right 1 start
      simp [hcloseState] at hsplit
      rw [hsplit] at hlive
      contradiction
  | some closeState =>
      have hstable :
          restrictedTonguesAt w N start right =
            restrictedTonguesAt w N start (left+1) := by
        let span := right - (left+1)
        have harith : left+1+span = right := by
          dsimp [span]
          omega
        have hquiet' : ∀ j, left+1 ≤ j → j < left+1+span →
            ¬ RawProductiveAt w N start j := by
          intro j hj hbound
          apply hquiet j <;> omega
        have hinterval := restrictedTonguesAt_eq_of_quiet_interval
          (first := left+1) (span := span)
          (finish := closeState) (by simpa [harith] using hcloseState)
          hquiet'
        simpa [harith] using hinterval
      have hfirstCongr :
          VectorCount.restrict N
              (flipAt (tonguesAt w start (left+1))
                (rawWriterAt w start right)) =
            VectorCount.restrict N
              (flipAt
                (flipAt (tonguesAt w start left)
                  (rawWriterAt w start right))
                (rawWriterAt w start right)) := by
        apply restrict_flipAt_congr
        calc
          VectorCount.restrict N (tonguesAt w start (left+1)) =
              restrictedTonguesAt w N start (left+1) := rfl
          _ = VectorCount.restrict N
              (flipAt (tonguesAt w start left)
                (rawWriterAt w start left)) := hopenFlip
          _ = VectorCount.restrict N
              (flipAt (tonguesAt w start left)
                (rawWriterAt w start right)) := by rw [F.same_writer]
      calc
        restrictedTonguesAt w N start (right+1) =
            VectorCount.restrict N
              (flipAt (tonguesAt w start right)
                (rawWriterAt w start right)) := hcloseFlip
        _ = VectorCount.restrict N
              (flipAt (tonguesAt w start (left+1))
                (rawWriterAt w start right)) :=
            restrict_flipAt_congr hstable
        _ = VectorCount.restrict N
              (flipAt
                (flipAt (tonguesAt w start left)
                  (rawWriterAt w start right))
                (rawWriterAt w start right)) := hfirstCongr
        _ = restrictedTonguesAt w N start left := by
          rw [flipAt_flipAt]
          rfl

/-- The endpoint cancellation only needs equality of the two middle
vectors.  The middle may contain arbitrarily many productive events. -/
theorem RawLastWriterFrame.closes_vector_of_middle_eq
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {left right : Nat}
    (F : RawLastWriterFrame w N start left right)
    (hmiddle :
      restrictedTonguesAt w N start right =
        restrictedTonguesAt w N start (left+1)) :
    restrictedTonguesAt w N start (right+1) =
      restrictedTonguesAt w N start left := by
  have hopenFlip := rawProductiveAt_restricted_flip hN F.open_productive
  have hcloseFlip := rawProductiveAt_restricted_flip hN F.close_productive
  have hfirstCongr :
      VectorCount.restrict N
          (flipAt (tonguesAt w start (left+1))
            (rawWriterAt w start right)) =
        VectorCount.restrict N
          (flipAt
            (flipAt (tonguesAt w start left)
              (rawWriterAt w start right))
            (rawWriterAt w start right)) := by
    apply restrict_flipAt_congr
    calc
      VectorCount.restrict N (tonguesAt w start (left+1)) =
          restrictedTonguesAt w N start (left+1) := rfl
      _ = VectorCount.restrict N
          (flipAt (tonguesAt w start left)
            (rawWriterAt w start left)) := hopenFlip
      _ = VectorCount.restrict N
          (flipAt (tonguesAt w start left)
            (rawWriterAt w start right)) := by rw [F.same_writer]
  calc
    restrictedTonguesAt w N start (right+1) =
        VectorCount.restrict N
          (flipAt (tonguesAt w start right)
            (rawWriterAt w start right)) := hcloseFlip
    _ = VectorCount.restrict N
          (flipAt (tonguesAt w start (left+1))
            (rawWriterAt w start right)) :=
        restrict_flipAt_congr hmiddle
    _ = VectorCount.restrict N
          (flipAt
            (flipAt (tonguesAt w start left)
              (rawWriterAt w start right))
            (rawWriterAt w start right)) := hfirstCongr
    _ = restrictedTonguesAt w N start left := by
      rw [flipAt_flipAt]
      rfl

/-- Novelty makes the middle of the last-writer frame genuinely
unbalanced: some represented tongue differs between just after the opening
and just before the close. -/
theorem RawRepeatedWriterNovelAt.interior_vector_ne
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {left right : Nat}
    (h : RawRepeatedWriterNovelAt w N start right)
    (F : RawLastWriterFrame w N start left right) :
    restrictedTonguesAt w N start right ≠
      restrictedTonguesAt w N start (left+1) := by
  intro hmiddle
  have hrepeat := F.closes_vector_of_middle_eq hN hmiddle
  apply h.2.2
  apply List.mem_map.mpr
  exact ⟨left, List.mem_range.mpr (by
    have horder := F.order
    omega), hrepeat.symm⟩

private theorem restrict_ne_has_coordinate
    {N : Nat} {u v : Tongues}
    (hne : VectorCount.restrict N u ≠ VectorCount.restrict N v) :
    ∃ C, C < N ∧ u C ≠ v C := by
  apply Classical.byContradiction
  intro hnone
  apply hne
  unfold VectorCount.restrict
  apply List.map_congr_left
  intro C hC
  apply Classical.byContradiction
  intro hneC
  exact hnone ⟨C, List.mem_range.mp hC, hneC⟩

/-- If one coordinate is never productively written on a live half-open
interval, that coordinate is unchanged across the interval. -/
private theorem tongueAt_eq_of_no_writer_interval
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start finish : Nat × Tongues} {first span : Nat}
    (hfinish : stepN w (first+span) start = some finish)
    (hno : ∀ j, first ≤ j → j < first+span →
      RawProductiveAt w N start j → rawWriterAt w start j ≠ C) :
    (tonguesAt w start (first+span)) C =
      (tonguesAt w start first) C := by
  induction span generalizing finish with
  | zero => simp
  | succ n ih =>
      have harith : first + (n+1) = first+n+1 := by omega
      have hprefix : ∃ middle,
          stepN w (first+n) start = some middle :=
        stepN_prefix_some_local
          (d := first+n) (K := first+(n+1)) (by omega) hfinish
      obtain ⟨middle, hmiddle⟩ := hprefix
      have hprev := ih hmiddle
        (fun j hj hbound hprod => hno j hj (by omega) hprod)
      have hlive : (stepN w (first+n+1) start).isSome := by
        rw [← harith, hfinish]
        simp
      obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
        live_successor_configs hlive
      have hcurEq : cur = middle := by
        exact (Option.some.inj (hmiddle.symm.trans hcur)).symm
      subst cur
      have hfinish' : stepN w (first+n+1) start = some finish := by
        rwa [← harith]
      have hnextEq : next = finish := by
        exact Option.some.inj (hnext.symm.trans hfinish')
      subst next
      have hbit : finish.2 C = middle.2 C := by
        apply Classical.byContradiction
        intro hchange
        obtain ⟨hprod, hwriter⟩ :=
          raw_tongue_change_is_productive_writer
            hC hmiddle hfinish' hstep hchange
        exact hno (first+n) (by omega) (by omega) hprod hwriter
      calc
        (tonguesAt w start (first+(n+1))) C = finish.2 C := by
          rw [harith]
          simp [tonguesAt, hfinish']
        _ = middle.2 C := hbit
        _ = (tonguesAt w start (first+n)) C := by
          simp [tonguesAt, hmiddle]
        _ = (tonguesAt w start first) C := hprev

private theorem exists_first_between_of_exists
    (P : Nat → Prop) [DecidablePred P] :
    ∀ (lo span : Nat),
      (∃ j, lo ≤ j ∧ j < lo+span ∧ P j) →
      ∃ j, lo ≤ j ∧ j < lo+span ∧ P j ∧
        ∀ t, lo ≤ t → t < j → ¬ P t := by
  intro lo span
  induction span generalizing lo with
  | zero =>
      rintro ⟨j, hj, hbound, _⟩
      omega
  | succ n ih =>
      intro hex
      by_cases hlo : P lo
      · exact ⟨lo, Nat.le_refl _, by omega, hlo, by omega⟩
      · have htail : ∃ j, lo+1 ≤ j ∧ j < (lo+1)+n ∧ P j := by
          obtain ⟨j, hjlo, hjhi, hjP⟩ := hex
          refine ⟨j, ?_, ?_, hjP⟩
          · by_cases hEq : j = lo
            · subst j
              exact (hlo hjP).elim
            · omega
          · omega
        obtain ⟨j, hjlo, hjhi, hjP, hfirst⟩ := ih (lo+1) htail
        refine ⟨j, by omega, by omega, hjP, ?_⟩
        intro t htlo htj htP
        by_cases hEq : t = lo
        · subst t
          exact hlo htP
        · exact hfirst t (by omega) htj htP

/-- A novel closing frame contains a first interior write to a coordinate
whose middle value really differs.  This is the parity witness used to
exclude a purely properly-nested explanation. -/
theorem RawRepeatedWriterNovelAt.first_changed_writer
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {left right : Nat}
    (h : RawRepeatedWriterNovelAt w N start right)
    (F : RawLastWriterFrame w N start left right) :
    ∃ C reroute,
      C < N ∧ left < reroute ∧ reroute < right ∧
      RawProductiveAt w N start reroute ∧
      rawWriterAt w start reroute = C ∧
      (tonguesAt w start right) C ≠
        (tonguesAt w start (left+1)) C ∧
      ∀ j, left < j → j < reroute →
        RawProductiveAt w N start j →
        rawWriterAt w start j ≠ C := by
  classical
  have hmiddle := h.interior_vector_ne hN F
  obtain ⟨C, hC, hCne⟩ := restrict_ne_has_coordinate hmiddle
  have hright : ∃ finish, stepN w right start = some finish := by
    obtain ⟨last, hlast⟩ := Option.isSome_iff_exists.mp h.1.1
    exact stepN_prefix_some_local
      (d := right) (K := right+1) (by omega) hlast
  obtain ⟨finish, hfinish⟩ := hright
  let span := right - (left+1)
  have hsum : left+1+span = right := by
    have horder := F.order
    dsimp [span]
    omega
  have hex : ∃ j, left+1 ≤ j ∧ j < left+1+span ∧
      RawProductiveAt w N start j ∧ rawWriterAt w start j = C := by
    apply Classical.byContradiction
    intro hnone
    have hstable := tongueAt_eq_of_no_writer_interval
      (first := left+1) (span := span) (finish := finish) hC
      (by simpa [hsum] using hfinish)
      (fun j hjlo hjhi hprod => by
        intro hwriter
        exact hnone ⟨j, hjlo, hjhi, hprod, hwriter⟩)
    rw [hsum] at hstable
    exact hCne hstable
  let P : Nat → Prop := fun j =>
    RawProductiveAt w N start j ∧ rawWriterAt w start j = C
  obtain ⟨reroute, hrlo, hrhi, hrP, hfirst⟩ :=
    exists_first_between_of_exists P (left+1) span (by
      simpa [P] using hex)
  refine ⟨C, reroute, hC, by omega, by simpa [hsum] using hrhi,
    hrP.1, hrP.2, hCne, ?_⟩
  intro j hlj hjr hjprod hwriter
  exact hfirst j (by omega) hjr ⟨hjprod, hwriter⟩

/-- **Open-frame decomposition.**  Every repeated-writer novelty contains
either a genuinely first interior writer, or a writer frame interlacing the
outer frame.  The nested alternative from the arbitrary last-rerouter
decomposition disappears when the rerouter is chosen by actual flip parity.

This is the formal obstruction to the abstract word
`1,...,N,1,...,N`: after its first repeated event, later novelty events must
expose crossing open frames rather than independent nested cancellations. -/
theorem RawRepeatedWriterNovelAt.open_rerouting_decomposition
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {right : Nat}
    (h : RawRepeatedWriterNovelAt w N start right) :
    ∃ left reroute,
      RawLastWriterFrame w N start left right ∧
      RawProductiveAt w N start reroute ∧
      rawWriterAt w start reroute ≠ rawWriterAt w start right ∧
      (∀ j, left < j → j < reroute →
        RawProductiveAt w N start j →
        rawWriterAt w start j ≠ rawWriterAt w start reroute) ∧
      RawOpenReroutingShape w N start left reroute right := by
  obtain ⟨left, F⟩ := h.last_writer_frame
  obtain ⟨C, reroute, _hC, hlr, hrr, hprod, hwriter,
      _hchange, hfirstInside⟩ := h.first_changed_writer hN F
  have hdiff : rawWriterAt w start reroute ≠
      rawWriterAt w start right :=
    F.no_same_writer_between reroute hlr hrr hprod
  refine ⟨left, reroute, F, hprod, hdiff, ?_, ?_⟩
  · intro j hlj hjr hjprod
    rw [hwriter]
    exact hfirstInside j hlj hjr hjprod
  · by_cases hfirst : RawFirstWriterAt w N start reroute
    · exact RawOpenReroutingShape.fresh hfirst
    · obtain ⟨b, G⟩ :=
        last_writer_frame_of_productive_not_first hprod hfirst
      have hbleft : b < left := by
        by_cases hEq : b = left
        · subst b
          exact (hdiff (G.same_writer.symm.trans F.same_writer)).elim
        · by_cases hlt : left < b
          · exact (hfirstInside b hlt G.order G.open_productive
              (G.same_writer.trans hwriter)).elim
          · omega
      exact RawOpenReroutingShape.crossing G
        ⟨hbleft, hlr, hrr⟩



def SelectedInternalEdge (u : Tongues) (p q : Nat) : Prop :=
  ∃ C,
    (p = 3*C ∧ q = selectedBranch u C) ∨
    (q = 3*C ∧ p = selectedBranch u C)

theorem unmatched_after_flip_eq_selected (u : Tongues) (C : Nat) :
    unmatchedBranch (flipAt u C) C = selectedBranch u C := by
  cases h : u C <;>
    simp [unmatchedBranch, selectedBranch, branchPort, flipAt, h]

def DecompCurveEdge (w : Wiring) (u : Tongues) (p q : Nat) : Prop :=
  w.link p = some q ∨ SelectedInternalEdge u p q

inductive DecompCurveConnected (w : Wiring) (u : Tongues) : Nat → Nat → Prop
  | refl (p : Nat) : DecompCurveConnected w u p p
  | cons {p q r : Nat} :
      DecompCurveEdge w u p q →
      DecompCurveConnected w u q r →
      DecompCurveConnected w u p r
end GeneralN
