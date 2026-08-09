import MellitRamanTopLevelRecursion

/-!
# Exact selected-close flip-stack recursion

This module repairs the selected-close strong induction at the vector level.
A recursive call retains every pending outer writer. The terminal base is a
literal member of the canonical first-writer-plus-event-zero history.

No quantitative claim is hidden here: a four-vector conclusion additionally
requires a proof that the retained writer stack has two-switch support.
-/

namespace GeneralN

/-- Apply pending outer writers from the inside out. -/
def applyFlipStack : List Nat -> Tongues -> Tongues
  | [], u => u
  | writer :: rest, u => flipAt (applyFlipStack rest u) writer

/-- Restricted equality is preserved by an arbitrary common flip stack. -/
theorem restrict_applyFlipStack_congr
    {N : Nat} {u v : Tongues}
    (h : VectorCount.restrict N u = VectorCount.restrict N v) :
    forall stack,
      VectorCount.restrict N (applyFlipStack stack u) =
        VectorCount.restrict N (applyFlipStack stack v)
  | [] => h
  | writer :: rest => by
      simp only [applyFlipStack]
      exact restrict_flipAt_congr
        (restrict_applyFlipStack_congr h rest)

/-- A selected close represented exactly as a finite stack of physical
writer flips applied to one canonical paid base vector. -/
structure SelectedCloseFlipStack
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (close : Nat) : Type where
  baseTime : Nat
  writers : List Nat
  base_before : baseTime <= close
  base_paid :
    List.Mem (restrictedTonguesAt w N start baseTime)
      (rawFirstWriterHistory w N start (C.z5 + 1) ++
        [restrictedTonguesAt w N start (C.z0 + 1)])
  writers_bounded : forall writer,
    List.Mem writer writers -> writer < N
  vector_eq :
    restrictedTonguesAt w N start (close + 1) =
      VectorCount.restrict N
        (applyFlipStack writers (tonguesAt w start baseTime))

/-- A first-writer post-vector before the horizon is literally in the
canonical paid history. -/
theorem RawFirstWriterAt.post_mem_selected_history
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {k : Nat}
    (hfirst : RawFirstWriterAt w N start k)
    (hk : k < C.z5 + 1) :
    List.Mem (restrictedTonguesAt w N start (k + 1))
      (rawFirstWriterHistory w N start (C.z5 + 1) ++
        [restrictedTonguesAt w N start (C.z0 + 1)]) := by
  apply List.mem_append_left
  unfold rawFirstWriterHistory
  apply List.mem_cons_of_mem
  apply List.mem_map.mpr
  refine Exists.intro k ?_
  exact And.intro
    (mem_rawFirstWriterTimes_iff.mpr (And.intro hk hfirst)) rfl

/-- Split a canonical selected event into event zero or a selected tail
event. -/
theorem RawSixSelectedTime.zero_or_tail
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {close : Nat}
    (hselected : RawSixSelectedTime C close) :
    Or (close = C.z0) (RawSixTailSelectedTime C close) := by
  cases hselected with
  | inl h0 =>
      exact Or.inl h0
  | inr hrest1 =>
      cases hrest1 with
      | inl h1 =>
          exact Or.inr (Or.inl h1)
      | inr hrest2 =>
          cases hrest2 with
          | inl h2 =>
              exact Or.inr (Or.inr (Or.inl h2))
          | inr hrest3 =>
              cases hrest3 with
              | inl h3 =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
              | inr hrest4 =>
                  cases hrest4 with
                  | inl h4 =>
                      exact Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inl h4))))
                  | inr h5 =>
                      exact Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr h5))))

/-- Every vector at or before a selected close is either already paid by
canonical history or is exactly the post-vector of a strictly earlier
selected tail close. This resolves replay bases without losing time
provenance. -/
theorem RawSixSelectedTime.prefix_vector_paid_or_earlier_tail
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {close t : Nat}
    (hselected : RawSixSelectedTime C close)
    (ht : t <= close) :
    Or
      (List.Mem (restrictedTonguesAt w N start t)
        (rawFirstWriterHistory w N start (C.z5 + 1) ++
          [restrictedTonguesAt w N start (C.z0 + 1)]))
      (Exists fun earlier =>
        And (RawSixTailSelectedTime C earlier)
          (And (earlier < close)
            (restrictedTonguesAt w N start t =
              restrictedTonguesAt w N start (earlier + 1)))) := by
  classical
  have hcloseZ5 : close <= C.z5 := hselected.le_z5
  have htHorizon : t <= C.z5 + 1 := by omega
  have hcovered :=
    restrictedTonguesAt_mem_finite_writer_cover
      w N start (C.z5 + 1) t htHorizon
  cases List.mem_append.mp hcovered with
  | inl hfirst =>
      exact Or.inl (List.mem_append_left _ hfirst)
  | inr hrepeated =>
      cases List.mem_map.mp hrepeated with
      | intro j hdata =>
          have hj := hdata.1
          have hvector := hdata.2
          have hjData := mem_rawRepeatedWriterNovelTimes_iff.mp hj
          have Hj : RawRepeatedWriterNovelAt w N start j := hjData.2
          have hjClose : j < close := by
            apply Classical.byContradiction
            intro hnot
            apply Hj.2.2
            apply List.mem_map.mpr
            refine Exists.intro t ?_
            exact And.intro (List.mem_range.mpr (by omega)) hvector.symm
          have hjZ5 : j <= C.z5 := by omega
          have hjSelected : RawSixSelectedTime C j := by
            simpa [RawSixSelectedTime] using
              C.repeated_novelty_at_most_z5 hjZ5 Hj
          cases hjSelected.zero_or_tail with
          | inl hzero =>
              subst j
              apply Or.inl
              apply List.mem_append_right
              simp only [List.mem_singleton]
              exact hvector.symm
          | inr htail =>
              exact Or.inr (Exists.intro j
                (And.intro htail
                  (And.intro hjClose hvector.symm)))

end GeneralN
/-- **Terminating transport-preserving selected-close recursion.**

The measure is the literal close time. At each close, the exact last-rerouter
transport contributes one outer writer. The rerouter vector is either paid or
is the post-vector of a strictly earlier selected close, in which case the
recursive representation is extended by that one writer. Unlike
SelectedFramePaidClosure, no pending flip is discarded. -/
theorem selected_close_flip_stack
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    (C : RawOverlappingFiveWindowReduction w N start) :
    forall close,
      RawSixSelectedTime C close ->
      forall opening,
        RawLastWriterFrame w N start opening close ->
        Nonempty (SelectedCloseFlipStack C close) := by
  intro close
  apply Nat.strongRecOn (motive := fun close =>
    RawSixSelectedTime C close ->
    forall opening,
      RawLastWriterFrame w N start opening close ->
      Nonempty (SelectedCloseFlipStack C close)) close
  intro close ih hselected opening F
  cases hselected.last_rerouter_transport hN F with
  | intro reroute hdata =>
      have R : RawLastRerouter w N start opening reroute close := hdata.1
      have htransport :
          restrictedTonguesAt w N start (close + 1) =
            VectorCount.restrict N
              (flipAt (tonguesAt w start (reroute + 1))
                (rawWriterAt w start close)) := hdata.2.2
      have hbase :=
        hselected.prefix_vector_paid_or_earlier_tail
          (t := reroute + 1) (by
            have hright := R.inside_right
            omega)
      cases hbase with
      | inl hpaid =>
          exact Nonempty.intro {
            baseTime := reroute + 1
            writers := [rawWriterAt w start close]
            base_before := by
              have hright := R.inside_right
              omega
            base_paid := hpaid
            writers_bounded := by
              intro writer hmem
              simp only [List.mem_singleton] at hmem
              subst writer
              exact rawProductiveAt_writer_lt hN F.close_productive
            vector_eq := by
              simpa [applyFlipStack] using htransport
          }
      | inr hearlier =>
          cases hearlier with
          | intro earlier hdataEarlier =>
              have htail : RawSixTailSelectedTime C earlier :=
                hdataEarlier.1
              have hearlierClose : earlier < close :=
                hdataEarlier.2.1
              have hbaseEq :
                  restrictedTonguesAt w N start (reroute + 1) =
                    restrictedTonguesAt w N start (earlier + 1) :=
                hdataEarlier.2.2
              have hearlierSelected : RawSixSelectedTime C earlier :=
                htail.selected
              cases hearlierSelected.rawRepeatedWriterNovelAt.last_writer_frame with
              | intro earlierOpening earlierFrame =>
                  cases ih earlier hearlierClose hearlierSelected
                      earlierOpening earlierFrame with
                  | intro rep =>
                      exact Nonempty.intro {
                        baseTime := rep.baseTime
                        writers := rawWriterAt w start close :: rep.writers
                        base_before := by
                          have hbaseBefore := rep.base_before
                          omega
                        base_paid := rep.base_paid
                        writers_bounded := by
                          intro writer hmem
                          simp only [List.mem_cons] at hmem
                          cases hmem with
                          | inl hhead =>
                              subst writer
                              exact rawProductiveAt_writer_lt
                                hN F.close_productive
                          | inr hrest =>
                              exact rep.writers_bounded writer hrest
                        vector_eq := by
                          calc
                            restrictedTonguesAt w N start (close + 1) =
                                VectorCount.restrict N
                                  (flipAt
                                    (tonguesAt w start (reroute + 1))
                                    (rawWriterAt w start close)) :=
                              htransport
                            _ = VectorCount.restrict N
                                  (flipAt
                                    (tonguesAt w start (earlier + 1))
                                    (rawWriterAt w start close)) :=
                              restrict_flipAt_congr hbaseEq
                            _ = VectorCount.restrict N
                                  (flipAt
                                    (applyFlipStack rep.writers
                                      (tonguesAt w start rep.baseTime))
                                    (rawWriterAt w start close)) :=
                              restrict_flipAt_congr rep.vector_eq
                            _ = VectorCount.restrict N
                                  (applyFlipStack
                                    (rawWriterAt w start close :: rep.writers)
                                    (tonguesAt w start rep.baseTime)) := by
                              rfl
                      }
