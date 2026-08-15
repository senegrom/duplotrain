import TrackEndpointMatching

/-!
# Self-pivot shrinkage and the serial one-shot obstruction

This file isolates the raw facts needed by the sharp finite-alternation
argument.

First, every globally novel repeated-writer frame contains a productive
self-pivot.  At that pivot the represented train curve either becomes
strictly smaller or keeps exactly the same finite carrier.  This is the
precise, non-vacuous size dichotomy; no future-tail premise is hidden in the
equal-size branch.

Second, the tempting serial `C,D,C` one-shot construction cannot hand the
train forward to an independent copy when its physical passage trace is
switch-simple.  The immutable external matching gives the general
cycle-or-retrace fork; because the two `C` visits are productive, both leave
through the same stem and the exact `C,D,C` case is forced into the absorbing
cycle branch.

Third, equal size is upgraded to equality of the complete physical carrier
and equality of its at-most-two endpoint-writer names.  In the strict branch
a concrete discarded port remains train-free throughout every self-only
continuation.

Thus any alleged forward concatenation must already repeat a switch passage
inside the first gadget.  That repeated passage is exactly the
interlacement/nesting contact consumed by the raw novelty-frame programme.

Finally, `rawNovelRepeatedStrictShrinks_le_three_mul` proves the global
`3*N` charge bound from one exact raw restoration statement:
`ReusedNovelStrictShrinkPortForcesReplay`.  The file still does not claim
`FiveRepeatedWriterNovelty`; that replay statement and the separately named
equal-size obligation `NovelEqualSelfPivotEntersEndpointEpoch` remain open.
-/

namespace GeneralN

/-! ## A forced self-pivot has a genuine finite-carrier dichotomy -/


theorem map_nodup_of_injective_on_mem_self_pivot
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) : ∀ {xs : List α}, xs.Nodup →
      (∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) →
      (xs.map f).Nodup := by
  intro xs hnd hinj
  induction xs with
  | nil => simp
  | cons a rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
        have hab := hinj a List.mem_cons_self b
          (List.mem_cons_of_mem _ hb) hfb.symm
        exact hnd.1 (hab ▸ hb)
      · exact ih hnd.2
          (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx)
            y (List.mem_cons_of_mem _ hy))

