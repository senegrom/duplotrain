import SharpStateLawAssembly

/-!
# Two manufacturing journeys followed by a directly counted tail

The physical length of the tail is irrelevant here.  We split selected raw
times at the exact end of the second manufacturing journey.  Earlier samples
are covered by the two canonical construction histories, with their shared
`stateA` boundary erased once.  Later samples are shifted to `stateB` and
passed to an arbitrary tongue-vector counting theorem.
-/

namespace GeneralN


theorem tailsharp_nodup_map_filter
    {α : Type}
    {f : Nat → α} (p : Nat → Bool) :
    ∀ {xs : List Nat},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs hnd
  exact ((List.filter_sublist (p := p) (l := xs)).map f).nodup hnd

end GeneralN
