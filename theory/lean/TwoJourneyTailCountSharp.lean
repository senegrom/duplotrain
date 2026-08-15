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
    {α : Type} [BEq α] [LawfulBEq α]
    {f : Nat → α} (p : Nat → Bool) :
    ∀ {xs : List Nat},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
            apply hnd.1
            exact List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

end GeneralN
