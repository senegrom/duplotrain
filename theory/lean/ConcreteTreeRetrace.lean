import ConcreteTreeDisjoint

/-!
# Last-ascent pins survive other-tree traffic

A landed cascade is switch-simple.  Therefore executing its pin word leaves
every switch on that word agreeing with its own branch.  By tree disjointness,
subsequent ascents of different roots preserve all those pins.  The original
`retrace` theorem can then be applied after arbitrary other-tree traffic.

This is the concrete last-writer-wins statement behind the echo-machine
register read.
-/

namespace GeneralN

/-- A switch-simple pin word leaves every visited switch agreeing with its
recorded branch. -/
theorem pinList_agrees_of_switch_nodup
    (word : List Nat) (t : Tongues)
    (hnd : (word.map (fun b => b / 3)).Nodup) :
    Agrees (pinList word t) word := by
  induction word generalizing t with
  | nil =>
      intro b hb
      cases hb
  | cons a rest ih =>
      have hnd' := List.nodup_cons.mp hnd
      intro b hb
      rcases List.mem_cons.mp hb with hba | hbRest
      · subst b
        have havoid : ∀ c ∈ rest, c / 3 ≠ a / 3 := by
          intro c hc hca
          apply hnd'.1
          exact List.mem_map.mpr ⟨c, hc, hca⟩
        unfold pinList
        rw [pinList_apply_of_avoids_switch
          rest (pin t a) (a / 3) havoid]
        unfold pin
        rw [if_pos rfl]
      · unfold pinList
        exact ih (pin t a) hnd'.2 b hbRest

/-- A realised canonical action leaves its own tree pins in agreement. -/
theorem entryAction_self_agrees
    {w : Wiring} {p : Nat}
    (hp : IsDescentEntry w p) (t : Tongues) :
    Agrees (pinList (entryAction w p) t) (entryAction w p) := by
  rcases hp with ⟨u, ps, s, u', hd⟩
  rw [entryAction_eq_of_descent hd]
  exact pinList_agrees_of_switch_nodup
    (p :: ps) t (descent_switch_path_nodup hd)

end GeneralN
