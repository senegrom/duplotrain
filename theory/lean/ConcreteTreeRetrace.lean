import ConcreteTreeDisjoint
import DescentSimplicity

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

/-- After a realised ascent, arbitrary realised ascents of different roots
preserve agreement with the original ascent word. -/
theorem last_entryAction_survives_other_roots
    {w : Wiring} {p : Nat}
    (hp : IsDescentEntry w p)
    (entries : List Nat)
    (hentries : ∀ q ∈ entries, IsDescentEntry w q)
    (hroots : ∀ q ∈ entries,
      entryRoot w p ≠ entryRoot w q)
    (t : Tongues) :
    Agrees
      (runEntryActions w entries
        (pinList (entryAction w p) t))
      (entryAction w p) := by
  apply runEntryActions_preserves_agrees hp entries
    hentries hroots
  exact entryAction_self_agrees hp t

/-- The concrete result tongue vector of a descent remains in agreement with
its action after arbitrary different-root traffic. -/
theorem descent_result_survives_other_roots
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (hd : Descent w t p ps s t')
    (entries : List Nat)
    (hentries : ∀ q ∈ entries, IsDescentEntry w q)
    (hroots : ∀ q ∈ entries,
      entryRoot w p ≠ entryRoot w q) :
    Agrees (runEntryActions w entries t') (p :: ps) := by
  have hp : IsDescentEntry w p := ⟨t, ps, s, t', hd⟩
  have hsurvive := last_entryAction_survives_other_roots
    hp entries hentries hroots t
  have ht' := descent_result_eq_entryAction hd
  rw [← ht'] at hsurvive
  have haction := entryAction_eq_of_descent hd
  rwa [haction] at hsurvive

/-- **Concrete last-writer retrace.**  A landed cascade remains retraceable
after any finite sequence of ascents belonging to different root trees. -/
theorem retrace_after_other_roots
    {w : Wiring} {t : Tongues} {p s ℓ : Nat}
    {ps : List Nat} {t' : Tongues}
    (hd : Descent w t p ps s t')
    (hentry : w.link ℓ = some p)
    (entries : List Nat)
    (hentries : ∀ q ∈ entries, IsDescentEntry w q)
    (hroots : ∀ q ∈ entries,
      entryRoot w p ≠ entryRoot w q) :
    stepN w (p :: ps).length
      (3 * (lastOf p ps / 3), runEntryActions w entries t') =
      some (ℓ, runEntryActions w entries t') := by
  apply retrace hd ℓ hentry
  exact descent_result_survives_other_roots
    hd entries hentries hroots

end GeneralN
