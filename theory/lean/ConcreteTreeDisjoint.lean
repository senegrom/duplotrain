import DescentRouteCatalogue

/-!
# Distinct concrete cascade trees are disjoint

If two canonical cascade words touch the same switch, `merge_land` gives the
same landing stem and landing injectivity gives the same root.  Contrapositively,
canonical words with different roots have disjoint switch sets.

This is the static non-interference lemma needed by the concrete echo
recurrence: ascents of other trees cannot change any pin laid by the most
recent ascent of a fixed tree.
-/

namespace GeneralN

/-- Two realised canonical actions sharing a switch have the same root. -/
theorem entryRoot_eq_of_shared_switch
    {w : Wiring} {p q b c : Nat}
    (hp : IsDescentEntry w p)
    (hq : IsDescentEntry w q)
    (hb : b ∈ entryAction w p)
    (hc : c ∈ entryAction w q)
    (hswitch : b / 3 = c / 3) :
    entryRoot w p = entryRoot w q := by
  rcases hp with ⟨tp, ps, sp, tp', hdp⟩
  rcases hq with ⟨tq, qs, sq, tq', hdq⟩
  have hpAction := entryAction_eq_of_descent hdp
  have hqAction := entryAction_eq_of_descent hdq
  rw [hpAction] at hb
  rw [hqAction] at hc
  have hland : sp = sq :=
    merge_land hdp hdq hb hc hswitch
  have hdq' : Descent w tq q qs sp tq' := by
    rw [hland]
    exact hdq
  have hlast := land_last_unique hdp hdq'
  rw [entryRoot_eq_of_descent hdp,
    entryRoot_eq_of_descent hdq]
  unfold descentRoot
  omega

/-- Canonical actions with different roots cannot share a switch. -/
theorem different_entryRoots_switch_disjoint
    {w : Wiring} {p q : Nat}
    (hp : IsDescentEntry w p)
    (hq : IsDescentEntry w q)
    (hroot : entryRoot w p ≠ entryRoot w q) :
    ∀ b ∈ entryAction w p,
      ∀ c ∈ entryAction w q, b / 3 ≠ c / 3 := by
  intro b hb c hc hswitch
  exact hroot (entryRoot_eq_of_shared_switch
    hp hq hb hc hswitch)

/-- A pin word that never visits switch `k` preserves tongue `k`. -/
theorem pinList_apply_of_avoids_switch
    (word : List Nat) (t : Tongues) (k : Nat)
    (havoid : ∀ b ∈ word, b / 3 ≠ k) :
    pinList word t k = t k := by
  induction word generalizing t with
  | nil => rfl
  | cons b rest ih =>
      unfold pinList
      have hhead : b / 3 ≠ k :=
        havoid b List.mem_cons_self
      have htail : ∀ c ∈ rest, c / 3 ≠ k := by
        intro c hc
        exact havoid c (List.mem_cons_of_mem _ hc)
      rw [ih (pin t b) htail]
      unfold pin
      rw [if_neg (Ne.symm hhead)]

/-- An ascent of a different root tree preserves every tongue occurring in
this tree's canonical action. -/
theorem other_entryAction_preserves_switches
    {w : Wiring} {p q : Nat}
    (hp : IsDescentEntry w p)
    (hq : IsDescentEntry w q)
    (hroot : entryRoot w p ≠ entryRoot w q)
    (t : Tongues) :
    ∀ b ∈ entryAction w p,
      pinList (entryAction w q) t (b / 3) = t (b / 3) := by
  intro b hb
  apply pinList_apply_of_avoids_switch
  intro c hc
  exact (different_entryRoots_switch_disjoint
    hp hq hroot b hb c hc).symm

/-- Consequently, an ascent of a different tree preserves agreement with all
pins of the fixed tree. -/
theorem other_entryAction_preserves_agrees
    {w : Wiring} {p q : Nat}
    (hp : IsDescentEntry w p)
    (hq : IsDescentEntry w q)
    (hroot : entryRoot w p ≠ entryRoot w q)
    {t : Tongues}
    (hagree : Agrees t (entryAction w p)) :
    Agrees (pinList (entryAction w q) t) (entryAction w p) := by
  intro b hb
  rw [other_entryAction_preserves_switches
    hp hq hroot t b hb]
  exact hagree b hb

/-- Execute a finite sequence of canonical entry actions. -/
noncomputable def runEntryActions (w : Wiring) : List Nat → Tongues → Tongues
  | [], t => t
  | q :: qs, t =>
      runEntryActions w qs (pinList (entryAction w q) t)

/-- A sequence of realised ascents from other roots preserves all pins of the
fixed root tree. -/
theorem runEntryActions_preserves_agrees
    {w : Wiring} {p : Nat}
    (hp : IsDescentEntry w p) :
    ∀ (entries : List Nat) {t : Tongues},
      (∀ q ∈ entries, IsDescentEntry w q) →
      (∀ q ∈ entries, entryRoot w p ≠ entryRoot w q) →
      Agrees t (entryAction w p) →
      Agrees (runEntryActions w entries t) (entryAction w p) := by
  intro entries
  induction entries with
  | nil =>
      intro t hentries hroots hagree
      exact hagree
  | cons q qs ih =>
      intro t hentries hroots hagree
      have hq : IsDescentEntry w q :=
        hentries q List.mem_cons_self
      have hqroot : entryRoot w p ≠ entryRoot w q :=
        hroots q List.mem_cons_self
      have hfirst :
          Agrees (pinList (entryAction w q) t)
            (entryAction w p) :=
        other_entryAction_preserves_agrees
          hp hq hqroot hagree
      apply ih
      · intro r hr
        exact hentries r (List.mem_cons_of_mem _ hr)
      · intro r hr
        exact hroots r (List.mem_cons_of_mem _ hr)
      · exact hfirst

end GeneralN
