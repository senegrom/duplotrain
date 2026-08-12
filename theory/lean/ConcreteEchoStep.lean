import ConcreteEchoMachine
import ConcreteTreeRetrace

/-!
# The concrete last-writer echo step

Let `f` be the most recent ascent entry of one root tree.  After any finite
sequence of ascents of different roots, the pins laid by `f` remain intact.
Facing that tree's root therefore retraces the old cascade and exits at the
jump partner `wireBar f`.

The second theorem places this retrace immediately after a current ascent of
the mouth-partner tree.  It is the physical counterpart of
`Echo.return_jump`.
-/

namespace GeneralN

/-- A canonical free entry has the reverse branch-edge link required by
`retrace`. -/
theorem canonicalEchoSlot_reverse_link
    {w : Wiring} {f : Nat}
    (hf : IsCanonicalEchoSlot w f) :
    w.link (wireBar w f) = some f := by
  exact w.symm _ _ hf.2.2.1

/-- **Last-writer exit.**  The most recent ascent entry `f` remains the exit
selected by its root after arbitrary different-root traffic. -/
theorem last_writer_retrace_exit
    {w : Wiring} {t : Tongues} {f s : Nat}
    {fs : List Nat} {tF : Tongues}
    (hdF : Descent w t f fs s tF)
    (hfSlot : IsCanonicalEchoSlot w f)
    (later : List Nat)
    (hlater : ∀ q ∈ later, IsDescentEntry w q)
    (hroots : ∀ q ∈ later,
      entryRoot w f ≠ entryRoot w q) :
    stepN w (f :: fs).length
      (3 * entryRoot w f, runEntryActions w later tF) =
      some (wireBar w f, runEntryActions w later tF) := by
  have hentry := canonicalEchoSlot_reverse_link hfSlot
  have hret := retrace_after_other_roots
    hdF hentry later hlater hroots
  rw [entryRoot_eq_of_descent hdF]
  exact hret

/-- A descent's canonical landing is exactly three times its landing switch. -/
theorem entryLanding_eq_three_mul
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (hd : Descent w t p ps s t') :
    entryLanding w p = 3 * (entryLanding w p / 3) := by
  rw [entryLanding_eq_of_descent hd]
  have hs := descent_landing_stem hd
  have hstem := stem_eq_three_mul_div hs
  omega

/-- The current partner ascent can be appended to a list of intervening
other-root ascents. -/
theorem later_append_current_avoids_root
    {w : Wiring} {f p : Nat}
    (middle : List Nat)
    (hmiddle : ∀ q ∈ middle, IsDescentEntry w q)
    (hmiddleRoots : ∀ q ∈ middle,
      entryRoot w f ≠ entryRoot w q)
    (hp : IsDescentEntry w p)
    (hfp : entryRoot w f ≠ entryRoot w p) :
    (∀ q ∈ middle ++ [p], IsDescentEntry w q) ∧
    (∀ q ∈ middle ++ [p],
      entryRoot w f ≠ entryRoot w q) := by
  constructor
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmiddle q hq
    · have hqp : q = p := by simpa using hq
      subst q
      exact hp
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmiddleRoots q hq
    · have hqp : q = p := by simpa using hq
      subst q
      exact hfp

/-- **Concrete physical echo step.**  Suppose `f` is the last ascent of the
tree now faced after current entry `p` ascends its mouth partner.  If no
intervening ascent has `f`'s root, the facing phase exits at `wireBar f`. -/
theorem concrete_echo_step
    {w : Wiring}
    {tF tP : Tongues} {f p sF sP : Nat}
    {fs ps : List Nat} {uF uP : Tongues}
    (hdF : Descent w tF f fs sF uF)
    (hdP : Descent w tP p ps sP uP)
    (hfSlot : IsCanonicalEchoSlot w f)
    (middle : List Nat)
    (hmiddle : ∀ q ∈ middle, IsDescentEntry w q)
    (hmiddleRoots : ∀ q ∈ middle,
      entryRoot w f ≠ entryRoot w q)
    (hcurrentDifferent : entryRoot w f ≠ entryRoot w p)
    (hcurrentLandsAtF : entryLanding w p / 3 = entryRoot w f) :
    stepN w (f :: fs).length
      (entryLanding w p,
        runEntryActions w (middle ++ [p]) uF) =
      some (wireBar w f,
        runEntryActions w (middle ++ [p]) uF) := by
  have hp : IsDescentEntry w p :=
    ⟨tP, ps, sP, uP, hdP⟩
  have hlater := later_append_current_avoids_root
    middle hmiddle hmiddleRoots hp hcurrentDifferent
  have hret := last_writer_retrace_exit
    hdF hfSlot (middle ++ [p]) hlater.1 hlater.2
  have hlanding := entryLanding_eq_three_mul hdP
  rw [hcurrentLandsAtF] at hlanding
  rw [hlanding]
  exact hret

end GeneralN
