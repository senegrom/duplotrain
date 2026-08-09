import MellitNoncompatibleSecondRepeat
import MinimalBABASecondRepeat

/-!
# Assembly of the early Mellit second-repeat branch

The quantitative second-repeat theorem returns either the literal four-vector
cover of the five selected closes or a concrete support passage through the
direct lobe's action switch.  The former is forbidden by the raw six-event
reduction.  If the latter passage participates in an early changing repair
route, `early_direct_lobe_changed_contact_false` is the same contradiction.

Consequently the only residue is a *pure crossing*: a static support contact
which is not the support side of any such early changing route contact.  This
file keeps that residue explicit rather than silently treating it as a
compatible pair.
-/

namespace GeneralN

/-- Exact data saying that the support contact of an early direct-lobe pair
is encountered by a changing passage on a completed old repair route.  The
opposite reflector is required to be the flip reflector consumed by the
sharp changed-contact theorem. -/
def EarlyDirectLobeChangedContact
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {g e K : Nat}
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g) : Prop :=
  ∃ (R : ManufacturedFlipReflector w e g)
      (A : ManufacturedReflector w g e)
      (p x : Nat) (approach suffix : List Passage) (u v : Tongues),
    ManufacturedReflector.flip R = B ∧
    PathGrooves B.toSupported.paths B.activatedState ∧
    A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix ∧
    PhysicalTrace w (g, B.activatedState) approach (p, u) ∧
    PathGrooves B.toSupported.paths u ∧
    arrive u p = (x, v) ∧
    p / 3 = D.actionSwitch ∧
    v (p / 3) ≠ u (p / 3) ∧
    K + A.toSupported.travel ≤ C.z1 + 1

/-- The exact pure-crossing residue left after both sharp closures.  There is
a literal support passage through the direct lobe's action switch, but no
early changing repair-route contact using that same opposite reflector. -/
def EarlyDirectLobePureCrossingResidue
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {g e K : Nat}
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g) : Prop :=
  (∃ path ∈ B.toSupported.paths, ∃ passage ∈ path,
      passageSwitch passage = D.actionSwitch) ∧
    ¬ EarlyDirectLobeChangedContact (K := K) C D B

/-- Any early changing realization of the support contact is impossible.
This is only an interface lemma: all dynamical work is the already-proved
exact retrace/changed-forward theorem. -/
theorem RawOverlappingFiveWindowReduction.early_direct_lobe_changed_contact_data_false
    {w : Wiring} {N g e K : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hreach : stepN w K start = some (g, B.activatedState))
    (H : EarlyDirectLobeChangedContact (K := K) C D B) : False := by
  rcases H with ⟨R, A, p, x, approach, suffix, u, v,
    hRB, hRactivated, hrouteSplit, happroach,
    hRu, harrive, hswitch, hchanged, hlead⟩
  subst B
  exact C.early_direct_lobe_changed_contact_false hN D R A
    hRunway hCandy hRactivated hreach hrouteSplit happroach
    hRu harrive hswitch hchanged hlead

/-- **Early second-repeat assembly.**

Assume the quantitative pair/contact output supplied by Mellit's second
repeat and that the pair is reached by the first selected tail close.  Then
either the five selected closes have the literal forbidden four-vector cover,
or the support interaction is the explicit pure-crossing residue above.

The changing-contact alternative is not returned: it is discharged by
`early_direct_lobe_changed_contact_false`. -/
theorem RawOverlappingFiveWindowReduction.early_direct_lobe_pair_four_cover_or_pure_crossing
    {w : Wiring} {N g e K : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hreach : stepN w K start = some (g, B.activatedState))
    (hK : K ≤ C.z1 + 1)
    (hquant : ∀ (times : List Nat) (history : List (List Bool)),
      (∀ j ∈ times, j < K →
        restrictedTonguesAt w N start j ∈ history) →
      FourNoveltyCover w N start times history ∨
        ∃ path ∈ B.toSupported.paths, ∃ passage ∈ path,
          passageSwitch passage = D.actionSwitch) :
    FourNoveltyCover w N start
        [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1]
        (rawFirstWriterHistory w N start (C.z5 + 1) ++
          [restrictedTonguesAt w N start (C.z0 + 1)]) ∨
      EarlyDirectLobePureCrossingResidue (K := K) C D B := by
  let times :=
    [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1]
  let history := rawFirstWriterHistory w N start (C.z5 + 1) ++
    [restrictedTonguesAt w N start (C.z0 + 1)]
  have htimes : ∀ j ∈ times, ¬ j < K := by
    intro j hj hjK
    have o12 : C.z1 < C.z2 := C.order12
    have o23 : C.z2 < C.z3 := C.order23
    have o34 : C.z3 < C.z4 := C.order34
    have o45 : C.z4 < C.z5 := C.order45
    dsimp [times] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega
  have hpast : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history := by
    intro j hj hjK
    exact (htimes j hj hjK).elim
  rcases hquant times history hpast with hcover | hcontact
  · exact Or.inl (by simpa [times, history] using hcover)
  · by_cases hchanged : EarlyDirectLobeChangedContact (K := K) C D B
    · exact (C.early_direct_lobe_changed_contact_data_false
        hN D B hRunway hCandy hreach hchanged).elim
    · exact Or.inr ⟨hcontact, hchanged⟩

/-- Since the first alternative of the assembly theorem is exactly the cover
forbidden by the raw six-event counter, every early direct-lobe pair is a
pure crossing.  Thus support compatibility and every changing support
interaction have both been eliminated. -/
theorem RawOverlappingFiveWindowReduction.early_direct_lobe_pair_forces_pure_crossing
    {w : Wiring} {N g e K : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hreach : stepN w K start = some (g, B.activatedState))
    (hK : K ≤ C.z1 + 1)
    (hquant : ∀ (times : List Nat) (history : List (List Bool)),
      (∀ j ∈ times, j < K →
        restrictedTonguesAt w N start j ∈ history) →
      FourNoveltyCover w N start times history ∨
        ∃ path ∈ B.toSupported.paths, ∃ passage ∈ path,
          passageSwitch passage = D.actionSwitch) :
    EarlyDirectLobePureCrossingResidue (K := K) C D B := by
  rcases C.early_direct_lobe_pair_four_cover_or_pure_crossing
      hN D B hRunway hCandy hreach hK hquant with hcover | hpure
  · exact (C.toSixEventReduction.no_tail_four_cover hN (by
      simpa [FourNoveltyCover,
        RawOverlappingFiveWindowReduction.toSixEventReduction]
        using hcover)).elim
  · exact hpure

/-- Direct assembly with Mellit's raw exact-lobe second-repeat theorem.

There are now exactly three outcomes, with no hidden support-interaction
case:

* the first revisit has already entered a simple cycle;
* the manufactured opposite pair is reached after the first selected close;
* or the early pair is the explicit pure-crossing residue.

In particular, every *early* pair branch from the exact-lobe theorem has had
both its compatible four-cover and its changing support contact discharged.
-/
theorem RawOverlappingFiveWindowReduction.rawExactLobeWrite_second_repeat_cycle_late_or_pure_crossing
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start next finish : Nat × Tongues} {k : Nat}
    {passages : List Passage}
    (C : RawOverlappingFiveWindowReduction w N start)
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k)
    (hnext : stepN w (k + 1) start = some next)
    (htrace : PhysicalTrace w next passages finish)
    (hnonsimple : ¬ SwitchSimple passages) :
    (∃ atRepeat visited,
        stepN w visited next = some atRepeat ∧
        SettlesOnSimpleCycle w atRepeat) ∨
      ∃ (D : ManufacturedFlipReflector w
            (3 * rawWriterAt w start k) next.1)
          (B : ManufacturedReflector w next.1
            (3 * rawWriterAt w start k))
          (K : Nat),
        D.runway = [] ∧ D.candy = [] ∧
        D.actionSwitch = rawWriterAt w start k ∧
        stepN w K start =
          some (3 * rawWriterAt w start k, B.activatedState) ∧
        (C.z1 + 1 < K ∨
          EarlyDirectLobePureCrossingResidue (K := K) C D B) := by
  rcases rawExactLobeWrite_second_repeat_four_cover_or_contact
      hN hprod hlobe hnext htrace hnonsimple with hcycle | hpair
  · exact Or.inl hcycle
  · obtain ⟨D, B, K, hreach, hrunway, hcandy,
      haction, hquant⟩ := hpair
    refine Or.inr ⟨D, B, K, hrunway, hcandy, haction,
      hreach, ?_⟩
    by_cases hearly : K ≤ C.z1 + 1
    · apply Or.inr
      have hquantD : ∀ (times : List Nat)
          (history : List (List Bool)),
          (∀ j ∈ times, j < K →
            restrictedTonguesAt w N start j ∈ history) →
          FourNoveltyCover w N start times history ∨
            ∃ path ∈ B.toSupported.paths, ∃ passage ∈ path,
              passageSwitch passage = D.actionSwitch := by
        intro times history hpast
        rcases hquant times history hpast with hcover | hcontact
        · exact Or.inl hcover
        · obtain ⟨path, hpath, passage, hpassage, hswitch⟩ :=
            hcontact
          exact Or.inr ⟨path, hpath, passage, hpassage,
            hswitch.trans haction.symm⟩
      exact C.early_direct_lobe_pair_forces_pure_crossing
        hN D B hrunway hcandy hreach hearly hquantD
    · exact Or.inl (Nat.lt_of_not_ge hearly)

end GeneralN
