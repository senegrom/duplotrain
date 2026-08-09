import MellitEarlySecondRepeatAssembly
import MinimalForeignCrossingClosure

/-!
# Mellit/Raman assembly at an overlap-minimal BABA

The pure support crossing left by the early Mellit pair and the pure foreign
restoration crossing classified by Raman are not the same proposition.  They
occur on complementary branches of the exact BABA endpoint classification.
This file joins them at that common split without identifying them.

For an endpoint lobe, the first/second-repeat construction now has only three
outcomes: a reached simple cycle, a pair reached after the first selected
close, or the explicit early pure-support-crossing residue.  For the
complementary foreign/foreign branch, Raman's well-founded selector gives an
interior reached lobe, a first-writer charge, or the exact quiet residual.
-/

namespace GeneralN

/-- A simple cycle together with the actual global time at which the raw run
reaches it. -/
def MellitReachedSimpleCycle
    (w : Wiring) (start : Nat × Tongues) : Prop :=
  ∃ K atRepeat,
    stepN w K start = some atRepeat ∧
    SettlesOnSimpleCycle w atRepeat

/-- The quantitative second-repeat pair, retained when its protected-pair
start is later than the first selected tail close. -/
structure MellitLatePairResidue
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start) : Type where
  g : Nat
  e : Nat
  K : Nat
  direct : ManufacturedFlipReflector w g e
  opposite : ManufacturedReflector w e g
  runway_empty : direct.runway = []
  candy_empty : direct.candy = []
  reach : stepN w K start = some (g, opposite.activatedState)
  late : C.z1 + 1 < K
  quantitative : ∀ (times : List Nat) (history : List (List Bool)),
    (∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) →
    FourNoveltyCover w N start times history ∨
      ∃ path ∈ opposite.toSupported.paths, ∃ passage ∈ path,
        passageSwitch passage = direct.actionSwitch

/-- Full context of the early pure-support-crossing branch. -/
structure MellitEarlyPureCrossingResidue
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start) : Type where
  g : Nat
  e : Nat
  K : Nat
  direct : ManufacturedFlipReflector w g e
  opposite : ManufacturedReflector w e g
  runway_empty : direct.runway = []
  candy_empty : direct.candy = []
  reach : stepN w K start = some (g, opposite.activatedState)
  early : K ≤ C.z1 + 1
  pure : EarlyDirectLobePureCrossingResidue
    (K := K) C direct opposite

/-- The exact no-frame/least-quiet-frame output of Raman's selector. -/
def RamanQuietForeignResidue
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (_B : RawBABAInterlacement
      w N start prior second reroute third) : Prop :=
  (∀ opening closing,
      second < opening →
      opening < reroute →
      RawLastWriterFrame w N start opening closing →
      False) ∨
    ∃ opening closing,
      second < opening ∧
      opening < reroute ∧
      opening < closing ∧
      closing < reroute ∧
      Echo.ForeignRestorationFrame
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) opening closing ∧
      (∀ opening' closing',
        second < opening' →
        opening' < reroute →
        RawLastWriterFrame w N start opening' closing' →
        closing' < closing → False) ∧
      (∀ k, opening < k → k < closing →
        ¬ RawProductiveAt w N start k)

/-- The six exact outcomes after joining Mellit's endpoint-lobe route and
Raman's complementary pure-foreign route. -/
inductive MellitRamanBABAOutcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    (B : RawBABAInterlacement
      w N start prior second reroute third) : Prop
  | cycle (h : MellitReachedSimpleCycle w start)
  | latePair (h : Nonempty (MellitLatePairResidue C))
  | earlyPureCrossing (h : Nonempty (MellitEarlyPureCrossingResidue C))
  | interiorLobe (k : Nat) (h : RawReachedDirectLobeAt w start k)
  | firstWriterCharge (k : Nat)
      (hsecond : second < k) (hreroute : k < reroute)
      (hfirst : RawFirstWriterAt w N start k)
  | quietForeign (h : RamanQuietForeignResidue B)

/-- Once a quantitative opposite pair is available, its reach time gives an
exact early/late split.  The early branch is already forced to be the pure
crossing by `MellitEarlySecondRepeatAssembly`; the late branch retains the
full pair/contact theorem for the later history-payment argument. -/
theorem RawOverlappingFiveWindowReduction.mellit_pair_early_or_late
    {w : Wiring} {N g e K : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (D : ManufacturedFlipReflector w g e)
    (R : ManufacturedReflector w e g)
    (hrunway : D.runway = [])
    (hcandy : D.candy = [])
    (hreach : stepN w K start = some (g, R.activatedState))
    (hquant : ∀ (times : List Nat) (history : List (List Bool)),
      (∀ j ∈ times, j < K →
        restrictedTonguesAt w N start j ∈ history) →
      FourNoveltyCover w N start times history ∨
        ∃ path ∈ R.toSupported.paths, ∃ passage ∈ path,
          passageSwitch passage = D.actionSwitch) :
    Nonempty (MellitLatePairResidue C) ∨
      Nonempty (MellitEarlyPureCrossingResidue C) := by
  by_cases hearly : K ≤ C.z1 + 1
  · exact Or.inr ⟨{
      g := g
      e := e
      K := K
      direct := D
      opposite := R
      runway_empty := hrunway
      candy_empty := hcandy
      reach := hreach
      early := hearly
      pure := C.early_direct_lobe_pair_forces_pure_crossing
        hN D R hrunway hcandy hreach hearly hquant
    }⟩
  · exact Or.inl ⟨{
      g := g
      e := e
      K := K
      direct := D
      opposite := R
      runway_empty := hrunway
      candy_empty := hcandy
      reach := hreach
      late := Nat.lt_of_not_ge hearly
      quantitative := hquant
    }⟩

/-- Assemble either exact lobe endpoint of the left BABA frame. -/
theorem RawBABAInterlacement.left_lobe_mellit_outcome
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (hleft :
      Echo.ExactLobeWrite
          (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) prior ∨
        Echo.ExactLobeWrite
          (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) reroute) :
    MellitReachedSimpleCycle w start ∨
      Nonempty (MellitLatePairResidue C) ∨
      Nonempty (MellitEarlyPureCrossingResidue C) := by
  rcases B.left_lobe_second_repeat_four_cover_or_contact hN hleft with
    hcycle | hpair
  · obtain ⟨next, atRepeat, visited, hnext, hvisited, hsettles⟩ :=
      hcycle
    apply Or.inl
    refine ⟨prior + 1 + visited, atRepeat, ?_, hsettles⟩
    rw [stepN_add, hnext]
    exact hvisited
  · obtain ⟨next, D, R, K, _hnext, hreach,
      hrunway, hcandy, haction, hquant⟩ := hpair
    have hquantD : ∀ (times : List Nat) (history : List (List Bool)),
        (∀ j ∈ times, j < K →
          restrictedTonguesAt w N start j ∈ history) →
        FourNoveltyCover w N start times history ∨
          ∃ path ∈ R.toSupported.paths, ∃ passage ∈ path,
            passageSwitch passage = D.actionSwitch := by
      intro times history hpast
      rcases hquant times history hpast with hcover | hcontact
      · exact Or.inl hcover
      · obtain ⟨path, hpath, passage, hpassage, hswitch⟩ := hcontact
        exact Or.inr ⟨path, hpath, passage, hpassage,
          hswitch.trans haction.symm⟩
    rcases C.mellit_pair_early_or_late hN D R
        hrunway hcandy hreach hquantD with hlate | hearly
    · exact Or.inr (Or.inl hlate)
    · exact Or.inr (Or.inr hearly)

/-- Assemble either exact lobe endpoint of the right BABA frame. -/
theorem RawBABAInterlacement.right_lobe_mellit_outcome
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (hright :
      Echo.ExactLobeWrite
          (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) second ∨
        Echo.ExactLobeWrite
          (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) third) :
    MellitReachedSimpleCycle w start ∨
      Nonempty (MellitLatePairResidue C) ∨
      Nonempty (MellitEarlyPureCrossingResidue C) := by
  rcases B.right_lobe_second_repeat_four_cover_or_contact hN hright with
    hcycle | hpair
  · obtain ⟨next, atRepeat, visited, hnext, hvisited, hsettles⟩ :=
      hcycle
    apply Or.inl
    refine ⟨second + 1 + visited, atRepeat, ?_, hsettles⟩
    rw [stepN_add, hnext]
    exact hvisited
  · obtain ⟨next, D, R, K, _hnext, hreach,
      hrunway, hcandy, haction, hquant⟩ := hpair
    have hquantD : ∀ (times : List Nat) (history : List (List Bool)),
        (∀ j ∈ times, j < K →
          restrictedTonguesAt w N start j ∈ history) →
        FourNoveltyCover w N start times history ∨
          ∃ path ∈ R.toSupported.paths, ∃ passage ∈ path,
            passageSwitch passage = D.actionSwitch := by
      intro times history hpast
      rcases hquant times history hpast with hcover | hcontact
      · exact Or.inl hcover
      · obtain ⟨path, hpath, passage, hpassage, hswitch⟩ := hcontact
        exact Or.inr ⟨path, hpath, passage, hpassage,
          hswitch.trans haction.symm⟩
    rcases C.mellit_pair_early_or_late hN D R
        hrunway hcandy hreach hquantD with hlate | hearly
    · exact Or.inr (Or.inl hlate)
    · exact Or.inr (Or.inr hearly)

/-- **Combined Mellit/Raman BABA classification.**

Every endpoint-lobe branch is sent through the sharp second-repeat assembly;
the sole complementary branch is sent through Raman's minimal pure-foreign
selector.  Thus no endpoint/support interaction or foreign-restoration case
is silently dropped. -/
theorem RawBABAOverlapMinimal.mellit_raman_outcome
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B) :
    MellitRamanBABAOutcome C B := by
  rcases B.endpoint_lobe_or_foreign_crossing hN with
    hprior | hreroute | hsecond | hthird | hpure
  · rcases B.left_lobe_mellit_outcome hN C (Or.inl hprior) with
      hcycle | hlate | hearly
    · exact .cycle hcycle
    · exact .latePair hlate
    · exact .earlyPureCrossing hearly
  · rcases B.left_lobe_mellit_outcome hN C (Or.inr hreroute) with
      hcycle | hlate | hearly
    · exact .cycle hcycle
    · exact .latePair hlate
    · exact .earlyPureCrossing hearly
  · rcases B.right_lobe_mellit_outcome hN C (Or.inl hsecond) with
      hcycle | hlate | hearly
    · exact .cycle hcycle
    · exact .latePair hlate
    · exact .earlyPureCrossing hearly
  · rcases B.right_lobe_mellit_outcome hN C (Or.inr hthird) with
      hcycle | hlate | hearly
    · exact .cycle hcycle
    · exact .latePair hlate
    · exact .earlyPureCrossing hearly
  · rcases hmin.pure_foreign_lobe_charge_or_quiet_residual hN hpure with
      hlobe | hcharge | hquiet
    · obtain ⟨k, hk⟩ := hlobe
      exact .interiorLobe k hk
    · obtain ⟨k, hsecond, hreroute, hfirst⟩ := hcharge
      exact .firstWriterCharge k hsecond hreroute hfirst
    · exact .quietForeign hquiet

end GeneralN
