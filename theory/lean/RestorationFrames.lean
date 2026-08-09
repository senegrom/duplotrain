import PairedNoFullReachFreeze
import ReversalFacts
import TreeReplay
import TwoReflectorEdgeTrap

/-!
# Restoration frames and the foreign-crossing obstruction

A productive write replaces one slot in a cell. A restoration frame starts
at such a write and ends when the evicted slot is productively written back
into the same cell. Crossing restoration frames are the precise obstruction
to the naive LIFO argument: their endpoints have order `t₀ < t₁ < u₀ < u₁`.

This file proves unconditional reverse-or-overwrite and returned-root replay
facts. The remaining global step is to show that a minimal foreign/foreign
crossing either produces a smaller crossing or has the compatible
two-reflector shape.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The register cell written by step `k → k+1`. -/
def writerAt (k : Nat) : Nat :=
  m.cellOf (e (k+1))

/-- A productive write at `u` restores the slot evicted at `t`. -/
def RestorationFrame (t u : Nat) : Prop :=
  ProductiveStep m e r0 t ∧
  t < u ∧
  ProductiveStep m e r0 u ∧
  writerAt m e u = writerAt m e t ∧
  e (u+1) = oldSlot m e r0 t

/-- A restoration frame with no earlier intervening delivery of the old slot. -/
def FirstRestorationFrame (t u : Nat) : Prop :=
  RestorationFrame m e r0 t u ∧
  ∀ v, t < v → v < u → e (v+1) ≠ oldSlot m e r0 t

/-- Two restoration intervals cross rather than nest. -/
def RestorationFramesCross (t₀ u₀ t₁ u₁ : Nat) : Prop :=
  t₀ < t₁ ∧ t₁ < u₀ ∧ u₀ < u₁

/-- A first restoration between genuinely different physical edges. -/
def ForeignRestorationFrame (t u : Nat) : Prop :=
  FirstRestorationFrame m e r0 t u ∧
  ¬ SameEdge m (oldSlot m e r0 t) (e (t+1)) ∧
  ¬ SameEdge m (oldSlot m e r0 u) (e (u+1))

/-- The exact unresolved temporal pattern. -/
def ForeignRestorationCrossing (t₀ u₀ t₁ u₁ : Nat) : Prop :=
  ForeignRestorationFrame m e r0 t₀ u₀ ∧
  ForeignRestorationFrame m e r0 t₁ u₁ ∧
  RestorationFramesCross t₀ u₀ t₁ u₁

/-- Inclusion-minimality for a foreign crossing pair. The open global proof
must show that a failed corridor retrace creates a strictly contained pair,
unless the compatible two-reflector alternative below already holds. -/
def MinimalForeignRestorationCrossing (t₀ u₀ t₁ u₁ : Nat) : Prop :=
  ForeignRestorationCrossing m e r0 t₀ u₀ t₁ u₁ ∧
  ∀ a₀ b₀ a₁ b₁,
    ForeignRestorationCrossing m e r0 a₀ b₀ a₁ b₁ →
    t₀ ≤ a₀ → b₁ ≤ u₁ →
    (t₀ < a₀ ∨ b₁ < u₁) → False

/-- Exact premise package for the already-proved separated two-reflector
four-snapshot tail. -/
structure CompatibleTwoReflectorTail (k x a b : Nat) : Prop where
  start : e k = x
  aLobe : m.cellOf (m.bar a) = m.cellOf a
  aPartner : m.cellOf x = m.star (m.cellOf a)
  bLobe : m.cellOf (m.bar b) = m.cellOf b
  bPartner : m.cellOf (m.bar x) = m.star (m.cellOf b)
  aOccupied : ∀ q, k ≤ q → Occupied m e r0 q a
  bOccupied : ∀ q, k ≤ q → Occupied m e r0 q b
  distinct : ReflectorCellsDistinct
    (m.cellOf a) (m.cellOf x) (m.cellOf (m.bar x)) (m.cellOf b)

/-- The compatible alternative is genuinely terminal: it has at most four
register snapshots after its initialization block. -/
theorem CompatibleTwoReflectorTail.snapshots_four
    (hrun : IsRun m e r0)
    (cells : List Nat)
    (hcells : ∀ t, m.star (m.cellOf (e t)) ∈ cells)
    {k x a b : Nat}
    (htrap : CompatibleTwoReflectorTail m e r0 k x a b)
    (ks : List Nat)
    (hks : ∀ j ∈ ks, k+4 ≤ j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ 4 := by
  exact two_reflector_edge_snapshots_four m e r0 hrun cells hcells
    htrap.start htrap.aLobe htrap.aPartner htrap.bLobe htrap.bPartner
    htrap.aOccupied htrap.bOccupied htrap.distinct ks hks hnd

/-- A returned root replays a certified component when endpoint support and
the old edge's one-step preservation are supplied directly. -/
theorem returned_root_replays_component_of_support
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {k l : Nat}
    (hpk : ProductiveStep m e r0 k)
    (hpl : ProductiveStep m e r0 l)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (l+1) s)
    (hpres : Occupied m e r0 (k+1) (oldSlot m e r0 k))
    (hdiffk : ¬ SameEdge m (oldSlot m e r0 k) (e (k+1)))
    (hdiffl : ¬ SameEdge m (oldSlot m e r0 l) (e (l+1)))
    (hreturn : e (l+1) = oldSlot m e r0 k)
    (hroot : RootedCells m e r0 k (oldSlot m e r0 k) cells) :
    snap m e r0 cells (l+1) = snap m e r0 cells k := by
  have hfullK : Full m e r0 k (oldSlot m e r0 k) := by
    simpa [oldSlot] using old_edge_full_of_preserved
      m e r0 hrun hr0 k hpk hpres (by simpa [oldSlot] using hdiffk)
  have hfullL : Full m e r0 (l+1) (e (l+1)) := by
    exact new_edge_full_of_preserved
      m e r0 hrun hr0 l hpl (by simpa [oldSlot] using hdiffl)
  exact rootedCells_sameEdge_replay m e r0 hr0 cells hsupport
    hfullK hfullL (Or.inl hreturn) hroot

/-- **Returned-root component replay.** During a fixed-support interval, a
foreign productive write makes its evicted edge full. If a later foreign
productive write returns that root, the whole rooted component has its old
snapshot. -/
theorem returned_root_replays_component
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {k l : Nat}
    (hkl : k < l)
    (hfixed : PairedSupportFixed m e r0 k (l+1))
    (hpk : ProductiveStep m e r0 k)
    (hpl : ProductiveStep m e r0 l)
    (hdiffk : ¬ SameEdge m (oldSlot m e r0 k) (e (k+1)))
    (hdiffl : ¬ SameEdge m (oldSlot m e r0 l) (e (l+1)))
    (hreturn : e (l+1) = oldSlot m e r0 k)
    (hroot : RootedCells m e r0 k (oldSlot m e r0 k) cells) :
    snap m e r0 cells (l+1) = snap m e r0 cells k := by
  have holdOccupied : Occupied m e r0 k (oldSlot m e r0 k) := by
    left
    unfold oldSlot
    exact old_register_confirmed m e r0 hr0 k _
  have hpres : Occupied m e r0 (k+1) (oldSlot m e r0 k) :=
    (hfixed k (Nat.le_refl _) (by omega) _).mp holdOccupied
  have hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (l+1) s :=
    pairedSupportFixed_between_of_le m e r0 hfixed
      (Nat.le_refl _) (by omega) (Nat.le_refl _)
  exact returned_root_replays_component_of_support m e r0 hrun hr0 cells
    hpk hpl hsupport hpres hdiffk hdiffl hreturn hroot

/-- A foreign first-restoration frame packages exactly the hypotheses needed
for returned-root replay, except for fixed support and the rooted component
certificate. -/
theorem foreign_restoration_replays_rooted_component
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {t u : Nat}
    (hframe : ForeignRestorationFrame m e r0 t u)
    (hfixed : PairedSupportFixed m e r0 t (u+1))
    (hroot : RootedCells m e r0 t (oldSlot m e r0 t) cells) :
    snap m e r0 cells (u+1) = snap m e r0 cells t := by
  rcases hframe with ⟨⟨hrestore, _hfirst⟩, hdiffT, hdiffU⟩
  exact returned_root_replays_component m e r0 hrun hr0 cells
    hrestore.2.1 hfixed hrestore.1 hrestore.2.2.1
    hdiffT hdiffU hrestore.2.2.2.2 hroot

/-- A bounded true predicate with a false left endpoint has a first true
point. This elementary form avoids importing a choice/minimum API. -/
private theorem exists_first_after {P : Nat → Prop} :
    ∀ d a, ¬ P a → P (a+d+1) →
      ∃ s, a < s ∧ s ≤ a+d+1 ∧ P s ∧
        ∀ r, a < r → r < s → ¬ P r := by
  intro d
  induction d with
  | zero =>
      intro a _ha hlast
      refine ⟨a+1, by omega, by omega, ?_, ?_⟩
      · simpa using hlast
      · intro r hr0 hr1
        omega
  | succ d ih =>
      intro a ha hlast
      by_cases hnext : P (a+1)
      · refine ⟨a+1, by omega, by omega, hnext, ?_⟩
        intro r hr0 hr1
        omega
      · have hlast' : P ((a+1)+d+1) := by
          have hidx : (a+1)+d+1 = a+(d+1)+1 := by omega
          rw [hidx]
          exact hlast
        obtain ⟨s, hs0, hs1, hsP, hsmin⟩ := ih (a+1) hnext hlast'
        refine ⟨s, by omega, by omega, hsP, ?_⟩
        intro r hr0 hrs
        by_cases hr : r = a+1
        · subst r
          exact hnext
        · exact hsmin r (by omega) hrs

/-- A nonempty bounded predicate has a last witness below its bound. -/
private theorem exists_last_before {P : Nat → Prop} :
    ∀ b, (∃ t, t < b ∧ P t) →
      ∃ t, t < b ∧ P t ∧
        ∀ s, t < s → s < b → ¬ P s := by
  intro b
  induction b with
  | zero =>
      intro h
      obtain ⟨t, ht, _⟩ := h
      omega
  | succ n ih =>
      intro h
      by_cases hn : P n
      · exact ⟨n, by omega, hn, fun s hs0 hs1 => by omega⟩
      · have h' : ∃ t, t < n ∧ P t := by
          obtain ⟨t, ht, hPt⟩ := h
          refine ⟨t, ?_, hPt⟩
          by_cases htn : t = n
          · subst t
            exact (hn hPt).elim
          · omega
        obtain ⟨t, ht, hPt, hlast⟩ := ih h'
        refine ⟨t, by omega, hPt, ?_⟩
        intro s hts hsn
        by_cases hsnEq : s = n
        · subst s
          exact hn
        · exact hlast s hts (by omega)

/-- If a register changed on `[i,j]`, choose the *last* productive write of
that register before `j`. No later productive step before `j` writes the same
cell. This is the stable top-frame witness needed by crossing arguments. -/
theorem change_has_last_productive_write
    {c i j : Nat} (hij : i ≤ j)
    (hchange : reg m e r0 j c ≠ reg m e r0 i c) :
    ∃ t, i ≤ t ∧ t < j ∧ ProductiveStep m e r0 t ∧
      writerAt m e t = c ∧
      ∀ s, t < s → s < j → ProductiveStep m e r0 s →
        writerAt m e s ≠ writerAt m e t := by
  obtain ⟨t₀, ht₀i, ht₀j, hp₀, hc₀⟩ :=
    change_has_productive_le m e r0 hij hchange
  have hex : ∃ t, t < j ∧
      (ProductiveStep m e r0 t ∧ writerAt m e t = c) := by
    exact ⟨t₀, ht₀j, hp₀, by simpa [writerAt] using hc₀⟩
  obtain ⟨t, htj, hp, hlast⟩ :=
    exists_last_before (P := fun s =>
      ProductiveStep m e r0 s ∧ writerAt m e s = c) j hex
  have hit : i ≤ t := by
    by_cases hle : i ≤ t
    · exact hle
    · exact (hlast t₀ (by omega) ht₀j ⟨hp₀,
        by simpa [writerAt] using hc₀⟩).elim
  refine ⟨t, hit, htj, hp.1, hp.2, ?_⟩
  intro s hts hsj hprod hsame
  apply hlast s hts hsj
  exact ⟨hprod, hsame.trans hp.2⟩

/-- A last productive write controls its register until the endpoint: other
productive writes and all unproductive steps cannot change that cell. -/
theorem last_productive_write_controls_register
    {t j : Nat} (htj : t < j)
    (hlast : ∀ s, t < s → s < j → ProductiveStep m e r0 s →
      writerAt m e s ≠ writerAt m e t) :
    reg m e r0 j (writerAt m e t) = e (t+1) := by
  have hwrite : reg m e r0 (t+1) (writerAt m e t) = e (t+1) :=
    reg_write m e r0 rfl
  by_cases heq : reg m e r0 j (writerAt m e t) =
      reg m e r0 (t+1) (writerAt m e t)
  · exact heq.trans hwrite
  · obtain ⟨s, hs0, hs1, hp, hc⟩ :=
      change_has_productive_le m e r0 (by omega) heq
    have hne := hlast s (by omega) hs1 hp
    exfalso
    apply hne
    simpa [writerAt] using hc

/-- If a productive write's register later contains its evicted slot again,
there is a first restoration frame ending before that later state. -/
theorem exists_first_restoration_frame_of_register_return
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {t j : Nat}
    (hprod : ProductiveStep m e r0 t)
    (hgap : t+1 < j)
    (hreturn : reg m e r0 j (writerAt m e t) = oldSlot m e r0 t) :
    ∃ u, u < j ∧ FirstRestorationFrame m e r0 t u := by
  let C := writerAt m e t
  let old := oldSlot m e r0 t
  have hnewCell : m.cellOf (e (t+1)) = C := by rfl
  have hregNext : reg m e r0 (t+1) C = e (t+1) :=
    reg_write m e r0 hnewCell
  have hnextNotOld : reg m e r0 (t+1) C ≠ old := by
    rw [hregNext]
    simpa [ProductiveStep, C, old, writerAt, oldSlot] using hprod
  obtain ⟨d, hd⟩ : ∃ d, j = (t+1)+d+1 :=
    ⟨j-(t+1)-1, by omega⟩
  have hlast : reg m e r0 ((t+1)+d+1) C = old := by
    rw [← hd]
    exact hreturn
  obtain ⟨s, hs0, hs1, hsP, hsmin⟩ :=
    exists_first_after (P := fun q => reg m e r0 q C = old)
      d (t+1) hnextNotOld hlast
  let u := s-1
  have hus : u+1 = s := by
    dsimp [u]
    omega
  have htu : t < u := by
    dsimp [u]
    omega
  have huj : u < j := by
    rw [hd]
    dsimp [u]
    omega
  have hbefore : reg m e r0 u C ≠ old := by
    by_cases hu0 : u = t+1
    · rw [hu0]
      exact hnextNotOld
    · exact hsmin u (by omega) (by omega)
  have harrivalCell : m.cellOf (e s) = C := by
    by_cases hcell : m.cellOf (e s) = C
    · exact hcell
    · exfalso
      have hskip : reg m e r0 (u+1) C = reg m e r0 u C := by
        apply reg_skip m e r0
        simpa [hus] using hcell
      apply hbefore
      calc
        reg m e r0 u C = reg m e r0 (u+1) C := hskip.symm
        _ = reg m e r0 s C := by rw [hus]
        _ = old := hsP
  have hentryOld : e (u+1) = old := by
    have hwrite : reg m e r0 s C = e s :=
      reg_write m e r0 harrivalCell
    calc
      e (u+1) = e s := by rw [hus]
      _ = reg m e r0 s C := hwrite.symm
      _ = old := hsP
  have huCell : m.cellOf (e (u+1)) = C := by
    rw [hus]
    exact harrivalCell
  have hprodU : ProductiveStep m e r0 u := by
    unfold ProductiveStep
    rw [hentryOld]
    have holdCellAtU : m.cellOf old = C := by
      rw [← hentryOld]
      exact huCell
    rw [holdCellAtU]
    exact Ne.symm hbefore
  have hwriterU : writerAt m e u = C := by
    exact huCell
  have hwriterT : writerAt m e t = C := rfl
  refine ⟨u, huj, ⟨?_, ?_⟩⟩
  · exact ⟨hprod, htu, hprodU, hwriterU.trans hwriterT.symm, hentryOld⟩
  · intro v htv hvu hentry
    have holdCell : m.cellOf old = C := by
      dsimp [old, C]
      unfold oldSlot writerAt
      exact reg_cell m e r0 hr0 t _
    have hvCell : m.cellOf (e (v+1)) = C := by
      rw [hentry]
      exact holdCell
    have hvP : reg m e r0 (v+1) C = old := by
      calc
        reg m e r0 (v+1) C = e (v+1) := reg_write m e r0 hvCell
        _ = old := hentry
    exact hsmin (v+1) (by omega) (by omega) hvP

/-- On a periodic register tail every productive write has a first
restoration before one full period elapses. -/
theorem productive_has_first_restoration_before_period
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K p t : Nat}
    (hp : 0 < p)
    (ht : K ≤ t)
    (hregper : ∀ q c, K ≤ q →
      reg m e r0 (q+p) c = reg m e r0 q c)
    (hprod : ProductiveStep m e r0 t) :
    ∃ u, t < u ∧ u < t+p ∧ FirstRestorationFrame m e r0 t u := by
  have hgap : t+1 < t+p := by
    by_cases h : t+1 < t+p
    · exact h
    · exfalso
      have hp1 : p = 1 := by omega
      have hwrite : reg m e r0 (t+1) (writerAt m e t) = e (t+1) :=
        reg_write m e r0 rfl
      have hper := hregper t (writerAt m e t) ht
      rw [hp1] at hper
      apply hprod
      simpa [writerAt] using hwrite.symm.trans hper
  have hreturn :
      reg m e r0 (t+p) (writerAt m e t) = oldSlot m e r0 t := by
    simpa [writerAt, oldSlot] using hregper t (writerAt m e t) ht
  obtain ⟨u, hu, hframe⟩ :=
    exists_first_restoration_frame_of_register_return
      m e r0 hr0 hprod hgap hreturn
  exact ⟨u, hframe.1.2.1, hu, hframe⟩

/-- **Exact reverse-or-overwrite dichotomy.**

Suppose `e j` is the bar-reflection of the endpoint `e (i+d)` of an old
trace. Then either the next `d` entries retrace every old endpoint exactly,
or there is a reverse depth `q < d` at which the register that should supply
the next endpoint was productively overwritten after it was recorded and
before the failed reverse step.

The witness also certifies the exact successful reverse prefix and the first
failed edge. No laminarity or LIFO assumption is used. -/
theorem bar_retrace_or_first_overwrite
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j d : Nat}
    (hij : i + d ≤ j)
    (hstart : e j = m.bar (e (i+d))) :
    (∀ q, q ≤ d →
      e (j+q) = m.bar (e (i + (d-q)))) ∨
    ∃ q t, q < d ∧
      (∀ r, r ≤ q →
        e (j+r) = m.bar (e (i + (d-r)))) ∧
      e (j+q+1) ≠ m.bar (e (i + (d-q-1))) ∧
      i + (d-q-1) ≤ t ∧ t < j+q ∧
      ProductiveStep m e r0 t ∧
      writerAt m e t = m.cellOf (e (i + (d-q-1))) ∧
      ∀ s, t < s → s < j+q → ProductiveStep m e r0 s →
        writerAt m e s ≠ writerAt m e t := by
  induction d generalizing j with
  | zero =>
      left
      intro q hq
      have hq0 : q = 0 := by omega
      subst q
      simpa using hstart
  | succ d ih =>
      by_cases hnext : e (j+1) = m.bar (e (i+d))
      · have hinner := ih (j := j+1) (by omega) hnext
        rcases hinner with htrace | hoverwrite
        · left
          intro q hq
          by_cases hq0 : q = 0
          · subst q
            simpa using hstart
          · obtain ⟨r, hr⟩ : ∃ r, q = r+1 := ⟨q-1, by omega⟩
            subst q
            have h := htrace r (by omega)
            have hidx : j + (r+1) = (j+1)+r := by omega
            have hsub : d+1-(r+1) = d-r := by omega
            rw [hidx]
            rw [hsub]
            exact h
        · right
          obtain ⟨q, t, hqd, hprefix, hfail,
            hlow, hhigh, hp, hc, hlast⟩ := hoverwrite
          refine ⟨q+1, t, by omega, ?_, ?_, by omega, by omega,
            hp, ?_, ?_⟩
          · intro r hr
            by_cases hr0 : r = 0
            · subst r
              simpa using hstart
            · obtain ⟨s, hs⟩ : ∃ s, r = s+1 := ⟨r-1, by omega⟩
              subst r
              have h := hprefix s (by omega)
              have hidx : j + (s+1) = (j+1)+s := by omega
              have hsub : d+1-(s+1) = d-s := by omega
              rw [hidx, hsub]
              exact h
          · have hidx : j+(q+1)+1 = (j+1)+q+1 := by omega
            have hsub : d+1-(q+1)-1 = d-q-1 := by omega
            rw [hidx, hsub]
            exact hfail
          · simpa [writerAt] using hc
          · intro s hts hsj hprod
            exact hlast s hts (by omega) hprod
      · right
        have hw := (witness m e r0 hrun hr0 (i+d)).1
        have hcurrent :
            m.cellOf (e j) = m.star (m.cellOf (e (i+d))) := by
          rw [hstart]
          exact hw
        have hreadCell :
            m.star (m.cellOf (e j)) = m.cellOf (e (i+d)) := by
          rw [hcurrent, m.star_invol]
        have hregNe :
            reg m e r0 j (m.cellOf (e (i+d))) ≠ e (i+d) := by
          intro heq
          apply hnext
          rw [hrun j, hreadCell, heq]
        have hbase :
            reg m e r0 (i+d) (m.cellOf (e (i+d))) = e (i+d) :=
          reg_write m e r0 rfl
        have hchanged :
            reg m e r0 j (m.cellOf (e (i+d))) ≠
              reg m e r0 (i+d) (m.cellOf (e (i+d))) := by
          rw [hbase]
          exact hregNe
        obtain ⟨t, ht0, ht1, hp, hc, hlast⟩ :=
          change_has_last_productive_write m e r0 (by omega) hchanged
        refine ⟨0, t, by omega, ?_, ?_, ?_, ?_, hp, ?_, ?_⟩
        · intro r hr
          have hr0 : r = 0 := by omega
          subst r
          simpa using hstart
        · simpa using hnext
        · simpa using ht0
        · simpa using ht1
        · simpa [writerAt] using hc
        · intro s hts hsj hprod
          exact hlast s hts (by simpa using hsj) hprod

/-- Projection of `bar_retrace_or_first_overwrite` retaining only the exact
retrace or the named overwrite witness. -/
theorem bar_retrace_or_overwrite
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j d : Nat}
    (hij : i + d ≤ j)
    (hstart : e j = m.bar (e (i+d))) :
    (∀ q, q ≤ d →
      e (j+q) = m.bar (e (i + (d-q)))) ∨
    ∃ q t, q < d ∧
      i + (d-q-1) ≤ t ∧ t < j+q ∧
      ProductiveStep m e r0 t ∧
      writerAt m e t = m.cellOf (e (i + (d-q-1))) := by
  rcases bar_retrace_or_first_overwrite m e r0 hrun hr0 hij hstart with
    htrace | ⟨q, t, hq, _hprefix, _hfail, hlow, hhigh,
      hp, hc, _hlast⟩
  · exact Or.inl htrace
  · exact Or.inr ⟨q, t, hq, hlow, hhigh, hp, hc⟩

end Echo
