import SelfEpochAmortization
import TripleInterlacementObstruction
import ManufacturedPairNovelty

/-!
# Five closing frames reduce to a triple obstruction

This file is a raw-`Wiring` order reduction for the remaining finite
alternation problem. It does not assume periodicity and it does not assert
`FiveRepeatedWriterNovelty`.

The live decomposition and triple-obstruction libraries are imported
together. Their curve relations have distinct names, so the raw endpoint
order below can be consumed directly by the certified `ABCABC` programme.

Every repeated-writer novelty is packaged with the proved
fresh-or-interlacing rerouter supplied by
`RawRepeatedWriterNovelAt.open_rerouting_decomposition`. For five such
events in increasing closing-time order, their last-writer openings are
pairwise distinct. Consequently either a later frame starts after the
first close (a genuine serial break), or the five overlapping openings
contain a monotone triple. The increasing triple is the endpoint order
`ABCABC`; the decreasing triple is a strict three-frame nest.
-/

namespace GeneralN

/-- A repeated novelty's parity-chosen open rerouting frame. The shape is
the proved fresh-or-interlacing dichotomy; the chosen rerouter has no
nested alternative. -/
structure RawNovelClosingFrame
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (left reroute right : Nat) : Prop where
  outer : RawLastWriterFrame w N start left right
  reroute_productive : RawProductiveAt w N start reroute
  different_writer :
    rawWriterAt w start reroute ≠ rawWriterAt w start right
  no_same_rerouter_before : ∀ j, left < j → j < reroute →
    RawProductiveAt w N start j →
    rawWriterAt w start j ≠ rawWriterAt w start reroute
  shape : RawOpenReroutingShape w N start left reroute right

/-- Package the open-frame decomposition as one existential witness. -/
theorem RawRepeatedWriterNovelAt.novelClosingFrame
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {right : Nat}
    (h : RawRepeatedWriterNovelAt w N start right) :
    ∃ left reroute, RawNovelClosingFrame w N start left reroute right := by
  obtain ⟨left, reroute, outer, productive, different,
      noEarlier, shape⟩ := h.open_rerouting_decomposition hN
  exact ⟨left, reroute, {
    outer := outer
    reroute_productive := productive
    different_writer := different
    no_same_rerouter_before := noEarlier
    shape := shape
  }⟩

/-- Last-writer frames with strictly ordered closing times cannot share an
opening. If they did, the first close would be a forbidden intervening
write in the second frame. -/
theorem rawLastWriterFrame_open_ne_of_close_lt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {leftA rightA leftB rightB : Nat}
    (hclose : rightA < rightB)
    (A : RawLastWriterFrame w N start leftA rightA)
    (B : RawLastWriterFrame w N start leftB rightB) :
    leftA ≠ leftB := by
  intro heq
  have hwriter : rawWriterAt w start rightA =
      rawWriterAt w start rightB := by
    calc
      rawWriterAt w start rightA = rawWriterAt w start leftA :=
        A.same_writer.symm
      _ = rawWriterAt w start leftB := by rw [heq]
      _ = rawWriterAt w start rightB := B.same_writer
  have hopen : leftB < rightA := by
    rw [← heq]
    exact A.order
  exact B.no_same_writer_between rightA hopen hclose
    A.close_productive hwriter

/-! ## The adversarial serial `C,D,C` module -/


private theorem grooved_passages_physicalTrace
    (w : Wiring) (u : Tongues) (p x q : Nat) (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hfinal : w.link (lastPassageExit x rest) = some q) :
    PhysicalTrace w (p, u) ((p, x) :: rest) (q, u) := by
  induction rest generalizing p x with
  | nil =>
      have hhead := hgrooved (p, x) (by simp)
      have hfwd := groove_forward hhead
      exact PhysicalTrace.cons hfwd
        (by simpa [lastPassageExit] using hfinal)
        (PhysicalTrace.nil (q, u))
  | cons passage rest ih =>
      rcases passage with ⟨r, y⟩
      have hxy : w.link x = some r := hlinked.1
      have htailLinked : LinkedPassages w ((r, y) :: rest) :=
        hlinked.2
      have htailGrooved : PassagesGrooved u ((r, y) :: rest) := by
        intro passage hp
        exact hgrooved passage (List.mem_cons_of_mem _ hp)
      have htailFinal : w.link (lastPassageExit y rest) = some q := by
        simpa [lastPassageExit] using hfinal
      have htail := ih r y htailLinked htailGrooved htailFinal
      have hhead := hgrooved (p, x) (by simp)
      exact PhysicalTrace.cons (groove_forward hhead) hxy htail



def FiveFrameSerialBreak
    (z₀ a₁ a₂ a₃ a₄ : Nat) : Prop :=
  z₀ ≤ a₁ ∨ z₀ ≤ a₂ ∨ z₀ ≤ a₃ ∨ z₀ ≤ a₄


private theorem rawProductiveAt_rebase
    {w : Wiring} {N shift time : Nat}
    {start middle : Nat × Tongues}
    (hshift : shift ≤ time)
    (hreach : stepN w shift start = some middle)
    (hprod : RawProductiveAt w N start time) :
    RawProductiveAt w N middle (time - shift) := by
  let d := time - shift
  have htime : shift + d = time := by
    dsimp [d]
    omega
  have hlocalPost : ∃ finish,
      stepN w (d + 1) middle = some finish := by
    obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hprod.1
    refine ⟨finish, ?_⟩
    rw [stepN_shift_eq hreach]
    have hsum : shift + (d + 1) = time + 1 := by omega
    rw [hsum]
    exact hfinish
  have hiff := RawProductiveAt.shift_iff (N := N) hreach hlocalPost
  rw [htime] at hiff
  exact hiff.mpr hprod

/-- Writer names rebase literally at a productive event. -/
private theorem rawWriterAt_rebase
    {w : Wiring} {N shift time : Nat}
    {start middle : Nat × Tongues}
    (hshift : shift ≤ time)
    (hreach : stepN w shift start = some middle)
    (hprod : RawProductiveAt w N start time) :
    rawWriterAt w middle (time - shift) =
      rawWriterAt w start time := by
  let d := time - shift
  have htime : shift + d = time := by
    dsimp [d]
    omega
  have hlocalProd := rawProductiveAt_rebase hshift hreach hprod
  obtain ⟨post, hpost⟩ := Option.isSome_iff_exists.mp hlocalProd.1
  obtain ⟨current, hcurrent⟩ := stepN_prefix_some
    (d := d) (K := d + 1) (by omega) hpost
  have hwriter := rawWriterAt_shift_eq hreach ⟨current, hcurrent⟩
  rw [htime] at hwriter
  exact hwriter

/-- A last-writer frame whose opening is after a reached suffix boundary is
still a last-writer frame in local suffix time. -/
private theorem RawLastWriterFrame.rebase
    {w : Wiring} {N shift left right : Nat}
    {start middle : Nat × Tongues}
    (F : RawLastWriterFrame w N start left right)
    (hshift : shift ≤ left)
    (hreach : stepN w shift start = some middle) :
    RawLastWriterFrame w N middle
      (left - shift) (right - shift) := by
  let localLeft := left - shift
  let localRight := right - shift
  have hleftTime : shift + localLeft = left := by
    dsimp [localLeft]
    omega
  have hrightTime : shift + localRight = right := by
    dsimp [localRight]
    have hright := F.order
    omega
  have hopen := rawProductiveAt_rebase hshift hreach F.open_productive
  have hshiftRight : shift ≤ right := by omega
  have hclose := rawProductiveAt_rebase
    hshiftRight hreach F.close_productive
  have hwriterOpen := rawWriterAt_rebase
    hshift hreach F.open_productive
  have hwriterClose := rawWriterAt_rebase
    hshiftRight hreach F.close_productive
  refine {
    order := by
      have hsum : shift + localLeft < shift + localRight := by
        rw [hleftTime, hrightTime]
        exact F.order
      omega
    open_productive := by simpa [localLeft] using hopen
    close_productive := by simpa [localRight] using hclose
    same_writer := ?_
    no_same_writer_between := ?_
  }
  · simpa [localLeft, localRight] using
      hwriterOpen.trans (F.same_writer.trans hwriterClose.symm)
  · intro j hjLeft hjRight hjProd
    have hjPost : ∃ finish,
        stepN w (j + 1) middle = some finish :=
      Option.isSome_iff_exists.mp hjProd.1
    have hjGlobalProd :
        RawProductiveAt w N start (shift + j) :=
      (RawProductiveAt.shift_iff hreach hjPost).mp hjProd
    have hjCurrent : ∃ current,
        stepN w j middle = some current := by
      obtain ⟨finish, hfinish⟩ := hjPost
      exact stepN_prefix_some (d := j) (K := j + 1)
        (by omega) hfinish
    have hjWriter := rawWriterAt_shift_eq hreach hjCurrent
    have hno := F.no_same_writer_between (shift + j)
      (by omega) (by omega) hjGlobalProd
    intro heq
    apply hno
    calc
      rawWriterAt w start (shift + j) =
          rawWriterAt w middle j := hjWriter.symm
      _ = rawWriterAt w middle localRight := by
        simpa [localRight] using heq
      _ = rawWriterAt w start right := by
        simpa [localRight] using hwriterClose

/-- A globally novel repeated close remains a novel repeated close after
rebasing at any boundary before its certified last-writer opening.  The
opening itself supplies the earlier local occurrence, and the local history
is a suffix of the global history. -/
private theorem RawRepeatedWriterNovelAt.rebase_after_frame
    {w : Wiring} {N shift left right : Nat}
    {start middle : Nat × Tongues}
    (H : RawRepeatedWriterNovelAt w N start right)
    (F : RawLastWriterFrame w N start left right)
    (hshift : shift ≤ left)
    (hreach : stepN w shift start = some middle) :
    RawRepeatedWriterNovelAt w N middle (right - shift) := by
  let localLeft := left - shift
  let localRight := right - shift
  have hleftTime : shift + localLeft = left := by
    dsimp [localLeft]
    omega
  have hrightTime : shift + localRight = right := by
    dsimp [localRight]
    have hright := F.order
    omega
  have hpostTime : shift + (localRight + 1) = right + 1 := by
    calc
      shift + (localRight + 1) = (shift + localRight) + 1 :=
        (Nat.add_assoc shift localRight 1).symm
      _ = right + 1 := congrArg (fun t => t + 1) hrightTime
  have localFrame := F.rebase hshift hreach
  refine ⟨localFrame.close_productive, ?_, ?_⟩
  · intro hfirst
    have hne := hfirst.2 localLeft localFrame.order
      localFrame.open_productive
    exact hne localFrame.same_writer
  · intro hseen
    obtain ⟨j, hj, hvector⟩ := List.mem_map.mp hseen
    have hjLt : j < localRight + 1 := List.mem_range.mp hj
    obtain ⟨post, hpost⟩ :=
      Option.isSome_iff_exists.mp localFrame.close_productive.1
    obtain ⟨earlier, hearlier⟩ := stepN_prefix_some
      (d := j) (K := localRight + 1) (by omega) hpost
    have hpostShift := restrictedTonguesAt_shift_eq
      (N := N) hreach ⟨post, hpost⟩
    have hearlierShift := restrictedTonguesAt_shift_eq
      (N := N) hreach ⟨earlier, hearlier⟩
    apply H.2.2
    apply List.mem_map.mpr
    refine ⟨shift + j, List.mem_range.mpr (by omega), ?_⟩
    calc
      restrictedTonguesAt w N start (shift + j) =
          restrictedTonguesAt w N middle j := hearlierShift.symm
      _ = restrictedTonguesAt w N middle (localRight + 1) := hvector
      _ = restrictedTonguesAt w N start
          (shift + (localRight + 1)) := hpostShift
      _ = restrictedTonguesAt w N start (right + 1) := by rw [hpostTime]

theorem self_link_exit_bounces
    {w : Wiring} {before after : Nat × Tongues}
    (hstep : step w before = some after)
    (hself : w.link (exitPort before) = some (exitPort before)) :
    step w after =
      (w.link before.1).map (fun q => (q, after.2)) := by
  have hparts := step_some_parts hstep
  have hentry : after.1 = exitPort before := by
    rw [hself] at hparts
    exact Option.some.inj hparts.1.symm
  have hback := (step_grooves hstep).1
  unfold step
  rw [hentry, hback]

/-- A self-linked branch, with its stem connected to `outside`, is a
two-step identity reflector whenever that branch is selected. This is the
local lobe/reflector theorem needed for the self-link branch of `StateLaw`;
it is not an irreflexivity assumption. -/
theorem self_linked_branch_is_identity_reflector
    {w : Wiring} {branch outside : Nat}
    (hbranch : branch % 3 ≠ 0)
    (hself : w.link branch = some branch)
    (hmouth : w.link (3 * (branch / 3)) = some outside) :
    IsReflector w (3 * (branch / 3)) outside 2
      (fun state => state (branch / 3) = bval branch)
      (fun state => state) := by
  intro state hselected
  have hpin : pin state branch = state :=
    pin_of_agrees hselected
  have hgroove :
      arrive state branch = (3 * (branch / 3), state) := by
    simp [arrive, hbranch, hpin]
  obtain ⟨hstep, _⟩ :=
    self_edge_groove_isReflector w hself hmouth state hgroove
  exact ⟨hstep, hselected⟩


def EndpointABCABC
    (a₀ z₀ a₁ z₁ a₂ z₂ : Nat) : Prop :=
  a₀ < a₁ ∧ a₁ < a₂ ∧ a₂ < z₀ ∧ z₀ < z₁ ∧ z₁ < z₂

/-- Three strictly nested closing frames:
`a₂ < a₁ < a₀ < z₀ < z₁ < z₂`. -/
def EndpointStrictNest
    (a₀ z₀ a₁ z₁ a₂ z₂ : Nat) : Prop :=
  a₂ < a₁ ∧ a₁ < a₀ ∧ a₀ < z₀ ∧ z₀ < z₁ ∧ z₁ < z₂

def EndpointTripleOutcome
    (a₀ z₀ a₁ z₁ a₂ z₂ : Nat) : Prop :=
  EndpointABCABC a₀ z₀ a₁ z₁ a₂ z₂ ∨
  EndpointStrictNest a₀ z₀ a₁ z₁ a₂ z₂

/-- One of the ten chronological triples selected from five frames is an
`ABCABC` interlacement or a strict nest. -/
def FiveFrameABCABC
    (a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat) : Prop :=
  EndpointABCABC a₀ z₀ a₁ z₁ a₂ z₂ ∨
  EndpointABCABC a₀ z₀ a₁ z₁ a₃ z₃ ∨
  EndpointABCABC a₀ z₀ a₁ z₁ a₄ z₄ ∨
  EndpointABCABC a₀ z₀ a₂ z₂ a₃ z₃ ∨
  EndpointABCABC a₀ z₀ a₂ z₂ a₄ z₄ ∨
  EndpointABCABC a₀ z₀ a₃ z₃ a₄ z₄ ∨
  EndpointABCABC a₁ z₁ a₂ z₂ a₃ z₃ ∨
  EndpointABCABC a₁ z₁ a₂ z₂ a₄ z₄ ∨
  EndpointABCABC a₁ z₁ a₃ z₃ a₄ z₄ ∨
  EndpointABCABC a₂ z₂ a₃ z₃ a₄ z₄

def FiveFrameStrictNest
    (a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat) : Prop :=
  EndpointStrictNest a₀ z₀ a₁ z₁ a₂ z₂ ∨
  EndpointStrictNest a₀ z₀ a₁ z₁ a₃ z₃ ∨
  EndpointStrictNest a₀ z₀ a₁ z₁ a₄ z₄ ∨
  EndpointStrictNest a₀ z₀ a₂ z₂ a₃ z₃ ∨
  EndpointStrictNest a₀ z₀ a₂ z₂ a₄ z₄ ∨
  EndpointStrictNest a₀ z₀ a₃ z₃ a₄ z₄ ∨
  EndpointStrictNest a₁ z₁ a₂ z₂ a₃ z₃ ∨
  EndpointStrictNest a₁ z₁ a₂ z₂ a₄ z₄ ∨
  EndpointStrictNest a₁ z₁ a₃ z₃ a₄ z₄ ∨
  EndpointStrictNest a₂ z₂ a₃ z₃ a₄ z₄

def FiveFrameTripleOutcome
    (a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat) : Prop :=
  FiveFrameABCABC a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ ∨
  FiveFrameStrictNest a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄

private theorem fiveOutcome012
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inl habc)
  · exact Or.inr (Or.inl hnest)

private theorem fiveOutcome013
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₀ z₀ a₁ z₁ a₃ z₃) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inr (Or.inl habc))
  · exact Or.inr (Or.inr (Or.inl hnest))

private theorem fiveOutcome123
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₁ z₁ a₂ z₂ a₃ z₃) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl habc)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl hnest)))))))

private theorem fiveOutcome134
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₁ z₁ a₃ z₃ a₄ z₄) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl habc)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl hnest)))))))))

private theorem fiveOutcome234
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₂ z₂ a₃ z₃ a₄ z₄) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr habc)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr hnest)))))))))

/-- The order-theoretic core: five distinct openings before the first of
five ordered closings contain an increasing or decreasing triple. This is
the five-term Erdős-Szekeres argument discharged in Presburger arithmetic,
not an enumeration of switch systems. -/
theorem five_distinct_common_openings_have_triple
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (hz01 : z₀ < z₁) (hz12 : z₁ < z₂)
    (hz23 : z₂ < z₃) (hz34 : z₃ < z₄)
    (ha0 : a₀ < z₀)
    (hcommon : a₁ < z₀ ∧ a₂ < z₀ ∧ a₃ < z₀ ∧ a₄ < z₀)
    (hn01 : a₀ ≠ a₁) (hn02 : a₀ ≠ a₂)
    (hn03 : a₀ ≠ a₃) (hn04 : a₀ ≠ a₄)
    (hn12 : a₁ ≠ a₂) (hn13 : a₁ ≠ a₃)
    (hn14 : a₁ ≠ a₄) (hn23 : a₂ ≠ a₃)
    (hn24 : a₂ ≠ a₄) (hn34 : a₃ ≠ a₄) :
    FiveFrameTripleOutcome
      a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  by_cases h01 : a₀ < a₁
  · by_cases h12 : a₁ < a₂
    · apply fiveOutcome012
      left
      unfold EndpointABCABC
      omega
    · by_cases h23 : a₂ < a₃
      · by_cases h34 : a₃ < a₄
        · apply fiveOutcome234
          left
          unfold EndpointABCABC
          omega
        · by_cases h13 : a₁ < a₃
          · apply fiveOutcome013
            left
            unfold EndpointABCABC
            omega
          · apply fiveOutcome134
            right
            unfold EndpointStrictNest
            omega
      · apply fiveOutcome123
        right
        unfold EndpointStrictNest
        omega
  · by_cases h12 : a₁ < a₂
    · by_cases h23 : a₂ < a₃
      · apply fiveOutcome123
        left
        unfold EndpointABCABC
        omega
      · by_cases h34 : a₃ < a₄
        · by_cases h31 : a₃ < a₁
          · apply fiveOutcome013
            right
            unfold EndpointStrictNest
            omega
          · apply fiveOutcome134
            left
            unfold EndpointABCABC
            omega
        · apply fiveOutcome234
          right
          unfold EndpointStrictNest
          omega
    · apply fiveOutcome012
      right
      unfold EndpointStrictNest
      omega

/-- Five common-overlap raw last-writer frames therefore contain the exact
triple endpoint pattern needed by the curve-shrink/`ABCABC` obstruction. -/
theorem five_common_raw_closing_frames_have_triple
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {a₀ q₀ z₀ a₁ q₁ z₁ a₂ q₂ z₂ a₃ q₃ z₃ a₄ q₄ z₄ : Nat}
    (hz01 : z₀ < z₁) (hz12 : z₁ < z₂)
    (hz23 : z₂ < z₃) (hz34 : z₃ < z₄)
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hcommon : a₁ < z₀ ∧ a₂ < z₀ ∧ a₃ < z₀ ∧ a₄ < z₀) :
    FiveFrameTripleOutcome
      a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  have hz02 : z₀ < z₂ := Nat.lt_trans hz01 hz12
  have hz03 : z₀ < z₃ := Nat.lt_trans hz02 hz23
  have hz04 : z₀ < z₄ := Nat.lt_trans hz03 hz34
  have hz13 : z₁ < z₃ := Nat.lt_trans hz12 hz23
  have hz14 : z₁ < z₄ := Nat.lt_trans hz13 hz34
  have hz24 : z₂ < z₄ := Nat.lt_trans hz23 hz34
  exact five_distinct_common_openings_have_triple
    hz01 hz12 hz23 hz34 F₀.outer.order hcommon
    (rawLastWriterFrame_open_ne_of_close_lt hz01 F₀.outer F₁.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz02 F₀.outer F₂.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz03 F₀.outer F₃.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz04 F₀.outer F₄.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz12 F₁.outer F₂.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz13 F₁.outer F₃.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz14 F₁.outer F₄.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz23 F₂.outer F₃.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz24 F₂.outer F₄.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz34 F₃.outer F₄.outer)


theorem five_repeated_novelties_serial_or_triple
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {z₀ z₁ z₂ z₃ z₄ : Nat}
    (hz01 : z₀ < z₁) (hz12 : z₁ < z₂)
    (hz23 : z₂ < z₃) (hz34 : z₃ < z₄)
    (h₀ : RawRepeatedWriterNovelAt w N start z₀)
    (h₁ : RawRepeatedWriterNovelAt w N start z₁)
    (h₂ : RawRepeatedWriterNovelAt w N start z₂)
    (h₃ : RawRepeatedWriterNovelAt w N start z₃)
    (h₄ : RawRepeatedWriterNovelAt w N start z₄) :
    ∃ a₀ q₀ a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄,
      RawNovelClosingFrame w N start a₀ q₀ z₀ ∧
      RawNovelClosingFrame w N start a₁ q₁ z₁ ∧
      RawNovelClosingFrame w N start a₂ q₂ z₂ ∧
      RawNovelClosingFrame w N start a₃ q₃ z₃ ∧
      RawNovelClosingFrame w N start a₄ q₄ z₄ ∧
      (FiveFrameSerialBreak z₀ a₁ a₂ a₃ a₄ ∨
       FiveFrameTripleOutcome
         a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄) := by
  obtain ⟨a₀, q₀, F₀⟩ := h₀.novelClosingFrame hN
  obtain ⟨a₁, q₁, F₁⟩ := h₁.novelClosingFrame hN
  obtain ⟨a₂, q₂, F₂⟩ := h₂.novelClosingFrame hN
  obtain ⟨a₃, q₃, F₃⟩ := h₃.novelClosingFrame hN
  obtain ⟨a₄, q₄, F₄⟩ := h₄.novelClosingFrame hN
  refine ⟨a₀, q₀, a₁, q₁, a₂, q₂, a₃, q₃, a₄, q₄,
    F₀, F₁, F₂, F₃, F₄, ?_⟩
  by_cases hcommon : a₁ < z₀ ∧ a₂ < z₀ ∧ a₃ < z₀ ∧ a₄ < z₀
  · exact Or.inr (five_common_raw_closing_frames_have_triple
      hz01 hz12 hz23 hz34 F₀ F₁ F₂ F₃ F₄ hcommon)
  · left
    unfold FiveFrameSerialBreak
    omega

end GeneralN

namespace Echo

end Echo
