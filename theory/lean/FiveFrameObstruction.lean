import SelfEpochAmortization
import RepeatedNoveltyDecomposition

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


def FiveFrameSerialBreak
    (z₀ a₁ a₂ a₃ a₄ : Nat) : Prop :=
  z₀ ≤ a₁ ∨ z₀ ≤ a₂ ∨ z₀ ≤ a₃ ∨ z₀ ≤ a₄


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
