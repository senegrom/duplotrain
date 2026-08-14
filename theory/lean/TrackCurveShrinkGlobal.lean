import TrackCurveGrowth

/-!
# Finite train-curve growth between self pivots

Koizumi's empty-curve argument has a dual formulation from the train's
point of view.  At a productive endpoint pivot which does not join two
points of the train's current selected curve, the whole current curve is
carried into the next curve and at least the pivot stem is added.

This file turns the local `CurveReach` theorem into a finite, raw-`stepN`
count.  In particular, a consecutive productive prefix containing no
self-pivot has length at most `3*N`, because there are only `3*N` physical
ports.  This is an unconditional theorem about that raw dynamical case, not
an assumed global decomposition.  The complementary self-pivot nesting is
still the obstruction to applying the measure across an arbitrary run.
-/

namespace GeneralN

/-- The represented ports on one selected train curve. -/
noncomputable def finiteCurvePorts
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) : List Nat := by
  classical
  exact (List.range (3 * N)).filter
    (fun p => decide (CurveReach w u root p))

theorem mem_finiteCurvePorts_iff
    {w : Wiring} {N : Nat} {u : Tongues} {root p : Nat} :
    p ∈ finiteCurvePorts w N u root ↔
      p < 3 * N ∧ CurveReach w u root p := by
  classical
  simp [finiteCurvePorts]

private theorem nodup_filter_nat_curve (pred : Nat → Bool) :
    ∀ {xs : List Nat}, xs.Nodup → (xs.filter pred).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : pred x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hmem => hnd.1 ((List.mem_filter.mp hmem).1),
            ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

theorem finiteCurvePorts_nodup
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) :
    (finiteCurvePorts w N u root).Nodup := by
  classical
  unfold finiteCurvePorts
  exact nodup_filter_nat_curve _ List.nodup_range

theorem finiteCurvePorts_length_le
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) :
    (finiteCurvePorts w N u root).length ≤ 3 * N := by
  classical
  unfold finiteCurvePorts
  have h := List.length_filter_le
    (fun p => decide (CurveReach w u root p)) (List.range (3 * N))
  simpa using h

private theorem nodup_subset_length_curve
    {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs ys : List α},
      xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length := by
  intro xs
  induction xs with
  | nil => intro ys _ _; exact Nat.zero_le _
  | cons x rest ih =>
      intro ys hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hrest : ∀ y ∈ rest, y ∈ ys.erase x := by
        intro y hy
        have hy' : y ∈ ys := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun heq => hnd.1 (heq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hy'
      have hle := ih hnd.2 hrest
      have herase : (ys.erase x).length = ys.length - 1 :=
        List.length_erase_of_mem hx
      have hpositive : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

private theorem length_lt_of_strict_subset_curve
    {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α}
    (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys)
    (y : α) (hy : y ∈ ys) (hnot : y ∉ xs) :
    xs.length < ys.length := by
  have hcons : (y :: xs).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hnot, hnd⟩
  have hconsSub : ∀ x ∈ y :: xs, x ∈ ys := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hy
    · exact hsub x hx
  have hle := nodup_subset_length_curve hcons hconsSub
  simp only [List.length_cons] at hle
  omega

/-! ## Endpoint capacity of one selected curve -/

/-- A finite walk in the selected curve graph. -/
def FiniteCurveChain (w : Wiring) (u : Tongues) : List Nat → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest =>
      CurveEdge w u p q ∧ FiniteCurveChain w u (q :: rest)

private theorem finiteCurveChain_tail
    {w : Wiring} {u : Tongues} {p : Nat} {xs : List Nat}
    (h : FiniteCurveChain w u (p :: xs)) :
    FiniteCurveChain w u xs := by
  cases xs with
  | nil => trivial
  | cons q rest => exact h.2

private theorem finiteCurveChain_suffix
    {w : Wiring} {u : Tongues} :
    ∀ (pre xs : List Nat),
      FiniteCurveChain w u (pre ++ xs) →
      FiniteCurveChain w u xs := by
  intro pre
  induction pre with
  | nil => intro xs h; simpa using h
  | cons p pre ih =>
      intro xs h
      exact ih xs (finiteCurveChain_tail h)

private theorem finiteCurveChain_append_one
    {w : Wiring} {u : Tongues} {p q : Nat} :
    ∀ {xs : List Nat},
      FiniteCurveChain w u xs →
      xs.getLast? = some p →
      CurveEdge w u p q →
      FiniteCurveChain w u (xs ++ [q]) := by
  intro xs hchain hlast hedge
  induction xs with
  | nil => simp at hlast
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton] at hlast
          injection hlast with hap
          subst p
          exact ⟨hedge, trivial⟩
      | cons b tail =>
          have hparts : CurveEdge w u a b ∧
              FiniteCurveChain w u (b :: tail) := hchain
          have hlastTail : (b :: tail).getLast? = some p := by
            simpa using hlast
          have htail := ih hparts.2 hlastTail
          exact ⟨hparts.1, htail⟩

private theorem finiteCurveChain_reverse
    {w : Wiring} {u : Tongues} :
    ∀ {xs : List Nat}, FiniteCurveChain w u xs →
      FiniteCurveChain w u xs.reverse := by
  intro xs h
  induction xs with
  | nil => trivial
  | cons p rest ih =>
      cases rest with
      | nil => trivial
      | cons q tail =>
          have hparts : CurveEdge w u p q ∧
              FiniteCurveChain w u (q :: tail) := h
          have hrev := ih hparts.2
          have hlast : (q :: tail).reverse.getLast? = some q := by simp
          simpa using finiteCurveChain_append_one hrev hlast
            (curveEdge_symm hparts.1)

/-- A repetition-free finite path between two ports of a selected curve. -/
structure FiniteSimpleCurvePath
    (w : Wiring) (u : Tongues) (start finish : Nat) where
  vertices : List Nat
  nodup : vertices.Nodup
  first : vertices.head? = some start
  last : vertices.getLast? = some finish
  chain : FiniteCurveChain w u vertices

private theorem reverseSimplePath_of
    {w : Wiring} {u : Tongues} {root p : Nat}
    (h : CurveReach w u root p) :
    ∃ path : FiniteSimpleCurvePath w u p root, True := by
  induction h with
  | refl =>
      exact ⟨{
        vertices := [root]
        nodup := by simp
        first := by simp
        last := by simp
        chain := trivial
      }, trivial⟩
  | @step p q hreach hedge ih =>
      obtain ⟨path, _⟩ := ih
      by_cases hmem : q ∈ path.vertices
      · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
        let suffix := q :: post
        have hchain : FiniteCurveChain w u suffix := by
          apply finiteCurveChain_suffix pre
          simpa [suffix, hsplit] using path.chain
        have hnodup : suffix.Nodup := by
          have hnd := path.nodup
          rw [hsplit, List.nodup_append] at hnd
          simpa [suffix] using hnd.2.1
        have hlast : suffix.getLast? = some root := by
          have hp := path.last
          simpa [suffix, hsplit] using hp
        exact ⟨{
          vertices := suffix
          nodup := hnodup
          first := by simp [suffix]
          last := hlast
          chain := hchain
        }, trivial⟩
      · obtain ⟨rest, hvertices⟩ :=
          List.head?_eq_some_iff.mp path.first
        have hchain : FiniteCurveChain w u (q :: path.vertices) := by
          rw [hvertices]
          have htail : FiniteCurveChain w u (p :: rest) := by
            simpa [hvertices] using path.chain
          exact ⟨curveEdge_symm hedge, htail⟩
        exact ⟨{
          vertices := q :: path.vertices
          nodup := (List.nodup_cons.mpr ⟨hmem, path.nodup⟩)
          first := by simp
          last := by simpa [hvertices] using path.last
          chain := hchain
        }, trivial⟩

/-- Every `CurveReach` witness admits an ordinary finite simple path. -/
private theorem mem_reverse_curve {x : Nat} {xs : List Nat} :
    x ∈ xs.reverse ↔ x ∈ xs := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih, or_comm]

private theorem nodup_reverse_curve {xs : List Nat}
    (hnd : xs.Nodup) : xs.reverse.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.reverse_cons]
      apply List.nodup_append.mpr
      refine ⟨ih hnd.2, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro hax
      apply hnd.1
      rw [← hax]
      exact mem_reverse_curve.mp ha

theorem curveReach_finiteSimplePath
    {w : Wiring} {u : Tongues} {root p : Nat}
    (h : CurveReach w u root p) :
    Nonempty (FiniteSimpleCurvePath w u root p) := by
  obtain ⟨backward, _⟩ := reverseSimplePath_of h
  exact ⟨{
    vertices := backward.vertices.reverse
    nodup := nodup_reverse_curve backward.nodup
    first := by simpa using backward.last
    last := by simpa using backward.first
    chain := finiteCurveChain_reverse backward.chain
  }⟩

private theorem internalCurveEdge_unmatched_impossible
    (u : Tongues) (C q : Nat) :
    ¬ InternalCurveEdge u (unmatchedBranch u C) q := by
  intro h
  unfold InternalCurveEdge at h
  rw [arrive_unmatched_pivots] at h
  have hstate := congrArg (fun z : Nat × Tongues => z.2 C) h
  simp [flipAt] at hstate

/-- An unmatched branch has at most one curve neighbour: its external track
mate. -/
theorem unmatchedBranch_curveEdge_unique
    (w : Wiring) (u : Tongues) (C : Nat) {q r : Nat}
    (hq : CurveEdge w u (unmatchedBranch u C) q)
    (hr : CurveEdge w u (unmatchedBranch u C) r) : q = r := by
  rcases hq with hq | hq
  · rcases hr with hr | hr
    · exact Option.some.inj (hq.symm.trans hr)
    · exact (internalCurveEdge_unmatched_impossible u C r hr).elim
  · exact (internalCurveEdge_unmatched_impossible u C q hq).elim

/-- The selected curve graph has degree at most two. -/
theorem curveEdge_degree_le_two
    (w : Wiring) (u : Tongues) {p q r s : Nat}
    (hq : CurveEdge w u p q)
    (hr : CurveEdge w u p r)
    (hs : CurveEdge w u p s) :
    q = r ∨ q = s ∨ r = s := by
  have sameExternal : ∀ {a b},
      w.link p = some a → w.link p = some b → a = b := by
    intro a b ha hb
    exact Option.some.inj (ha.symm.trans hb)
  have sameInternal : ∀ {a b},
      InternalCurveEdge u p a → InternalCurveEdge u p b → a = b := by
    intro a b ha hb
    unfold InternalCurveEdge at ha hb
    have hpair := ha.symm.trans hb
    exact congrArg Prod.fst hpair
  rcases hq with hq | hq <;>
    rcases hr with hr | hr <;>
      rcases hs with hs | hs
  · exact Or.inl (sameExternal hq hr)
  · exact Or.inl (sameExternal hq hr)
  · exact Or.inr (Or.inl (sameExternal hq hs))
  · exact Or.inr (Or.inr (sameInternal hr hs))
  · exact Or.inr (Or.inr (sameExternal hr hs))
  · exact Or.inr (Or.inl (sameInternal hq hs))
  · exact Or.inl (sameInternal hq hr)
  · exact Or.inl (sameInternal hq hr)

private def CurvePrefixComparable (xs ys : List Nat) : Prop :=
  (∃ tail, ys = xs ++ tail) ∨ (∃ tail, xs = ys ++ tail)

private theorem curvePrefixComparable_cons
    {x : Nat} {xs ys : List Nat}
    (h : CurvePrefixComparable xs ys) :
    CurvePrefixComparable (x :: xs) (x :: ys) := by
  rcases h with ⟨tail, htail⟩ | ⟨tail, htail⟩
  · left
    exact ⟨tail, by simp [htail]⟩
  · right
    exact ⟨tail, by simp [htail]⟩

/-- Once a simple curve path has traversed `prev--cur`, its remaining tail is
forced until one of two compared paths ends.  This is the non-backtracking
form of the degree-two property. -/
private theorem simple_curve_tails_prefix_after_edge
    (w : Wiring) (u : Tongues) :
    ∀ (prev cur : Nat) (xs ys : List Nat),
      CurveEdge w u prev cur →
      (prev :: cur :: xs).Nodup →
      FiniteCurveChain w u (prev :: cur :: xs) →
      (prev :: cur :: ys).Nodup →
      FiniteCurveChain w u (prev :: cur :: ys) →
      CurvePrefixComparable xs ys := by
  intro prev cur xs
  induction xs generalizing prev cur with
  | nil =>
      intro ys _ _ _ _ _
      left
      exact ⟨ys, by simp⟩
  | cons x xs ih =>
      intro ys hprev hndx hchainx hndy hchainy
      cases ys with
      | nil =>
          right
          exact ⟨x :: xs, by simp⟩
      | cons y ys =>
          have hxEdge : CurveEdge w u cur x := hchainx.2.1
          have hyEdge : CurveEdge w u cur y := hchainy.2.1
          have hdegree := curveEdge_degree_le_two w u
            (curveEdge_symm hprev) hxEdge hyEdge
          have hprevX : prev ≠ x := by
            intro heq
            rw [List.nodup_cons] at hndx
            exact hndx.1 (by simp [heq])
          have hprevY : prev ≠ y := by
            intro heq
            rw [List.nodup_cons] at hndy
            exact hndy.1 (by simp [heq])
          have hxy : x = y := by
            rcases hdegree with h | h | h
            · exact (hprevX h).elim
            · exact (hprevY h).elim
            · exact h
          subst y
          have hndxTail : (cur :: x :: xs).Nodup :=
            (List.nodup_cons.mp hndx).2
          have hndyTail : (cur :: x :: ys).Nodup :=
            (List.nodup_cons.mp hndy).2
          have htail := ih cur x ys hxEdge
            hndxTail hchainx.2 hndyTail hchainy.2
          exact curvePrefixComparable_cons htail

/-- Two simple paths leaving the same unmatched branch are prefix-comparable.
The first edge is forced by endpoint degree one; all later edges are forced by
degree two and the prohibition on immediate backtracking from `Nodup`. -/
private theorem simple_curve_paths_prefix_from_unmatched
    (w : Wiring) (u : Tongues) (A : Nat) {xs ys : List Nat}
    (hndx : (unmatchedBranch u A :: xs).Nodup)
    (hchainx : FiniteCurveChain w u (unmatchedBranch u A :: xs))
    (hndy : (unmatchedBranch u A :: ys).Nodup)
    (hchainy : FiniteCurveChain w u (unmatchedBranch u A :: ys)) :
    CurvePrefixComparable
      (unmatchedBranch u A :: xs) (unmatchedBranch u A :: ys) := by
  cases xs with
  | nil =>
      left
      exact ⟨ys, by simp⟩
  | cons x xs =>
      cases ys with
      | nil =>
          right
          exact ⟨x :: xs, by simp⟩
      | cons y ys =>
          have hxParts : CurveEdge w u (unmatchedBranch u A) x ∧
              FiniteCurveChain w u (x :: xs) := hchainx
          have hyParts : CurveEdge w u (unmatchedBranch u A) y ∧
              FiniteCurveChain w u (y :: ys) := hchainy
          have hxy := unmatchedBranch_curveEdge_unique w u A
            hxParts.1 hyParts.1
          subst y
          have htail' := simple_curve_tails_prefix_after_edge w u
            (unmatchedBranch u A) x xs ys hxParts.1
            hndx hchainx hndy hchainy
          exact curvePrefixComparable_cons
            (curvePrefixComparable_cons htail')

private theorem finiteCurveChain_append_edge
    {w : Wiring} {u : Tongues} {p q : Nat} {rest : List Nat} :
    ∀ {xs : List Nat},
      xs.getLast? = some p →
      FiniteCurveChain w u (xs ++ (q :: rest)) →
      CurveEdge w u p q := by
  intro xs hlast hchain
  induction xs with
  | nil => simp at hlast
  | cons a xs ih =>
      cases xs with
      | nil =>
          simp only [List.getLast?_singleton] at hlast
          injection hlast with hap
          subst p
          exact hchain.1
      | cons b tail =>
          exact ih (by simpa using hlast) hchain.2

/-- A nontrivial simple path ending at an unmatched branch cannot be extended
past that branch without repeating its unique neighbour. -/
private theorem unmatched_endpoint_cannot_extend
    (w : Wiring) (u : Tongues) (A B q : Nat)
    {vertices tail : List Nat}
    (hAB : A ≠ B)
    (hfirst : vertices.head? = some (unmatchedBranch u A))
    (hlast : vertices.getLast? = some (unmatchedBranch u B))
    (hchain : FiniteCurveChain w u vertices)
    (hndExtended : (vertices ++ (q :: tail)).Nodup)
    (hchainExtended : FiniteCurveChain w u (vertices ++ (q :: tail))) :
    False := by
  have hboundary : CurveEdge w u (unmatchedBranch u B) q :=
    finiteCurveChain_append_edge hlast hchainExtended
  have hrevHead : vertices.reverse.head? =
      some (unmatchedBranch u B) := by
    simpa using hlast
  obtain ⟨rest, hrev⟩ := List.head?_eq_some_iff.mp hrevHead
  cases rest with
  | nil =>
      have horig : vertices = [unmatchedBranch u B] := by
        have h := congrArg List.reverse hrev
        simpa using h
      rw [horig] at hfirst
      simp only [List.head?_cons] at hfirst
      have hports := Option.some.inj hfirst
      apply hAB
      have hswitches := congrArg (fun p : Nat => p / 3) hports
      simpa [unmatchedBranch_switch] using hswitches.symm
  | cons r rs =>
      have hrevChain := finiteCurveChain_reverse hchain
      rw [hrev] at hrevChain
      have hback : CurveEdge w u (unmatchedBranch u B) r := hrevChain.1
      have hrq := unmatchedBranch_curveEdge_unique w u B hback hboundary
      have hrRev : r ∈ vertices.reverse := by rw [hrev]; simp
      have hr : r ∈ vertices := mem_reverse_curve.mp hrRev
      rw [List.nodup_append] at hndExtended
      have hrne : r ≠ q := hndExtended.2.2 r hr q (by simp)
      exact hrne hrq

/-- A selected curve contains unmatched branches belonging to at most two
switches.  Once one unmatched branch is fixed as an endpoint, any two other
unmatched endpoints in its component must coincide. -/
theorem connected_unmatched_endpoints_unique
    (w : Wiring) (u : Tongues) {A B C : Nat}
    (hAB : A ≠ B) (hAC : A ≠ C)
    (hB : CurveReach w u (unmatchedBranch u A) (unmatchedBranch u B))
    (hC : CurveReach w u (unmatchedBranch u A) (unmatchedBranch u C)) :
    B = C := by
  obtain ⟨pathB⟩ := curveReach_finiteSimplePath hB
  obtain ⟨pathC⟩ := curveReach_finiteSimplePath hC
  obtain ⟨xs, hx⟩ := List.head?_eq_some_iff.mp pathB.first
  obtain ⟨ys, hy⟩ := List.head?_eq_some_iff.mp pathC.first
  have hcomp := simple_curve_paths_prefix_from_unmatched w u A
    (by simpa [hx] using pathB.nodup)
    (by simpa [hx] using pathB.chain)
    (by simpa [hy] using pathC.nodup)
    (by simpa [hy] using pathC.chain)
  have hports : unmatchedBranch u B = unmatchedBranch u C := by
    rcases hcomp with ⟨tail, hprefix⟩ | ⟨tail, hprefix⟩
    · cases tail with
      | nil =>
          have heq : pathC.vertices = pathB.vertices := by
            simpa [hx, hy] using hprefix
          have hlastC := pathC.last
          rw [heq] at hlastC
          exact Option.some.inj (pathB.last.symm.trans hlastC)
      | cons q tail =>
          have hext : pathC.vertices = pathB.vertices ++ (q :: tail) := by
            simpa [hx, hy, List.cons_append] using hprefix
          exact (unmatched_endpoint_cannot_extend w u A B q hAB
            pathB.first pathB.last pathB.chain
            (by simpa [hext] using pathC.nodup)
            (by simpa [hext] using pathC.chain)).elim
    · cases tail with
      | nil =>
          have heq : pathB.vertices = pathC.vertices := by
            simpa [hx, hy] using hprefix
          have hlastB := pathB.last
          rw [heq] at hlastB
          exact Option.some.inj (hlastB.symm.trans pathC.last)
      | cons q tail =>
          have hext : pathB.vertices = pathC.vertices ++ (q :: tail) := by
            simpa [hx, hy, List.cons_append] using hprefix
          exact (unmatched_endpoint_cannot_extend w u A C q hAC
            pathC.first pathC.last pathC.chain
            (by simpa [hext] using pathB.nodup)
            (by simpa [hext] using pathB.chain)).elim
  have hswitches := congrArg (fun p : Nat => p / 3) hports
  simpa [unmatchedBranch_switch] using hswitches

/-- The represented switches whose currently unmatched branch lies on one
selected curve. -/
noncomputable def finiteCurveEndpointWriters
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) : List Nat := by
  classical
  exact (List.range N).filter (fun C => decide
    (CurveReach w u root (unmatchedBranch u C)))

theorem mem_finiteCurveEndpointWriters_iff
    {w : Wiring} {N : Nat} {u : Tongues} {root C : Nat} :
    C ∈ finiteCurveEndpointWriters w N u root ↔
      C < N ∧ CurveReach w u root (unmatchedBranch u C) := by
  classical
  simp [finiteCurveEndpointWriters]

theorem finiteCurveEndpointWriters_nodup
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) :
    (finiteCurveEndpointWriters w N u root).Nodup := by
  classical
  unfold finiteCurveEndpointWriters
  exact nodup_filter_nat_curve _ List.nodup_range

/-- **Endpoint capacity.** Every finite selected component exposes unmatched
branches from at most two represented switches.  This is a theorem about the
raw union of the fixed track matching and the tongue-selected switch
matching; no trajectory or periodicity assumption is used. -/
theorem finiteCurveEndpointWriters_length_le_two
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) :
    (finiteCurveEndpointWriters w N u root).length ≤ 2 := by
  classical
  let endpoints := finiteCurveEndpointWriters w N u root
  change endpoints.length ≤ 2
  cases hlist : endpoints with
  | nil => simp
  | cons A rest =>
      have hA : A ∈ endpoints := by rw [hlist]; simp
      have hreachA := (mem_finiteCurveEndpointWriters_iff.mp hA).2
      by_cases hsecond : ∃ B, B ∈ endpoints ∧ B ≠ A
      · obtain ⟨B, hB, hBA⟩ := hsecond
        have hreachB := (mem_finiteCurveEndpointWriters_iff.mp hB).2
        have hABreach : CurveReach w u (unmatchedBranch u A)
            (unmatchedBranch u B) :=
          curveReach_trans (curveReach_symm hreachA) hreachB
        have hsubset : ∀ C ∈ endpoints, C ∈ [A, B] := by
          intro C hC
          by_cases hCA : C = A
          · simp [hCA]
          · have hreachC :=
                (mem_finiteCurveEndpointWriters_iff.mp hC).2
            have hACreach : CurveReach w u (unmatchedBranch u A)
                (unmatchedBranch u C) :=
              curveReach_trans (curveReach_symm hreachA) hreachC
            have hCB : C = B := by
              exact (connected_unmatched_endpoints_unique w u
                (Ne.symm hBA) (Ne.symm hCA) hABreach hACreach).symm
            simp [hCB]
        have hle := nodup_subset_length_curve
          (finiteCurveEndpointWriters_nodup w N u root) hsubset
        have hleE : endpoints.length ≤ [A, B].length := by
          change (finiteCurveEndpointWriters w N u root).length ≤
            [A, B].length
          exact hle
        rw [hlist] at hleE
        simpa using hleE
      · have hsubset : ∀ C ∈ endpoints, C ∈ [A] := by
          intro C hC
          have hCA : C = A := by
            apply Classical.byContradiction
            intro hne
            exact hsecond ⟨C, hC, hne⟩
          simp [hCA]
        have hle := nodup_subset_length_curve
          (finiteCurveEndpointWriters_nodup w N u root) hsubset
        have hleE : endpoints.length ≤ [A].length := by
          change (finiteCurveEndpointWriters w N u root).length ≤ [A].length
          exact hle
        rw [hlist] at hleE
        simp only [List.length_cons, List.length_nil, Nat.add_zero] at hleE ⊢
        omega

/-- A non-self productive endpoint pivot strictly enlarges the finite train
curve, even after re-rooting that curve at the next raw entry port. -/
theorem nonself_endpoint_pivot_finiteCurvePorts_growth
    {w : Wiring} {N C : Nat} {cur next : Nat × Tongues}
    (hC : C < N)
    (hstep : step w cur = some next)
    (hentry : cur.1 = unmatchedBranch cur.2 C)
    (hexit : exitPort cur = 3 * C)
    (hflip : next.2 = flipAt cur.2 C)
    (houtside : ¬ CurveReach w cur.2 cur.1 (3 * C)) :
    (finiteCurvePorts w N cur.2 cur.1).length <
      (finiteCurvePorts w N next.2 next.1).length := by
  have hgrowth := unmatched_pivot_strict_curve_growth cur.2 C (by
    simpa [hentry] using houtside)
  have hlink : w.link (3 * C) = some next.1 := by
    have hp := (step_some_parts hstep).1
    simpa [hexit] using hp
  have hrootStem :
      CurveReach w next.2 cur.1 (3 * C) := by
    simpa [hentry, hflip] using hgrowth.2.1
  have hrootNext : CurveReach w next.2 cur.1 next.1 :=
    CurveReach.step hrootStem (Or.inl hlink)
  have hnextRoot : CurveReach w next.2 next.1 cur.1 :=
    curveReach_symm hrootNext
  have hlift : ∀ p, CurveReach w cur.2 cur.1 p →
      CurveReach w next.2 next.1 p := by
    intro p hp
    have hp' : CurveReach w next.2 cur.1 p := by
      simpa [hentry, hflip] using hgrowth.1 p (by
        simpa [hentry] using hp)
    exact curveReach_trans hnextRoot hp'
  have hstemNew : CurveReach w next.2 next.1 (3 * C) :=
    curveReach_trans hnextRoot hrootStem
  have hsubset : ∀ p,
      p ∈ finiteCurvePorts w N cur.2 cur.1 →
      p ∈ finiteCurvePorts w N next.2 next.1 := by
    intro p hp
    rw [mem_finiteCurvePorts_iff] at hp ⊢
    exact ⟨hp.1, hlift p hp.2⟩
  have hstemMem : 3 * C ∈ finiteCurvePorts w N next.2 next.1 := by
    rw [mem_finiteCurvePorts_iff]
    exact ⟨by omega, hstemNew⟩
  have hstemNot : 3 * C ∉ finiteCurvePorts w N cur.2 cur.1 := by
    intro hm
    exact houtside (mem_finiteCurvePorts_iff.mp hm).2
  exact length_lt_of_strict_subset_curve
    (finiteCurvePorts_nodup w N cur.2 cur.1)
    hsubset (3 * C) hstemMem hstemNot

/-- A newly selected internal edge at `C` never escapes the old selected
curve when the pivot is a self-join.  Away from `C` the internal edge is
unchanged; at `C` both of its endpoints were already on the old curve. -/
theorem flipped_internal_edge_stays_in_self_curve
    {w : Wiring} {u : Tongues} {C p q : Nat}
    (hself : CurveReach w u (unmatchedBranch u C) (3 * C))
    (hp : CurveReach w u (unmatchedBranch u C) p)
    (hedge : InternalCurveEdge (flipAt u C) p q) :
    CurveReach w u (unmatchedBranch u C) q := by
  by_cases hpC : p / 3 = C
  · unfold InternalCurveEdge at hedge
    have hends := arrive_stem_endpoint (flipAt u C) p
    rw [hedge] at hends
    rcases hends with hpStem | hqStem
    · have hpEq : p = 3 * C := by omega
      subst p
      have hpivot := arrive_pivot_back u C
      rw [hpivot] at hedge
      injection hedge with hq
      subst q
      exact CurveReach.refl
    · have hqEq : q = 3 * C := by omega
      simpa [hqEq] using hself
  · have hold : InternalCurveEdge u p q := by
      have hback := internalCurveEdge_flip_other
        (u := flipAt u C) (C := C) hedge hpC
      simpa [flipAt_flipAt] using hback
    exact CurveReach.step hp (Or.inr hold)

/-- Pointwise shrinking at a self-pivot: every port on the next selected
train curve was already on the previous selected train curve. -/
theorem self_endpoint_pivot_curveReach_subset
    {w : Wiring} {C : Nat} {cur next : Nat × Tongues}
    (hstep : step w cur = some next)
    (hentry : cur.1 = unmatchedBranch cur.2 C)
    (hexit : exitPort cur = 3 * C)
    (hflip : next.2 = flipAt cur.2 C)
    (hself : CurveReach w cur.2 cur.1 (3 * C)) :
    ∀ p, CurveReach w next.2 next.1 p →
      CurveReach w cur.2 cur.1 p := by
  have hparts := step_some_parts hstep
  have hlink : w.link (3 * C) = some next.1 := by
    simpa [hexit] using hparts.1
  have hrootNextOld : CurveReach w cur.2 cur.1 next.1 :=
    CurveReach.step hself (Or.inl hlink)
  have hself' :
      CurveReach w cur.2 (unmatchedBranch cur.2 C) (3 * C) := by
    simpa [hentry] using hself
  intro p hreach
  induction hreach with
  | refl => exact hrootNextOld
  | @step x y hprefix hedge ih =>
      rcases hedge with htrack | hinternal
      · exact CurveReach.step ih (Or.inl htrack)
      · have hy :
            CurveReach w cur.2 (unmatchedBranch cur.2 C) y := by
          apply flipped_internal_edge_stays_in_self_curve hself'
          · simpa [hentry] using ih
          · simpa [hflip] using hinternal
        simpa [hentry] using hy

/-- At a self-pivot the next train curve is contained in the old one.  This
is the shrinking half dual to `unmatched_pivot_strict_curve_growth`. -/
theorem self_endpoint_pivot_finiteCurvePorts_nonincrease
    {w : Wiring} {N C : Nat} {cur next : Nat × Tongues}
    (hstep : step w cur = some next)
    (hentry : cur.1 = unmatchedBranch cur.2 C)
    (hexit : exitPort cur = 3 * C)
    (hflip : next.2 = flipAt cur.2 C)
    (hself : CurveReach w cur.2 cur.1 (3 * C)) :
    (finiteCurvePorts w N next.2 next.1).length ≤
      (finiteCurvePorts w N cur.2 cur.1).length := by
  have hlift : ∀ p, CurveReach w next.2 next.1 p →
      CurveReach w cur.2 cur.1 p :=
    self_endpoint_pivot_curveReach_subset
      hstep hentry hexit hflip hself
  have hsubset : ∀ p,
      p ∈ finiteCurvePorts w N next.2 next.1 →
      p ∈ finiteCurvePorts w N cur.2 cur.1 := by
    intro p hp
    rw [mem_finiteCurvePorts_iff] at hp ⊢
    exact ⟨hp.1, hlift p hp.2⟩
  exact nodup_subset_length_curve
    (finiteCurvePorts_nodup w N next.2 next.1) hsubset

/-- The selected train curve at a raw time, represented by its in-range
ports.  The default configuration matters only after a fall-off; all growth
theorems below assume the relevant productive step is live. -/
noncomputable def rawFiniteCurveSizeAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Nat :=
  let cur := (stepN w k start).getD start
  (finiteCurvePorts w N cur.2 cur.1).length

/-- The raw productive pivot at time `k` is a self-pivot when its unmatched
entry endpoint already lies on the selected curve containing its stem. -/
def RawCurveSelfAt
    (w : Wiring) (start : Nat × Tongues) (k : Nat) : Prop :=
  let cur := (stepN w k start).getD start
  CurveReach w cur.2 cur.1 (3 * (cur.1 / 3))

/-- Endpoint-writer switches on the selected train curve at raw time `k`. -/
noncomputable def rawFiniteCurveEndpointWritersAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : List Nat :=
  let cur := (stepN w k start).getD start
  finiteCurveEndpointWriters w N cur.2 cur.1

theorem rawFiniteCurveEndpointWritersAt_length_le_two
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    (rawFiniteCurveEndpointWritersAt w N start k).length ≤ 2 := by
  unfold rawFiniteCurveEndpointWritersAt
  exact finiteCurveEndpointWriters_length_le_two w N
    ((stepN w k start).getD start).2
    ((stepN w k start).getD start).1

/-- The writer of every productive step is an unmatched endpoint of the
selected train curve immediately before that step. -/
theorem rawProductiveAt_writer_mem_endpointWritersAt
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    rawWriterAt w start k ∈
      rawFiniteCurveEndpointWritersAt w N start k := by
  obtain ⟨cur, _next, C, hCwriter, hcur, _hnext, _hstep,
      hentry, _hexit, _hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  rw [← hCwriter]
  unfold rawFiniteCurveEndpointWritersAt
  simp only [hcur, Option.getD_some]
  rw [mem_finiteCurveEndpointWriters_iff]
  refine ⟨?_, ?_⟩
  · rw [hCwriter]
    exact rawProductiveAt_writer_lt hN hprod
  · rw [hentry]
    exact CurveReach.refl

/-- A productive self-pivot cannot introduce a new endpoint-writer switch
into the selected train component. -/
theorem rawProductiveAt_self_endpointWriters_subset
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hself : RawCurveSelfAt w start k) :
    ∀ D, D ∈ rawFiniteCurveEndpointWritersAt w N start (k+1) →
      D ∈ rawFiniteCurveEndpointWritersAt w N start k := by
  obtain ⟨cur, next, C, hCwriter, hcur, hnext, hstep,
      hentry, hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hCcur : C = cur.1 / 3 := by
    simpa [rawWriterAt, rawEntryAt, hcur] using hCwriter
  have hself' : CurveReach w cur.2 cur.1 (3 * C) := by
    unfold RawCurveSelfAt at hself
    simpa [hcur, hCcur] using hself
  have hlift := self_endpoint_pivot_curveReach_subset
    hstep hentry hexit hflip hself'
  intro D hD
  unfold rawFiniteCurveEndpointWritersAt at hD ⊢
  simp only [hcur, hnext, Option.getD_some] at hD ⊢
  rw [mem_finiteCurveEndpointWriters_iff] at hD ⊢
  refine ⟨hD.1, ?_⟩
  by_cases hDC : D = C
  · subst D
    rw [hentry]
    exact CurveReach.refl
  · have hold := hlift (unmatchedBranch next.2 D) hD.2
    have hbranch : unmatchedBranch next.2 D =
        unmatchedBranch cur.2 D := by
      rw [hflip]
      simp [unmatchedBranch, flipAt, hDC]
    rw [hbranch] at hold
    exact hold

/-- A live nonproductive step merely reroots the same selected component, so
it cannot introduce a new endpoint writer either. -/
theorem rawNonproductiveAt_endpointWriters_subset
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome)
    (hnot : ¬ RawProductiveAt w N start k) :
    ∀ D, D ∈ rawFiniteCurveEndpointWritersAt w N start (k+1) →
      D ∈ rawFiniteCurveEndpointWritersAt w N start k := by
  obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
    live_successor_configs hlive
  have hparts := step_some_parts hstep
  have hstate : next.2 = cur.2 := by
    have hwriterLt : cur.1 / 3 < N := by
      have hexitLt := (hN _ _ hparts.1).1
      rw [← arrive_exit_switch cur.2 cur.1]
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
      simpa [exitPort, Nat.mul_comm] using hexitLt
    have hwriter : next.2 (cur.1 / 3) = cur.2 (cur.1 / 3) := by
      by_cases heq : next.2 (cur.1 / 3) = cur.2 (cur.1 / 3)
      · exact heq
      · exact (hnot (raw_tongue_change_is_productive_writer
          hwriterLt hcur hnext hstep heq).1).elim
    funext j
    by_cases hj : j = cur.1 / 3
    · simpa [hj] using hwriter
    · have harrived : next.2 = (arrive cur.2 cur.1).2 := by
        simpa [arrivedTongues] using hparts.2
      rw [harrived]
      exact arrive_preserves_other rfl hj
  have hinternal : InternalCurveEdge cur.2 cur.1 (exitPort cur) := by
    unfold InternalCurveEdge
    apply Prod.ext
    · rfl
    · change arrivedTongues cur = cur.2
      rw [← hparts.2, hstate]
  have hcurNext : CurveReach w cur.2 cur.1 next.1 :=
    CurveReach.step
      (curveReach_edge (Or.inr hinternal))
      (Or.inl hparts.1)
  intro D hD
  unfold rawFiniteCurveEndpointWritersAt at hD ⊢
  simp only [hcur, hnext, Option.getD_some] at hD ⊢
  rw [mem_finiteCurveEndpointWriters_iff] at hD ⊢
  refine ⟨hD.1, ?_⟩
  have hreach := hD.2
  rw [hstate] at hreach
  exact curveReach_trans hcurNext hreach

/-- One step of a self-only epoch makes the endpoint-writer carrier
monotone decreasing. -/
theorem rawSelfOnlyStep_endpointWriters_subset
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome)
    (hself : RawProductiveAt w N start k → RawCurveSelfAt w start k) :
    ∀ D, D ∈ rawFiniteCurveEndpointWritersAt w N start (k+1) →
      D ∈ rawFiniteCurveEndpointWritersAt w N start k := by
  by_cases hprod : RawProductiveAt w N start k
  · exact rawProductiveAt_self_endpointWriters_subset
      hN hprod (hself hprod)
  · exact rawNonproductiveAt_endpointWriters_subset hN hlive hprod

/-- Throughout a self-only epoch, every current endpoint writer already
belonged to the initial selected component. -/
theorem rawSelfOnlyEpoch_endpointWriters_subset
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hself : ∀ k, k < K → RawProductiveAt w N start k →
      RawCurveSelfAt w start k) :
    ∀ j, j ≤ K → ∀ D,
      D ∈ rawFiniteCurveEndpointWritersAt w N start j →
      D ∈ rawFiniteCurveEndpointWritersAt w N start 0 := by
  intro j hj
  induction j with
  | zero =>
      intro D hD
      exact hD
  | succ j ih =>
      intro D hD
      have hstep := rawSelfOnlyStep_endpointWriters_subset hN
        (hlive (j+1) (by omega))
        (fun hprod => hself j (by omega) hprod)
      exact ih (by omega) D (hstep D hD)

/-- Every productive writer in a self-only epoch is one of the at-most-two
endpoint writers present at the epoch's initial configuration. -/
theorem rawSelfOnlyEpoch_productive_writer_mem_initial
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hself : ∀ k, k < K → RawProductiveAt w N start k →
      RawCurveSelfAt w start k)
    {k : Nat} (hk : k < K) (hprod : RawProductiveAt w N start k) :
    rawWriterAt w start k ∈
      rawFiniteCurveEndpointWritersAt w N start 0 := by
  have hmem := rawProductiveAt_writer_mem_endpointWritersAt hN hprod
  exact rawSelfOnlyEpoch_endpointWriters_subset
    hN start K hlive hself k (by omega)
    (rawWriterAt w start k) hmem

theorem rawSelfOnlyEpoch_tongue_stable_outside
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hself : ∀ k, k < K → RawProductiveAt w N start k →
      RawCurveSelfAt w start k)
    {C : Nat} (hC : C < N)
    (houtside : C ∉ rawFiniteCurveEndpointWritersAt w N start 0) :
    ∀ j, j ≤ K → (tonguesAt w start j) C = start.2 C := by
  intro j hj
  apply raw_tongue_stable_before_writer hC start j
  intro i hi hprod hwriter
  have hmem := rawProductiveAt_writer_mem_endpointWritersAt hN hprod
  have hmem0 := rawSelfOnlyEpoch_endpointWriters_subset
    hN start K hlive hself i (by omega)
    (rawWriterAt w start i) hmem
  rw [hwriter] at hmem0
  exact houtside hmem0

private def endpointProjection (endpoints : List Nat) (u : Tongues) :
    List Bool := endpoints.map u

private theorem endpointProjection_apply_of_mem
    {endpoints : List Nat} {u v : Tongues} {C : Nat}
    (hmap : endpointProjection endpoints u = endpointProjection endpoints v)
    (hC : C ∈ endpoints) : u C = v C := by
  unfold endpointProjection at hmap
  induction endpoints with
  | nil => cases hC
  | cons D rest ih =>
      simp only [List.map_cons] at hmap
      injection hmap with hhead htail
      rcases List.mem_cons.mp hC with hDC | hCrest
      · simpa [hDC] using hhead
      · exact ih htail hCrest

private theorem restrict_eq_of_endpointProjection_eq
    {N : Nat} {endpoints : List Nat} {base u v : Tongues}
    (hu : ∀ C, C < N → C ∉ endpoints → u C = base C)
    (hv : ∀ C, C < N → C ∉ endpoints → v C = base C)
    (hprojection : endpointProjection endpoints u =
      endpointProjection endpoints v) :
    VectorCount.restrict N u = VectorCount.restrict N v := by
  unfold VectorCount.restrict
  apply List.map_congr_left
  intro C hCmem
  have hC : C < N := List.mem_range.mp hCmem
  by_cases hendpoint : C ∈ endpoints
  · exact endpointProjection_apply_of_mem hprojection hendpoint
  · rw [hu C hC hendpoint, hv C hC hendpoint]

private theorem nodup_projection_of_full_nodup
    {α : Type} [BEq α] [LawfulBEq α]
    {full projection : Nat → α} :
    ∀ {ks : List Nat},
      (∀ i, i ∈ ks → ∀ j, j ∈ ks →
        projection i = projection j → full i = full j) →
      (ks.map full).Nodup → (ks.map projection).Nodup := by
  intro ks
  induction ks with
  | nil => intro _ _; simp
  | cons k rest ih =>
      intro hfibre hnd
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      constructor
      · intro hm
        obtain ⟨j, hj, hprojection⟩ := List.mem_map.mp hm
        have hfull := hfibre k List.mem_cons_self j
          (List.mem_cons_of_mem _ hj) hprojection.symm
        exact hnd.1 (List.mem_map.mpr ⟨j, hj, hfull.symm⟩)
      · exact ih
          (fun i hi j hj => hfibre i (List.mem_cons_of_mem _ hi)
            j (List.mem_cons_of_mem _ hj)) hnd.2

/-- **Four-snapshot bound for a self-only epoch.** At most two endpoint
writers can change, all other represented tongues are frozen, so any
duplicate-free sample of visible tongue vectors has length at most four. -/
theorem rawSelfOnlyEpoch_distinct_snapshots_le_four
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hself : ∀ k, k < K → RawProductiveAt w N start k →
      RawCurveSelfAt w start k)
    (ks : List Nat) (hks : ∀ k, k ∈ ks → k ≤ K)
    (hnd : (ks.map (restrictedTonguesAt w N start)).Nodup) :
    ks.length ≤ 4 := by
  let endpoints := rawFiniteCurveEndpointWritersAt w N start 0
  let projected := fun k => endpointProjection endpoints (tonguesAt w start k)
  have hprojectedNodup : (ks.map projected).Nodup := by
    apply nodup_projection_of_full_nodup
      (full := restrictedTonguesAt w N start)
    · intro i hi j hj hprojection
      have hiK := hks i hi
      have hjK := hks j hj
      unfold restrictedTonguesAt
      apply restrict_eq_of_endpointProjection_eq
        (base := start.2) (endpoints := endpoints)
      · intro C hC hout
        exact rawSelfOnlyEpoch_tongue_stable_outside
          hN start K hlive hself hC hout i hiK
      · intro C hC hout
        exact rawSelfOnlyEpoch_tongue_stable_outside
          hN start K hlive hself hC hout j hjK
      · exact hprojection
    · exact hnd
  have hlen : ∀ x ∈ ks.map projected, x.length = endpoints.length := by
    intro x hx
    obtain ⟨k, _hk, rfl⟩ := List.mem_map.mp hx
    simp [projected, endpointProjection]
  have hcount := VectorCount.pigeonhole endpoints.length
    (ks.map projected) hlen hprojectedNodup
  have hcap : endpoints.length ≤ 2 := by
    exact rawFiniteCurveEndpointWritersAt_length_le_two w N start 0
  have hpow : 2 ^ endpoints.length ≤ 4 := by
    have hcases : endpoints.length = 0 ∨
        endpoints.length = 1 ∨ endpoints.length = 2 := by omega
    rcases hcases with h | h | h <;> simp [h]
  simp only [List.length_map] at hcount
  omega

/-- Raw `stepN` form of strict train-curve growth. -/
theorem rawProductiveAt_nonself_curve_growth
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hnonself : ¬ RawCurveSelfAt w start k) :
    rawFiniteCurveSizeAt w N start k <
      rawFiniteCurveSizeAt w N start (k+1) := by
  obtain ⟨cur, next, C, hCwriter, hcur, hnext, hstep,
      hentry, hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hwriterLt := rawProductiveAt_writer_lt hN hprod
  have hC : C < N := by
    rw [hCwriter]
    exact hwriterLt
  have hCcur : C = cur.1 / 3 := by
    simpa [rawWriterAt, rawEntryAt, hcur] using hCwriter
  have houtside : ¬ CurveReach w cur.2 cur.1 (3 * C) := by
    unfold RawCurveSelfAt at hnonself
    simpa [hcur, hCcur] using hnonself
  have hgrowth := nonself_endpoint_pivot_finiteCurvePorts_growth
    hC hstep hentry hexit hflip houtside
  simpa [rawFiniteCurveSizeAt, hcur, hnext] using hgrowth

/-- Raw `stepN` form of the shrinking half: a productive self-pivot cannot
increase the finite train curve. -/
theorem rawProductiveAt_self_curve_nonincrease
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hself : RawCurveSelfAt w start k) :
    rawFiniteCurveSizeAt w N start (k+1) ≤
      rawFiniteCurveSizeAt w N start k := by
  obtain ⟨cur, next, C, hCwriter, hcur, hnext, hstep,
      hentry, hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hCcur : C = cur.1 / 3 := by
    simpa [rawWriterAt, rawEntryAt, hcur] using hCwriter
  have hself' : CurveReach w cur.2 cur.1 (3 * C) := by
    unfold RawCurveSelfAt at hself
    simpa [hcur, hCcur] using hself
  have hshrink := self_endpoint_pivot_finiteCurvePorts_nonincrease
    (N := N) hstep hentry hexit hflip hself'
  simpa [rawFiniteCurveSizeAt, hcur, hnext] using hshrink

/-- A live raw step which is not productive leaves the complete tongue
vector unchanged.  Boundedness is used only to know that the current writer
is one of the represented `N` switches. -/
theorem rawNonproductiveAt_tongues_eq
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start cur next : Nat × Tongues} {k : Nat}
    (hcur : stepN w k start = some cur)
    (hnext : stepN w (k+1) start = some next)
    (hstep : step w cur = some next)
    (hnot : ¬ RawProductiveAt w N start k) :
    next.2 = cur.2 := by
  have hparts := step_some_parts hstep
  have hwriterLt : cur.1 / 3 < N := by
    have hexitLt := (hN _ _ hparts.1).1
    rw [← arrive_exit_switch cur.2 cur.1]
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    simpa [exitPort, Nat.mul_comm] using hexitLt
  have hwriter : next.2 (cur.1 / 3) = cur.2 (cur.1 / 3) := by
    by_cases heq : next.2 (cur.1 / 3) = cur.2 (cur.1 / 3)
    · exact heq
    · exact (hnot (raw_tongue_change_is_productive_writer
        hwriterLt hcur hnext hstep heq).1).elim
  funext j
  by_cases hj : j = cur.1 / 3
  · simpa [hj] using hwriter
  · have harrived : next.2 = (arrive cur.2 cur.1).2 := by
      simpa [arrivedTongues] using hparts.2
    rw [harrived]
    exact arrive_preserves_other rfl hj

/-- A live nonproductive step only moves the root along its present selected
curve.  Consequently the represented finite curve, and hence its size, is
unchanged. -/
theorem rawNonproductiveAt_curve_size_eq
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome)
    (hnot : ¬ RawProductiveAt w N start k) :
    rawFiniteCurveSizeAt w N start (k+1) =
      rawFiniteCurveSizeAt w N start k := by
  obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
    live_successor_configs hlive
  have hstate := rawNonproductiveAt_tongues_eq
    hN hcur hnext hstep hnot
  have hparts := step_some_parts hstep
  have hinternal : InternalCurveEdge cur.2 cur.1 (exitPort cur) := by
    unfold InternalCurveEdge
    apply Prod.ext
    · rfl
    · change arrivedTongues cur = cur.2
      rw [← hparts.2, hstate]
  have hcurNext : CurveReach w cur.2 cur.1 next.1 :=
    CurveReach.step
      (curveReach_edge (Or.inr hinternal))
      (Or.inl hparts.1)
  have hnextCur : CurveReach w cur.2 next.1 cur.1 :=
    curveReach_symm hcurNext
  have hforward : ∀ p,
      p ∈ finiteCurvePorts w N cur.2 cur.1 →
      p ∈ finiteCurvePorts w N next.2 next.1 := by
    intro p hp
    rw [mem_finiteCurvePorts_iff] at hp ⊢
    rw [hstate]
    exact ⟨hp.1, curveReach_trans hnextCur hp.2⟩
  have hbackward : ∀ p,
      p ∈ finiteCurvePorts w N next.2 next.1 →
      p ∈ finiteCurvePorts w N cur.2 cur.1 := by
    intro p hp
    rw [mem_finiteCurvePorts_iff] at hp ⊢
    rw [hstate] at hp
    exact ⟨hp.1, curveReach_trans hcurNext hp.2⟩
  have hleForward := nodup_subset_length_curve
    (finiteCurvePorts_nodup w N cur.2 cur.1) hforward
  have hleBackward := nodup_subset_length_curve
    (finiteCurvePorts_nodup w N next.2 next.1) hbackward
  have hlength : (finiteCurvePorts w N cur.2 cur.1).length =
      (finiteCurvePorts w N next.2 next.1).length := by omega
  unfold rawFiniteCurveSizeAt
  simp only [hcur, hnext, Option.getD_some]
  exact hlength.symm

/-- Productive event times in a finite raw prefix. -/
noncomputable def rawProductiveCurveTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (List.range K).filter
    (fun k => decide (RawProductiveAt w N start k))
end GeneralN
