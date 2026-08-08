import OutwardReplayCore

/-!
# Simple support paths manufacture outward replay certificates

`OutwardReplayCore` uses an inductive non-backtracking path.  This file exposes
an ordinary finite-list interface.  A list of occupied, correctly oriented
jump edges whose vertex list is duplicate-free can be folded into an
`OutwardPath`; the duplicate-free condition supplies the no-backtracking fact
at every step.

The remaining graph-theoretic extraction problem is therefore reduced to the
standard statement that every vertex in a finite connected component admits a
simple path from one endpoint of the component's full edge.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Consecutive oriented slots form a path from cell `c`. -/
def Follows : Nat → List Nat → Prop
  | _, [] => True
  | c, s :: ss =>
      m.cellOf s = c ∧ Follows (m.cellOf (m.bar s)) ss

/-- Endpoint of an oriented slot list. -/
def chainEnd : Nat → List Nat → Nat
  | c, [] => c
  | _, s :: ss => chainEnd (m.cellOf (m.bar s)) ss

/-- Vertex list of an oriented path. -/
def chainCells (c : Nat) (ss : List Nat) : List Nat :=
  c :: ss.map (fun s => m.cellOf (m.bar s))

theorem chainCells_cons (c s : Nat) (ss : List Nat) :
    chainCells m c (s :: ss) =
      c :: chainCells m (m.cellOf (m.bar s)) ss := by
  rfl

/-- Every slot in the path is occupied. -/
def OccupiedChain (k : Nat) (ss : List Nat) : Prop :=
  ∀ s ∈ ss, Occupied m e r0 k s

/-- Fold a simple oriented path onto an existing outward-path prefix.  The
extra first vertex is the parent of the current cell; keeping it in the Nodup
list rules out immediately returning along the parent edge. -/
theorem outwardPath_of_simple_chain
    {k f c p : Nat} :
    ∀ ss : List Nat,
      OutwardPath m e r0 k f c p →
      Follows m c ss →
      OccupiedChain m e r0 k ss →
      (m.cellOf (m.bar p) :: chainCells m c ss).Nodup →
      ∃ q, OutwardPath m e r0 k f (chainEnd m c ss) q := by
  intro ss
  induction ss generalizing c p with
  | nil =>
      intro hout _ _ _
      exact ⟨p, by simpa [chainEnd] using hout⟩
  | cons s rest ih =>
      intro hout hfollow hocc hnd
      simp only [Follows] at hfollow
      have hsocc : Occupied m e r0 k s :=
        hocc s List.mem_cons_self
      have hfar : m.cellOf (m.bar s) ≠ m.cellOf (m.bar p) := by
        intro heq
        rw [List.nodup_cons] at hnd
        apply hnd.1
        simp only [chainCells, List.map_cons, List.mem_cons]
        exact Or.inr (Or.inl heq.symm)
      have hstep : OutwardPath m e r0 k f
          (m.cellOf (m.bar s)) (m.bar s) :=
        OutwardPath.step hout hsocc hfollow.1 hfar
      have hoccRest : OccupiedChain m e r0 k rest := by
        intro t ht
        exact hocc t (List.mem_cons_of_mem _ ht)
      have hndRest :
          (m.cellOf (m.bar (m.bar s)) ::
            chainCells m (m.cellOf (m.bar s)) rest).Nodup := by
        rw [List.nodup_cons] at hnd
        simpa [chainCells, m.bar_invol, hfollow.1] using hnd.2
      have htail := ih hstep hfollow.2 hoccRest hndRest
      simpa [chainEnd] using htail

/-- Simple path from the first endpoint of a full edge.  The opposite full
endpoint is included as the initial parent vertex, so the path cannot cross the
full edge itself. -/
theorem rootedAt_of_simple_chain_left
    {k f : Nat} (ss : List Nat)
    (hfull : Full m e r0 k f)
    (hfollow : Follows m (m.cellOf f) ss)
    (hocc : OccupiedChain m e r0 k ss)
    (hnd : (m.cellOf (m.bar f) ::
      chainCells m (m.cellOf f) ss).Nodup) :
    RootedAt m e r0 k f (chainEnd m (m.cellOf f) ss) := by
  rcases outwardPath_of_simple_chain m e r0 ss
      (OutwardPath.left : OutwardPath m e r0 k f (m.cellOf f) f)
      hfollow hocc hnd with ⟨p, hp⟩
  exact (outwardPath_confirmed_rooted m e r0 hfull hp).2

/-- Symmetric path from the second endpoint of a full edge. -/
theorem rootedAt_of_simple_chain_right
    {k f : Nat} (ss : List Nat)
    (hfull : Full m e r0 k f)
    (hfollow : Follows m (m.cellOf (m.bar f)) ss)
    (hocc : OccupiedChain m e r0 k ss)
    (hnd : (m.cellOf f ::
      chainCells m (m.cellOf (m.bar f)) ss).Nodup) :
    RootedAt m e r0 k f
      (chainEnd m (m.cellOf (m.bar f)) ss) := by
  rcases outwardPath_of_simple_chain m e r0 ss
      (OutwardPath.right :
        OutwardPath m e r0 k f (m.cellOf (m.bar f)) (m.bar f))
      hfollow hocc hnd with ⟨p, hp⟩
  exact (outwardPath_confirmed_rooted m e r0 hfull hp).2

end Echo
