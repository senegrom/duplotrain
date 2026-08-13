/-!
# The small-`N` legs of the sharp state law

Model (audited against physical track): `n` switches, each with three
ports encoded as `3*k + a` where the arm `a` is `0` (stem), `1` (left
branch), `2` (right branch).  A *wiring* pairs ports with edges (paths of
plain track -- length and shape are irrelevant to the dynamics) or caps
them (dead ends).  Tongues are a bitmask: bit `k` false = Left, true =
Right.  A facing entry (stem) exits by the tongue's branch and leaves the
tongue alone; a trailing entry (branch) forces the tongue to that branch
and exits the stem.  Caps end the run: the train falls off.

The sharp state law `f(N) = min(2^N, N + 4)` is proved symbolically for
the `N + 4` regime (`state_law_N_add_four`, `state_law_lower_bound`);
at `N ≤ 2` the binding value is `2^N`, below the family's reach.  This
file supplies exactly those two legs by exhaustive evaluation
(`native_decide`) over every wiring and every start -- including starts
that first enter a port (a train standing on a stub):

* `states_one`: `f(1) = 2`;
* `states_two`: `f(2) = 4` (the dogbone Gray square).

The enumerator's completeness (every abstract wiring appears in
`allWirings n`) is by construction of the pairing recursion.
-/

namespace Duplotrain

/-- All matchings-with-caps of the port list: each head port is either capped
or paired with a later port.  Fuel avoids a termination proof; `length + 1`
always suffices. -/
def pairings : Nat → List Nat → List (List (Nat × Nat) × List Nat)
  | _, [] => [([], [])]
  | 0, _ => []
  | fuel + 1, p :: rest =>
    ((pairings fuel rest).map fun ec => (ec.1, p :: ec.2)) ++
    (List.range rest.length).flatMap fun i =>
      match rest[i]? with
      | none => []
      | some q =>
        (pairings fuel (rest.eraseIdx i)).map fun ec => ((p, q) :: ec.1, ec.2)

def allWirings (n : Nat) : List (List (Nat × Nat) × List Nat) :=
  pairings (3 * n + 1) (List.range (3 * n))

/-- Switch-level connectivity: `n` rounds of closure from switch 0. -/
def connected (n : Nat) (edges : List (Nat × Nat)) : Bool :=
  let step : List Nat → List Nat := fun seen =>
    edges.foldl
      (fun s e =>
        let k1 := e.1 / 3
        let k2 := e.2 / 3
        if s.contains k1 && !s.contains k2 then k2 :: s
        else if s.contains k2 && !s.contains k1 then k1 :: s
        else s)
      seen
  let final := (List.range n).foldl (fun s _ => step s) [0]
  (List.range n).all final.contains

def setBit (t k : Nat) (v : Bool) : Nat :=
  if v then t ||| (1 <<< k)
  else if t.testBit k then t - (1 <<< k) else t

/-- Arrive INTO port `p` with tongues `t`: returns (exit port, tongues',
route bit index) where routes are numbered `4*k + 2*(branch-1) + dir`
(dir 0 = stem→branch, 1 = branch→stem). -/
def arrive (t p : Nat) : Nat × Nat × Nat :=
  let k := p / 3
  match p % 3 with
  | 0 =>
    let b := if t.testBit k then 2 else 1
    (3 * k + b, t, 4 * k + 2 * (b - 1))
  | a => (3 * k, setBit t k (a == 2), 4 * k + 2 * (a - 1) + 1)

def lookupEdge : List (Nat × Nat) → Nat → Nat → Option (Nat × Bool)
  | [], _, _ => none
  | e :: rest, p, i =>
    if e.1 == p then some (i, false)
    else if e.2 == p then some (i, true)
    else lookupEdge rest p (i + 1)

def lookupCap : List Nat → Nat → Nat → Option Nat
  | [], _, _ => none
  | c :: rest, p, i => if c == p then some i else lookupCap rest p (i + 1)

/-- One fall-mode step; `none` when the train leaves the layout. -/
def stepFall (edges : List (Nat × Nat)) (i : Nat) (d : Bool) (t : Nat) :
    Option (Nat × Bool × Nat) :=
  match edges[i]? with
  | none => none
  | some edge =>
    let dest := if d then edge.1 else edge.2
    let (exitP, t', _r) := arrive t dest
    match lookupEdge edges exitP 0 with
    | some (j, endB) => some (j, endB, t')
    | none => none

/-- Distinct tongue vectors along the run from `s`, given vectors already
seen. -/
def vectorsFrom (edges : List (Nat × Nat)) (n : Nat)
    (s : Nat × Bool × Nat) (seen : List Nat) : Nat :=
  let code : Nat × Bool × Nat → Nat := fun st =>
    ((2 * st.1 + (if st.2.1 then 1 else 0)) <<< n) + st.2.2
  let rec go : Nat → Nat × Bool × Nat → List Nat → List Nat → Nat
    | 0, _, _, vecs => vecs.length
    | fuel + 1, st, states, vecs =>
      let c := code st
      if states.contains c then vecs.length
      else
        let vecs := if vecs.contains st.2.2 then vecs else st.2.2 :: vecs
        match stepFall edges st.1 st.2.1 st.2.2 with
        | none => vecs.length
        | some st' => go fuel st' (c :: states) vecs
  go (2 * edges.length * (1 <<< n) + 4) s [] seen

/-- Max distinct tongue vectors over every start: every edge/direction, every
initial tongue vector, plus the port-entry starts (train on a stub). -/
def maxStates (n : Nat) (w : List (Nat × Nat) × List Nat) : Nat :=
  let edges := w.1
  let edgeBest := (List.range edges.length).foldl
    (fun best i =>
      [false, true].foldl
        (fun best d =>
          (List.range (1 <<< n)).foldl
            (fun best t => max best (vectorsFrom edges n (i, d, t) [t]))
            best)
        best)
    0
  -- port-entry starts: first event is arriving INTO a port
  let ports := (List.range (3 * n)).filter fun p =>
    (lookupEdge edges p 0).isSome || (lookupCap w.2 p 0).isSome
  ports.foldl
    (fun best p =>
      (List.range (1 <<< n)).foldl
        (fun best t =>
          let (exitP, t', _r) := arrive t p
          let seen := if t == t' then [t] else [t', t]
          match lookupEdge edges exitP 0 with
          | some (j, endB) =>
            max best (vectorsFrom edges n (j, endB, t') seen)
          | none => max best seen.length)
        best)
    edgeBest

def bestStates (n : Nat) : Nat :=
  (allWirings n).foldl
    (fun best w =>
      if connected n w.1 then max best (maxStates n w) else best)
    0

/-- `f(1) = 2` and `f(2) = 4 = 2^N`: the two legs of
`f(N) = min(2^N, N + 4)` below the symbolic family's reach. -/
theorem states_one : bestStates 1 = 2 := by native_decide
theorem states_two : bestStates 2 = 4 := by native_decide

end Duplotrain
