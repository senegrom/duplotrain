/-!
# The lazy-point switch theorems, machine-checked in Lean 4

Model (audited against physical track, see docs/switch_ceiling_proof.py):
`n` switches, each with three ports encoded as `3*k + a` where the arm
`a` is `0` (stem), `1` (left branch), `2` (right branch).  A *wiring* pairs
ports with edges (paths of plain track -- length and shape are irrelevant to
the dynamics) or caps them (dead ends / guarded buffer stubs).  Tongues are a
bitmask: bit `k` false = Left, true = Right.

Dynamics of the DUPLO lazy point: a *facing* entry (via the stem) exits by the
tongue's branch and leaves the tongue alone; a *trailing* entry (via a branch)
forces the tongue to that branch and exits the stem.

Two automata are formalised:
* the *perfection* automaton (caps reflect, as guarded buffers): a wiring is
  perfect iff from EVERY start edge/direction and EVERY initial tongue vector
  the eventually-periodic run sweeps every edge, cap and switch route in both
  directions;
* the *state-counting* automaton (caps end the run: the train falls off),
  measuring how many distinct tongue vectors a single run can visit, over all
  starts -- including starts that first enter a port (a train standing on a
  stub), which the audit of 2026-08-06 added.

Main results, all by exhaustive evaluation (`native_decide`):
* `no_perfect_three`: no connected 3-switch wiring is perfect (the switch
  ceiling -- with the lobe-contraction reduction this closes the perfect-loop
  classification);
* `unique_perfect_two`: the dogbone is the ONLY perfect connected 2-switch
  wiring, and `unique_perfect_one` its 1-switch analogue (teardrop + guarded
  stem);
* `states_one/two/three`: the maximal number of distinct tongue vectors is
  2, 4, 7 = min(2^N, N+4);
* `cycle_cap_two/three`: the eventual cycle never carries more than 4
  distinct tongue vectors (the dogbone Gray square is the strongest
  oscillator a lazy-point network can sustain).

The enumerator's completeness (every abstract wiring appears in
`allWirings n`) is by construction of the pairing recursion; the count
theorems `count_three`/`count_four` pin the enumeration sizes to the
independently computed values.
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

/-- One perfection-automaton step from riding edge `i` in direction `d`
(reflecting caps).  Returns `none` if the train gets stuck bouncing between
caps, else the next (edge, dir, tongues) plus the bitmask of sweep targets
touched: bits `2*i+d` for edges, `2*e + j` for caps, `2*e + c + r` for routes. -/
def stepReflect (edges : List (Nat × Nat)) (caps : List Nat) (nc : Nat)
    (i : Nat) (d : Bool) (t : Nat) : Option (Nat × Bool × Nat) × Nat :=
  let e := edges.length
  let mask0 := 1 <<< (2 * i + (if d then 1 else 0))
  match edges[i]? with
  | none => (none, mask0)
  | some edge =>
    let dest := if d then edge.1 else edge.2
    let rec resolve : Nat → Nat → Nat → Nat → Option (Nat × Bool × Nat) × Nat
      | 0, _, _, mask => (none, mask)
      | fuel + 1, port, tg, mask =>
        let (exitP, tg', route) := arrive tg port
        let mask := mask ||| (1 <<< (2 * e + nc + route))
        match lookupEdge edges exitP 0 with
        | some (j, endB) => (some (j, endB, tg'), mask)
        | none =>
          match lookupCap caps exitP 0 with
          | some cj => resolve fuel exitP tg' (mask ||| (1 <<< (2 * e + cj)))
          | none => (none, mask)
    resolve 6 dest t mask0

/-- Sweep-target count for the perfection automaton. -/
def fullMask (edges : List (Nat × Nat)) (caps : List Nat) (n : Nat) : Nat :=
  let e := edges.length
  let bits := 2 * e + caps.length + 4 * n
  (1 <<< bits) - 1

/-- Does the eventual cycle from this start sweep everything?  Trajectory is
at most `2*e*2^n` states; fuel covers it. -/
def runCovers (edges : List (Nat × Nat)) (caps : List Nat) (n : Nat)
    (start : Nat × Bool × Nat) : Bool :=
  let full := fullMask edges caps n
  let nc := caps.length
  let code : Nat × Bool × Nat → Nat := fun s =>
    ((2 * s.1 + (if s.2.1 then 1 else 0)) <<< n) + s.2.2
  let rec go : Nat → Nat × Bool × Nat → List (Nat × Nat) → Bool
    | 0, _, _ => false
    | fuel + 1, s, trail =>
      let c := code s
      if trail.any (fun p => p.1 == c) then
        let cycleMask := (trail.takeWhile (fun p => p.1 != c)).foldl
          (fun m p => m ||| p.2) 0
        -- trail is newest-first: takeWhile stops AT the revisited state, so
        -- the accumulated masks are exactly the cycle's steps... plus we must
        -- include the revisited state's own step mask, which is the head of
        -- the remaining list.
        let rest := trail.dropWhile (fun p => p.1 != c)
        let cycleMask := match rest with
          | p :: _ => cycleMask ||| p.2
          | [] => cycleMask
        cycleMask &&& full == full
      else
        match stepReflect edges caps nc s.1 s.2.1 s.2.2 with
        | (none, _m) => false
        | (some s', m) => go fuel s' ((c, m) :: trail)
  go (2 * edges.length * (1 <<< n) + 4) start []

def perfect (n : Nat) (w : List (Nat × Nat) × List Nat) : Bool :=
  let edges := w.1
  let caps := w.2
  edges.length != 0 &&
  (List.range edges.length).all fun i =>
    [false, true].all fun d =>
      (List.range (1 <<< n)).all fun t =>
        runCovers edges caps n (i, d, t)

/-- The switch ceiling at n = 3: no connected wiring is perfect. -/
theorem no_perfect_three :
    ((allWirings 3).all fun w =>
      !(connected 3 w.1 && perfect 3 w)) = true := by native_decide

/-- Exactly one perfect connected wiring at n = 2 (the dogbone) ... -/
theorem unique_perfect_two :
    ((allWirings 2).filter fun w =>
      connected 2 w.1 && perfect 2 w).length = 1 := by native_decide

/-- ... and it IS the dogbone: stems joined, both lobes closed. -/
theorem dogbone_perfect :
    perfect 2 ([(0, 3), (1, 2), (4, 5)], []) = true := by native_decide

/-- Exactly one perfect connected wiring at n = 1 (teardrop + guarded stem). -/
theorem unique_perfect_one :
    ((allWirings 1).filter fun w =>
      connected 1 w.1 && perfect 1 w).length = 1 := by native_decide

/-- Enumeration sizes match the independently computed counts. -/
theorem count_two : (allWirings 2).length = 76 := by native_decide
theorem count_three : (allWirings 3).length = 2620 := by native_decide

/-! ## State counting (caps end the run: the train falls off) -/

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

/-- f(1) = 2, f(2) = 4, f(3) = 7 = min(2^N, N+4). -/
theorem states_one : bestStates 1 = 2 := by native_decide
theorem states_two : bestStates 2 = 4 := by native_decide
theorem states_three : bestStates 3 = 7 := by native_decide

/-! ## The cycle cap: eventual cycles carry at most 4 tongue vectors -/

/-- Distinct tongue vectors ON the eventual cycle (0 if the train falls off). -/
def cycleVectors (edges : List (Nat × Nat)) (n : Nat)
    (s : Nat × Bool × Nat) : Nat :=
  let code : Nat × Bool × Nat → Nat := fun st =>
    ((2 * st.1 + (if st.2.1 then 1 else 0)) <<< n) + st.2.2
  let rec go : Nat → Nat × Bool × Nat → List (Nat × Nat) → Nat
    | 0, _, _ => 0
    | fuel + 1, st, trail =>
      let c := code st
      if trail.any (fun p => p.1 == c) then
        let cyc := (c, st.2.2) ::
          trail.takeWhile (fun p => p.1 != c)
        (cyc.foldl
          (fun (vs : List Nat) p =>
            if vs.contains p.2 then vs else p.2 :: vs)
          []).length
      else
        match stepFall edges st.1 st.2.1 st.2.2 with
        | none => 0
        | some st' => go fuel st' ((c, st.2.2) :: trail)
  go (2 * edges.length * (1 <<< n) + 4) s []

def bestCycle (n : Nat) : Nat :=
  (allWirings n).foldl
    (fun best w =>
      if !(connected n w.1) then best
      else
        (List.range w.1.length).foldl
          (fun best i =>
            [false, true].foldl
              (fun best d =>
                (List.range (1 <<< n)).foldl
                  (fun best t =>
                    max best (cycleVectors w.1 n (i, d, t)))
                  best)
              best)
          best)
    0

/-- The strongest oscillator a lazy-point network sustains is the dogbone's
Gray square: cycles never carry more than 4 distinct tongue vectors. -/
theorem cycle_cap_two : bestCycle 2 = 4 := by native_decide
theorem cycle_cap_three : bestCycle 3 = 4 := by native_decide

/-! ## The n = 4 exhaustions (140,152 wirings each) -/

theorem count_four : (allWirings 4).length = 140152 := by native_decide

theorem no_perfect_four :
    ((allWirings 4).all fun w =>
      !(connected 4 w.1 && perfect 4 w)) = true := by native_decide

theorem states_four : bestStates 4 = 8 := by native_decide

theorem cycle_cap_four : bestCycle 4 = 4 := by native_decide

end Duplotrain
