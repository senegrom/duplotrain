# duplotrain

Model LEGO® DUPLO® train track and find every layout that **loops nicely** — given the
pieces you actually own.

```
duplotrain solve --curve 12 --straight 4 -o out
```

![Every exact loop from one starter box](docs/starter-shapes.png)

That picture is the *complete* answer for a starter box (12 curves + 4 straights): up
to rotation, reflection and starting point, exactly four closed layouts exist, and the
solver proves it by exhaustion — in exact arithmetic, so "closed" means *closed*, not
"closed to within some epsilon".

## Why exact arithmetic

A DUPLO curve turns 30° with a 256 mm centreline radius, and one curve advances exactly
one straight length (128 mm) while kicking sideways by `256 − 128·√3` mm. That `√3`
means loop-closure positions are irrational: test them with floats and a tolerance and
you will eventually bless a layout that is millimetres open, or reject one that is
perfect. All geometry here lives in the field **ℚ(√2, √3)** (four exact rational
coefficients per coordinate), headings live on a 24-step lattice of 15°, and a loop is
closed if and only if the end pose *equals* the start pose.

Real DUPLO joints do have designed-in play (~1 mm each), and some classic builds rely
on it — the famous `R,R,L,L` lane-change is 4.59 mm short of its nominal length. Pass
`--slop 6` and the solver will admit such **forced fits** too, always reporting exactly
how many millimetres the joints must absorb. It never mislabels them as exact.

## The pieces

Geometry for the modern light-grey system (2018+, sets 10874 / 10875 / 10882), sourced
from measured surveys ([Cailliau](https://www.cailliau.org/en/Alphabetical/L/Lego/Duplo/Train/Rails/Dimensions/),
[duplo-schienen.de](http://www.duplo-schienen.de/lego-duplo-schienen-geometrische-regeln.html),
[onemetre.net](https://www.onemetre.net/OtherTopics/Duplo/Track%20dims/DuploTrack.htm))
and the LDraw part library:

| id               | part    | geometry                                            |
| ---------------- | ------- | --------------------------------------------------- |
| `straight`       | 6377    | 128 mm (8 studs) connection pitch                    |
| `curve`          | 6378    | 30°, R = 256 mm; 12 make a 576 mm circle             |
| `switch`         | 51943c01| left + right 30° branches off one stem; no straight route |
| `crossing`       | 6376    | two 192 mm runs crossing at 60° *(provisional)*      |
| `level_crossing` | 6391    | one straight under a 160 × 160 mm road plate         |
| `ramp`           | 6392    | 320 mm run rising 76.8 mm *(provisional)*            |
| `span`           | 6393    | 192 mm level run atop the ramps *(provisional)*      |

Connectors are genderless (a jigsaw tab **and** socket at every end), so any end mates
with any end and one physical curve serves as both the left and the right turn — the
model gets that for free by letting pieces be entered from either port.

Pieces marked *provisional* use a derived number nobody has published. Override any of
them — or add entirely new pieces — with a JSON catalogue, no code changes:

```json
{ "pieces": [ { "id": "ramp",
    "name": "Bridge ramp (measured)", "category": "bridge", "width": 64,
    "paths": [ { "segments": [ { "type": "ramp", "run": 320, "rise": 80 } ] } ],
    "port_names": ["low", "high"] } ] }
```

```
duplotrain solve --catalog my-measurements.json --curve 12 --ramp 2 --span 2 ...
```

Lengths may be plain numbers, exact fractions (`"384/5"`), field elements
(`{"alg": [a, b, c, d]}` = `a + b√2 + c√3 + d√6`), or arc chords
(`{"chord": {"radius": 256, "degrees": 30}}`).

## Install & use

Python ≥ 3.12. From a checkout:

```
pip install -e .[dev]        # click + rich + matplotlib + pytest
```

CLI:

```
duplotrain pieces                                     # the catalogue
duplotrain solve --curve 12 --straight 4 --switch 2 -o out
duplotrain solve --inventory mybox.json --slop 5 -o out
duplotrain check out/loop_01.json                     # closure report
duplotrain render out/loop_01.json -o picture.png
duplotrain demo                                       # the classic oval
```

`solve` prints a ranked table (exactness, box usage, compactness, squareness, variety,
dangling-branch penalty — weights overridable in `duplotrain.scoring`) and writes a
PNG + JSON per kept layout. Layout JSON stores frames as exact coefficients, so a
reloaded layout still passes the exact closure test.

Library:

```python
from duplotrain import default_catalog, solve, SolverConfig, render_layout

pieces = default_catalog()
result = solve({"curve": 12, "straight": 4, "switch": 1}, pieces,
               SolverConfig(max_results=50))
best = result.solutions[0]        # .layout, .exact, .gap, .open_stubs
render_layout(best.layout, "loop.png")
```

![Oval with a switch worked in](docs/oval-with-switch.png)

## How the solver works

Depth-first search that walks track outward from an anchored origin, over the
geometrically distinct traversals of each piece type (a straight contributes one move,
a curve two — its left and right readings). It prunes, conservatively: headings that the
remaining pieces cannot swing back to the anchor's, positions they cannot reach home
from, and placements that overlap existing track (respecting elevation, so a
sufficiently high bridge legitimately crosses over). Switches drop *open stubs* which
the walk may later re-enter exactly — figure-eights and re-joining branches emerge from
that rule alone. Found loops are deduplicated by a canonical signature invariant under
rotation, reversal and mirroring.

Elevation is modelled (ramps carry `z`; closure requires returning to ground), and the
collision clearance defaults to more than the 10872 bridge deck height because a DUPLO
locomotive genuinely does not fit under that bridge.

**Current limits worth knowing:**

- The solver finds *driving loops* — one closed train circuit. A passing loop (both
  switch branch-pairs connected) is not a single circuit and needs the planned
  multi-cycle search; today the second track shows up as two dangling stubs.
- The X-crossing's run length is inferred (192 mm fits its catalogued bounding box);
  with it, no figure-eight closes within 6 mm using 12–16 curves — measure the real
  part before concluding anything about your floor.
- Collision checking is sampled discs along centrelines: exact-touch parallel tracks
  are legal, sub-2 mm grazes may slip through.

## Tests

```
python -m pytest
```

48 tests cover the number field, the pose lattice, piece derivation, the documented
geometric identities (the `L,R,R,L` snake equals four straights exactly; `R,R,L,L`
misses by exactly `448 − 256√3` ≈ 4.59 mm), serialisation round-trips, and solver
ground truths (12 curves make exactly one circle; the starter box makes exactly four
shapes; 11 curves make nothing).

---

*Not affiliated with the LEGO Group. LEGO and DUPLO are trademarks of the LEGO Group.*
