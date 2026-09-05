"""The built-in piece catalogue, and loading of user-supplied ones.

Numbers here come from measured sources (Cailliau's dimension survey, the LDraw part
library, duplo-schienen.de's geometry rules, BrickLink listings) and refer to the
modern light-grey track generation (2018+, sets 10874/10875/10882).  The load-bearing
facts:

* straight (6377): connection pitch exactly **128 mm** (8 DUPLO studs)
* curve (6378): **30 degrees**, 12 to a circle, centreline radius **256 mm = 2 x 128**
* switch (51943c01): a meld of a left and a right curve sharing one stem -- there is
  **no straight route** through a DUPLO switch
* the connectors are genderless, so every end mates with every end and one physical
  curve is both the left and the right curve

Because ``R = 2L`` exactly, one curve advances exactly one straight-length along the
entry heading while shifting sideways by ``256 - 128*sqrt(3)`` mm.  That irrational
offset is why the geometry runs on exact ``Q(sqrt2, sqrt3)`` arithmetic: layouts that
truly close (ovals, S-bends, 90-degree lattice layouts) then test closed with no
epsilon, and layouts that only *look* closed (the classic "Regel 3" builds, which are
4.59 mm short) are honestly reported as forced fits.

The crossing, switch and bridge plan geometry were settled by parsing the LDraw part
files and BlueBrick's measured connection library (cross-calibrated against each
other and against part weights and photographs).  The bridge's *vertical* split
(57.6 mm ramp + 19.2 mm arch to a 76.8 mm crest) is derived from brick-integer
constraints and part bounding heights rather than a published figure -- the most
likely number to move if someone puts callipers on the real part -- so the bridge
parts, the slight slope and the off-ramp stay flagged ``provisional``.
Override any piece by loading a user catalogue on top -- same JSON schema, matching ids
replace the built-ins.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .pieces import PieceType, parse_pieces

__all__ = ["DEFAULT_CATALOG_SPECS", "default_catalog", "load_catalog"]

#: One DUPLO stud pitch, mm.
STUD = 16

#: Straight-rail connection pitch, mm (8 studs).
STRAIGHT = 8 * STUD  # 128

#: Curve centreline radius, mm (exactly two straights -- the system's design identity).
RADIUS = 2 * STRAIGHT  # 256

#: Nominal track piece width, mm (4 studs).
WIDTH = 4 * STUD  # 64

# The default catalogue, in exactly the schema accepted for user catalogue files.
# A length may be a plain number or {"alg": [a, b, c, d]} = a + b*sqrt2 + c*sqrt3 + d*sqrt6.
DEFAULT_CATALOG_SPECS: list[dict[str, Any]] = [
    {
        "id": "straight",
        "name": "Straight rail",
        "category": "track",
        "part_numbers": ["6377", "6207494"],
        "width": WIDTH,
        "paths": [
            {"segments": [{"type": "straight", "run": STRAIGHT}]},
        ],
        "port_names": ["a", "b"],
        "notes": "Connection pitch 128 mm = 8 studs; body overhangs to 10 studs via the tab.",
    },
    {
        "id": "curve",
        "name": "Curved rail (30 deg)",
        "category": "track",
        "part_numbers": ["6378", "6207493"],
        "width": WIDTH,
        "paths": [
            {"segments": [{"type": "arc", "radius": RADIUS, "degrees": 30}]},
        ],
        "port_names": ["a", "b"],
        "notes": (
            "12 make a circle of 576 mm outer diameter. Genderless ends: entering from "
            "port b turns the other way, so this one piece is both the left and the "
            "right curve."
        ),
    },
    {
        "id": "switch",
        "name": "Switch / points",
        "category": "junction",
        "part_numbers": ["51943c01", "51560", "6207508"],
        "width": WIDTH,
        "paths": [
            {"segments": [{"type": "arc", "radius": RADIUS, "degrees": 30}]},
            {"segments": [{"type": "arc", "radius": RADIUS, "degrees": -30}]},
        ],
        "port_names": ["stem", "left", "right"],
        "notes": (
            "A meld of a left and a right curve sharing the stem; there is no straight "
            "route through a DUPLO switch, and the two exits sit 60 deg apart. LDraw "
            "51943.dat confirms each branch is EXACTLY a standard 30.000 deg / R=256 mm "
            "curve (branch ends at (128, +/-34.2975) mm, max file deviation 1.2 um). "
            "Gilbert's measured ~29.7 deg is real-part play, absorbed by --slop."
        ),
    },
    {
        "id": "crossing",
        "name": "Track crossing (60 deg X)",
        "category": "junction",
        "part_numbers": ["6376"],
        "width": WIDTH,
        "paths": [
            # Two straight 128 mm runs crossing at their common midpoint, 60 deg apart.
            {"segments": [{"type": "straight", "run": STRAIGHT}]},
            {
                "start": {"x": 32, "y": {"alg": [0, 0, -32, 0]}, "heading_deg": 60},
                "segments": [{"type": "straight", "run": STRAIGHT}],
            },
        ],
        "port_names": ["a", "b", "c", "d"],
        "notes": (
            "Out of production since ~2008. Each route is exactly one straight module "
            "(128 mm); geometry from BlueBrick's measured part library, calibrated "
            "against LDraw 6377/6378 and cross-checked by part weight and imagery. "
            "BrickLink's '12 x 14 studs' listing is wrong and was rejected."
        ),
    },
    {
        "id": "level_crossing",
        "name": "Level crossing plate",
        "category": "track",
        "part_numbers": ["6391", "6207496"],
        "width": 160,
        "end_overhang": 16.0,  # (160 mm plate - 128 mm pitch) / 2 per end
        "paths": [
            {"segments": [{"type": "straight", "run": STRAIGHT}]},
        ],
        "port_names": ["a", "b"],
        "notes": (
            "Rail run is one plain straight (128 mm); the road plate is 10 x 10 studs "
            "(160 x 160 mm), so each end overhangs the joint by 16 mm -- which is why "
            "two of these cannot sit directly adjacent, and the model forbids it."
        ),
    },
    {
        "id": "buffer",
        "name": "Buffer stop (rail end)",
        "category": "track",
        "part_numbers": ["35967", "6219464"],
        "width": WIDTH,
        "paths": [
            {"segments": [{"type": "straight", "run": 4 * STUD}]},
        ],
        "port_names": ["a", "end"],
        "sealed_ports": [1],
        "notes": (
            "Red track-end bumper from set 10882 ('RAIL STOP, 4 MODULE'), 64 mm long. "
            "Its far face is sealed: nothing can mate there and no loop can pass "
            "through, so it terminates sidings and shuttle runs."
        ),
    },
    {
        "id": "offramp",
        "name": "Off-ramp to the floor",
        "category": "track",
        "part_numbers": ["4785"],
        "width": WIDTH,
        "provisional": True,
        "paths": [
            {"segments": [{"type": "straight", "run": 6 * STUD}]},
        ],
        "port_names": ["a", "floor"],
        "sealed_ports": [1],
        "notes": (
            "'RAIL RAMP, 6 MODULE' from set 10425 (2024): a 96 mm wedge that lets the "
            "train drive off the rails onto the floor. Modelled like a buffer -- the "
            "floor side is sealed and a run ending there stops (the train has left "
            "the railway). Run length inferred from the 6-module name."
        ),
    },
    {
        "id": "slope",
        "name": "Slight slope rail",
        "category": "track",
        "part_numbers": ["35966", "6207491"],
        "width": WIDTH,
        "provisional": True,
        "paths": [
            {"segments": [{"type": "ramp", "run": 16 * STUD, "rise": "28/5"}]},
        ],
        "port_names": ["low", "high"],
        "notes": (
            "'Train Track, Slight Slope' from set 10875 (two per set). Run 256 mm = 16 "
            "modules (BrickOwl measures 28.1 cm incl. tab). The rise is derived: the "
            "part stands 26 mm tall vs the 20.4 mm rail profile, giving ~5.6 mm -- a "
            "play feature, not real elevation. Measure before trusting the rise."
        ),
    },
    {
        "id": "ramp",
        "name": "Bridge ramp (lower part)",
        "category": "bridge",
        "part_numbers": ["6392", "35136", "6231963"],
        "width": WIDTH,
        "provisional": True,
        # Underpass near the top only (user ruling 2026-08-04: touching under the
        # ramp's highest part is fine): the flag admits track beneath deck points
        # at least UNDERPASS_MIN higher, which the lower ramp never reaches.
        "underpass": True,
        "paths": [
            {"segments": [{"type": "ramp", "run": 320, "rise": "288/5"}]},
        ],
        "port_names": ["low", "high"],
        "notes": (
            "Inclined approach from sets 2738/10508/10872. Run 320 mm (confirmed: the "
            "full 4-piece bridge spans exactly 8 straights = 1024 mm, duplo-schienen "
            "Regel 5/6); rises 57.6 mm = 3 DUPLO bricks (a 76.8 mm rise is impossible "
            "inside the part's ~88 mm overall height). Mean grade 18%."
        ),
    },
    {
        "id": "span",
        "name": "Bridge arch (upper part)",
        "category": "bridge",
        "part_numbers": ["6393", "35138", "6232170"],
        "width": WIDTH,
        "provisional": True,
        "underpass": True,
        "paths": [
            {"segments": [{"type": "ramp", "run": 192, "rise": "96/5"}]},
        ],
        "port_names": ["low", "high"],
        "notes": (
            "Half-arch middle section; the deck is NOT level -- it keeps rising 19.2 mm "
            "(1 brick) over its 192 mm run and crests at 76.8 mm (4 bricks) where the "
            "two arches meet mid-bridge. Modelled piecewise-linear. Physically its low "
            "end is a special overlap joint onto the ramp needing 2-brick supports (no "
            "normal pin/socket); modelled as a normal port since the solver has no "
            "port-type machinery. UNDERPASS (user-verified 2026-08-04): a train passes "
            "beneath the arch near the crest -- provisional pending real measurements "
            "of deck height, ramp rise and under-arch clearance."
        ),
    },
]


# --------------------------------------------------------------------------------------
# Action stones (Funktionssteine): coloured inserts that clip onto a straight rail and
# trigger a behaviour in the powered trains (10874/10875) as they drive over.  They are
# accessories, not track -- no connectors, no geometry -- but they change what counts as
# a playable layout: a green direction-change stone lets a train run a layout endlessly
# without the track forming a plain closed loop (see the solver's reversing-loop mode).
# --------------------------------------------------------------------------------------

ACCESSORIES: dict[str, dict[str, str]] = {
    "stone_stop": {
        "name": "Stop stone",
        "color": "#c4281c",
        "design": "38507",
        "effect": "stops the train",
    },
    "stone_direction": {
        "name": "Direction-change stone",
        "color": "#237841",
        "design": "38506",
        "effect": "reverses the train's direction of travel",
    },
    "stone_refuel": {
        "name": "Refuel stone",
        "color": "#0055bf",
        "design": "38505",
        "effect": "pauses with a refuelling sound, then continues",
    },
    "stone_lights": {
        "name": "Lights stone",
        "color": "#f4f4f4",
        "design": "38508",
        "effect": "toggles the headlights",
    },
    "stone_horn": {
        "name": "Horn stone",
        "color": "#f2cd37",
        "design": "38509",
        "effect": "sounds the horn",
    },
}

#: Piece ids an action stone can clip onto (the flat sleeper area of a plain straight;
#: LEGO's 35965 'rail with plate' is counted as a straight in the set data).
STONE_MOUNTS = frozenset({"straight"})


def default_catalog() -> dict[str, PieceType]:
    """The built-in modern-generation piece set, keyed by id."""
    return parse_pieces(DEFAULT_CATALOG_SPECS)


def load_catalog(*paths: str | Path, include_default: bool = True) -> dict[str, PieceType]:
    """Load piece catalogues, later files overriding earlier ids.

    Each file is JSON: either a list of piece specs or ``{"pieces": [...]}``.  With
    *include_default* the built-in catalogue is the base layer, so a user file can both
    add new pieces and override a built-in one (e.g. correct a provisional dimension)
    by reusing its id.
    """
    specs: dict[str, dict[str, Any]] = {}
    if include_default:
        for spec in DEFAULT_CATALOG_SPECS:
            specs[spec["id"]] = spec
    for path in paths:
        with open(path, encoding="utf-8") as fh:
            data = json.load(fh)
        if isinstance(data, dict):
            if "pieces" not in data:
                raise ValueError(f"catalogue {path} has no 'pieces' key")
            entries = data["pieces"]
        else:
            entries = data
        for spec in entries:
            if "id" not in spec:
                raise ValueError(f"piece spec without an id in {path}")
            specs[spec["id"]] = spec
    return parse_pieces(specs.values())
