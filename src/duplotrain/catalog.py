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

Pieces marked ``provisional`` carry a dimension nobody has published; the value used is
derived and clearly noted.  Override any piece by loading a user catalogue on top --
same JSON schema, matching ids replace the built-ins.
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
            "route through a DUPLO switch, and the two exits sit 60 deg apart. Modelled "
            "as two nominal 30 deg / R256 curves; Gilbert (onemetre.net) measured the "
            "real branch nearer 29.7 deg, absorbed in practice by joint play."
        ),
    },
    {
        "id": "crossing",
        "name": "Track crossing (60 deg X)",
        "category": "junction",
        "part_numbers": ["6376"],
        "width": WIDTH,
        "provisional": True,
        "paths": [
            # Two straight runs crossing at their midpoints, 60 degrees apart.
            {"segments": [{"type": "straight", "run": 192}]},
            {
                "start": {"x": 48, "y": {"alg": [0, 0, -48, 0]}, "heading_deg": 60},
                "segments": [{"type": "straight", "run": 192}],
            },
        ],
        "port_names": ["a", "b", "c", "d"],
        "notes": (
            "Out of production since ~2008. Crossing angle 60 deg is documented; the "
            "192 mm (12-stud) run length is inferred from BrickLink's 12 x 14 stud "
            "bounding box and should be confirmed by measurement."
        ),
    },
    {
        "id": "level_crossing",
        "name": "Level crossing plate",
        "category": "track",
        "part_numbers": ["6391", "6207496"],
        "width": 160,
        "paths": [
            {"segments": [{"type": "straight", "run": STRAIGHT}]},
        ],
        "port_names": ["a", "b"],
        "notes": (
            "Rail run is one plain straight (128 mm); the road plate is 10 x 10 studs "
            "(160 x 160 mm), which is why two of these cannot sit adjacent in reality."
        ),
    },
    {
        "id": "ramp",
        "name": "Bridge ramp (ascending half)",
        "category": "bridge",
        "part_numbers": ["6392", "35136", "6231963"],
        "width": WIDTH,
        "provisional": True,
        "paths": [
            {"segments": [{"type": "ramp", "run": 320, "rise": "384/5"}]},
        ],
        "port_names": ["low", "high"],
        "notes": (
            "Inclined approach from set 10872. The full 4-piece bridge spans exactly 8 "
            "straights = 1024 mm of run (duplo-schienen Regel 5), split here as ramp "
            "320 mm + span 192 mm per half. The 76.8 mm rise (4 DUPLO brick heights) is "
            "derived from part bounding boxes, not published -- measure before trusting."
        ),
    },
    {
        "id": "span",
        "name": "Bridge span (level top)",
        "category": "bridge",
        "part_numbers": ["6393", "35138", "6232170"],
        "width": WIDTH,
        "provisional": True,
        "paths": [
            {"segments": [{"type": "straight", "run": 192}]},
        ],
        "port_names": ["a", "b"],
        "notes": (
            "Raised level section from set 10872; two of them bridge between the tops "
            "of two ramps. Run length 192 mm inferred from the 1024 mm total; modelled "
            "level, with the ramps carrying all the rise."
        ),
    },
]


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
        entries = data["pieces"] if isinstance(data, dict) else data
        for spec in entries:
            if "id" not in spec:
                raise ValueError(f"piece spec without an id in {path}")
            specs[spec["id"]] = spec
    return parse_pieces(specs.values())
