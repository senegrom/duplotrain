"""LEGO set contents, so an inventory can be "the sets we own".

Counts cover the modern (2018) DUPLO train wave and were taken from the Brickset /
BrickOwl inventories of each set.  Only track geometry and action stones are listed --
locomotives, wagons, figures and scenery bricks don't affect layouts.

LEGO's 35965 "rail with plate" (a straight with a 2x4 mounting plate between the
sleepers) is geometrically a plain straight and is counted as one.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Mapping

__all__ = ["TrainSet", "SETS", "inventory_for_sets"]


@dataclass(frozen=True, slots=True)
class TrainSet:
    code: str
    name: str
    year: int
    pieces: Mapping[str, int]
    stones: Mapping[str, int] = field(default_factory=dict)
    notes: str = ""


SETS: dict[str, TrainSet] = {
    s.code: s
    for s in [
        TrainSet(
            code="10874",
            name="Steam Train",
            year=2018,
            pieces={"curve": 12, "straight": 4},
            stones={
                "stone_stop": 1,
                "stone_direction": 1,
                "stone_refuel": 1,
                "stone_lights": 1,
                "stone_horn": 1,
            },
            notes="Push-and-go powered loco; 3 plain straights + 1 rail-with-plate (35965).",
        ),
        TrainSet(
            code="10875",
            name="Cargo Train",
            year=2018,
            pieces={
                "curve": 14,
                "straight": 3,
                "switch": 2,
                "level_crossing": 1,
                "slope": 2,
            },
            stones={
                "stone_stop": 1,
                "stone_direction": 1,
                "stone_refuel": 1,
                "stone_lights": 1,
                "stone_horn": 1,
            },
            notes=(
                "2 plain straights + 1 rail-with-plate (35965); the two 35966 slight "
                "slopes are the crane approach."
            ),
        ),
        TrainSet(
            code="10872",
            name="Train Bridge and Tracks",
            year=2018,
            pieces={"straight": 8, "ramp": 2, "span": 2},
            notes="The four bridge pieces span exactly 8 straights (1024 mm) of run.",
        ),
        TrainSet(
            code="10425",
            name="Train Tunnel and Tracks",
            year=2024,
            pieces={"curve": 10, "switch": 1, "buffer": 1, "straight": 1, "offramp": 1},
            notes=(
                "The straight is the new rail-with-plates 5370; buffer 35967 in "
                "reddish orange; plus the 96 mm off-ramp (4785) and a tunnel arch "
                "(scenery, not track). Its white 'rail accessory no. 7' action stone "
                "is a 2024-generation function brick not yet modelled."
            ),
        ),
        TrainSet(
            code="10426",
            name="Train Bridge and Tracks Expansion Set",
            year=2024,
            pieces={"straight": 9, "ramp": 2, "span": 2},
            notes=(
                "8 plain straights + 1 rail-with-plates 5370. The redesigned bridge "
                "moulds (5086 lower x2, 5087 upper x2) keep the classic 8-straight "
                "1024 mm span and are mapped onto the 6392/6393 geometry; its 'rail "
                "accessory no. 8' stone is not yet modelled."
            ),
        ),
        TrainSet(
            code="10882",
            name="Train Tracks",
            year=2018,
            pieces={
                "curve": 10,
                "straight": 1,
                "switch": 2,
                "level_crossing": 1,
                "buffer": 2,
            },
            stones={"stone_stop": 1},
            notes="Track expansion pack: also includes one red stop stone (38507).",
        ),
    ]
}


def inventory_for_sets(
    codes: Iterable[str],
) -> tuple[dict[str, int], dict[str, int]]:
    """Combined ``(track pieces, action stones)`` for the given set numbers.

    Repeat a code to own a set twice.  Raises ``ValueError`` for unknown sets, naming
    the ones that exist.
    """
    pieces: dict[str, int] = {}
    stones: dict[str, int] = {}
    for code in codes:
        clean = str(code).strip()
        if clean not in SETS:
            known = ", ".join(sorted(SETS))
            raise ValueError(f"unknown set {clean!r}; known sets: {known}")
        train_set = SETS[clean]
        for pid, n in train_set.pieces.items():
            pieces[pid] = pieces.get(pid, 0) + n
        for sid, n in train_set.stones.items():
            stones[sid] = stones.get(sid, 0) + n
    return pieces, stones
