"""duplotrain: model LEGO DUPLO train track and find layouts that loop nicely.

Quick taste::

    from duplotrain import default_catalog, solve, SolverConfig, render_layout

    pieces = default_catalog()
    result = solve({"curve": 12, "straight": 4}, pieces)
    best = result.solutions[0]
    render_layout(best.layout, "oval.png")
"""

from .catalog import default_catalog
from .drive import ClassificationLimitError, DriveLimitError, classify, drive
from .explore import (
    IncompleteSearchError,
    PerfectResult,
    congruence_key,
    find_perfect_loops,
    find_perfect_networks,
    is_stem_tailed,
    make_dogbone,
    pick_stem_tailed,
)
from .geometry import ORIGIN, Pose
from .layout import Layout, Placement, build_chain, layout_from_dict, layout_to_dict
from .networks import NetworkConfig, enumerate_networks
from .pieces import parse_piece
from .render import render_layout
from .solver import SolverConfig, solve

__version__ = "0.1.0"

__all__ = [
    "Pose",
    "ORIGIN",
    "parse_piece",
    "default_catalog",
    "Layout",
    "Placement",
    "build_chain",
    "layout_to_dict",
    "layout_from_dict",
    "solve",
    "SolverConfig",
    "drive",
    "classify",
    "ClassificationLimitError",
    "DriveLimitError",
    "congruence_key",
    "find_perfect_loops",
    "find_perfect_networks",
    "PerfectResult",
    "IncompleteSearchError",
    "enumerate_networks",
    "NetworkConfig",
    "make_dogbone",
    "is_stem_tailed",
    "pick_stem_tailed",
    "render_layout",
    "__version__",
]

