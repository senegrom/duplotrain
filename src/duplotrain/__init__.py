"""duplotrain: model LEGO DUPLO train track and find layouts that loop nicely.

Quick taste::

    from duplotrain import default_catalog, solve, SolverConfig, render_layout

    pieces = default_catalog()
    result = solve({"curve": 12, "straight": 4}, pieces)
    best = result.solutions[0]
    render_layout(best.layout, "oval.png")
"""

from .catalog import ACCESSORIES, default_catalog, load_catalog
from .drive import (
    ClassificationLimitError,
    DriveLimitError,
    DriveReport,
    LoopClassification,
    classify,
    drive,
)
from .exact import Alg
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
from .pieces import PieceType, parse_piece, parse_pieces
from .render import render_layout
from .scoring import ScoreWeights, score_solution
from .sets import SETS, inventory_for_sets
from .solver import Solution, SolverConfig, SolveResult, solve

__version__ = "0.1.0"

__all__ = [
    "Alg",
    "Pose",
    "ORIGIN",
    "PieceType",
    "parse_piece",
    "parse_pieces",
    "default_catalog",
    "load_catalog",
    "ACCESSORIES",
    "SETS",
    "inventory_for_sets",
    "Layout",
    "Placement",
    "build_chain",
    "layout_to_dict",
    "layout_from_dict",
    "solve",
    "SolverConfig",
    "SolveResult",
    "Solution",
    "ScoreWeights",
    "score_solution",
    "drive",
    "classify",
    "DriveReport",
    "LoopClassification",
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

