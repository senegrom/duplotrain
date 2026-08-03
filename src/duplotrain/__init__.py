"""duplotrain: model LEGO DUPLO train track and find layouts that loop nicely.

Quick taste::

    from duplotrain import default_catalog, solve, SolverConfig, render_layout

    pieces = default_catalog()
    result = solve({"curve": 12, "straight": 4}, pieces)
    best = result.solutions[0]
    render_layout(best.layout, "oval.png")
"""

from typing import TYPE_CHECKING

from .catalog import ACCESSORIES, default_catalog, load_catalog
from .drive import DriveReport, LoopClassification, classify, drive, endless_run
from .exact import Alg
from .explore import congruence_key, find_perfect_loops, make_dogbone
from .geometry import ORIGIN, Pose
from .layout import Layout, Placement, build_chain, layout_from_dict, layout_to_dict
from .pieces import PieceType, parse_piece, parse_pieces
from .scoring import ScoreWeights, score_solution
from .sets import SETS, inventory_for_sets
from .solver import Solution, SolveResult, SolverConfig, solve

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
    "endless_run",
    "classify",
    "DriveReport",
    "LoopClassification",
    "congruence_key",
    "find_perfect_loops",
    "make_dogbone",
    "render_layout",
    "__version__",
]


if TYPE_CHECKING:  # give type checkers and IDEs the real signature
    from .render import render_layout
else:

    def render_layout(*args, **kwargs):
        """Lazy proxy for :func:`duplotrain.render.render_layout` (needs matplotlib)."""
        from .render import render_layout as _render

        return _render(*args, **kwargs)
