"""duplotrain: model LEGO DUPLO train track and find layouts that loop nicely.

Quick taste::

    from duplotrain import default_catalog, solve, SolverConfig, render_layout

    pieces = default_catalog()
    result = solve({"curve": 12, "straight": 4}, pieces)
    best = result.solutions[0]
    render_layout(best.layout, "oval.png")
"""

from typing import TYPE_CHECKING

from .catalog import default_catalog, load_catalog
from .exact import Alg
from .geometry import ORIGIN, Pose
from .layout import Layout, Placement, build_chain, layout_from_dict, layout_to_dict
from .pieces import PieceType, parse_piece, parse_pieces
from .scoring import ScoreWeights, score_solution
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
