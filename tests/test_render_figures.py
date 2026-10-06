"""Rendering: track ordered by local height, rails and sleepers whole, height labels, and
pyplot's backend and figures left as the caller had them."""

import math

import pytest

matplotlib = pytest.importorskip("matplotlib")

import numpy as np  # noqa: E402

from duplotrain.catalog import default_catalog  # noqa: E402
from duplotrain.geometry import Pose  # noqa: E402
from duplotrain.layout import Layout, Placement, build_chain  # noqa: E402
from duplotrain.pieces import parse_piece  # noqa: E402
from duplotrain.render import (  # noqa: E402
    GAUGE,
    RAIL,
    _track_chunks,
    elevation_color,
    render_layout,
)


@pytest.fixture()
def layout():
    return build_chain([(default_catalog()["curve"], 0, 1)] * 12)


def raster(layout, limits, size=(9, 5), dpi=100):
    """Draw *layout* cut to *limits*; return a reader of the pixel at a data point."""
    from matplotlib.backends.backend_agg import FigureCanvasAgg
    from matplotlib.figure import Figure

    figure = Figure(figsize=size, dpi=dpi)
    canvas = FigureCanvasAgg(figure)
    ax = figure.subplots()
    render_layout(layout, ax=ax)
    for text in list(ax.texts):  # height labels and arrows are not track
        text.remove()
    ax.set_xlim(*limits[:2])
    ax.set_ylim(*limits[2:])
    canvas.draw()
    image = np.asarray(canvas.buffer_rgba())[:, :, :3].astype(int)

    def pixel(x, y):
        sx, sy = ax.transData.transform((x, y))
        return image[image.shape[0] - round(sy) - 1, round(sx)]

    return pixel


def off(pixel, colour):
    """Largest channel difference between a pixel and a hex colour."""
    return max(abs(int(pixel[i]) - int(colour[1 + 2 * i:3 + 2 * i], 16)) for i in range(3))


def placed(piece, x, y, z=0, heading=0):
    catalog = default_catalog()
    return Placement(catalog[piece] if isinstance(piece, str) else piece,
                     Pose.make(x, y, z, heading))


@pytest.mark.parametrize("reverse", [False, True])
@pytest.mark.parametrize("z", [-100, 0, 100])
def test_a_ramp_covers_the_ground_track_under_its_high_end(reverse, z):
    # Where a ground straight passes under a ramp's high end, the ramp's deck covers its
    # rail, whatever the order of the pieces or the layout's base height.
    pieces = [placed("ramp", 0, 0, z), placed("straight", 310, -64, z, 6)]
    pixel = raster(Layout(pieces[::-1] if reverse else pieces), (245, 335, -45, 45))
    assert off(pixel(286, 8), RAIL) > 40
    assert off(pixel(286, 8), elevation_color(286 / 320 * 57.6)) <= 3


@pytest.mark.parametrize("reverse", [False, True])
def test_a_climb_runs_under_one_crossing_and_over_another(reverse):
    # A ramp's foot passes under track raised on bricks to crest height, its top over
    # ground track: the raised rail shows, the ramp's and the ground rails are covered.
    pieces = [placed("ramp", 0, 0), placed("straight", 310, -64, 0, 6),
              placed("straight", 30, -64, "384/5", 6)]
    pixel = raster(Layout(pieces[::-1] if reverse else pieces), (-20, 345, -70, 70))
    assert off(pixel(54, 8), RAIL) <= 5
    assert off(pixel(20, 24), RAIL) > 40
    assert off(pixel(20, 24), elevation_color(76.8)) <= 5
    assert off(pixel(286, 8), RAIL) > 40
    # A steeper custom climb goes under one raised straight and over the other.
    climb = parse_piece({"id": "long_climb", "width": 64, "category": "bridge",
                         "paths": [{"segments": [{"type": "ramp", "run": 320, "rise": 200}]}]})
    pieces = [placed(climb, -160, 0), placed("straight", -120, -64, 100, 6),
              placed("straight", 120, -64, 100, 6)]
    pixel = raster(Layout(pieces[::-1] if reverse else pieces), (-165, 165, -45, 45))
    assert off(pixel(-144, 8), RAIL) <= 5
    assert off(pixel(96, 8), RAIL) > 40
    assert off(pixel(96, 8), elevation_color(160)) <= 8


@pytest.mark.parametrize("limits,dpi", [((-20, 300, -20, 300), 100),
                                        ((-600, 900, -600, 900), 150)])
def test_rails_run_unbroken_up_a_climb(limits, dpi):
    # The cuts leave no notch: every sample along a diagonal ramp's rail shows the rail
    # colour, at two zooms.
    ramp = placed("ramp", 0, 0, 0, 2)
    pixel = raster(Layout([ramp]), limits, size=(9, 9), dpi=dpi)
    cos, sin = math.cos(math.radians(30)), math.sin(math.radians(30))
    for k in range(400):
        d = 16 + 288 * (k + 0.5) / 400
        assert off(pixel(d * cos - sin * GAUGE / 2, d * sin + cos * GAUGE / 2), RAIL) <= 30, d


def test_sleepers_up_a_climb_keep_their_width():
    # No deck beside a cut covers part of a sleeper: every sleeper of a ramp and span
    # shows at one width.
    from matplotlib.backends.backend_agg import FigureCanvasAgg
    from matplotlib.figure import Figure

    from duplotrain.render import SLEEPER

    catalog = default_catalog()
    bridge = build_chain([(catalog["ramp"], 0, 1), (catalog["span"], 0, 1)])
    figure = Figure(figsize=(9, 3), dpi=150)
    FigureCanvasAgg(figure)
    ax = figure.subplots()
    render_layout(bridge, ax=ax)
    ax.set_xlim(-5, 517)
    ax.set_ylim(-60, 60)
    figure.canvas.draw()
    image = np.asarray(figure.canvas.buffer_rgba())[:, :, :3].astype(int)
    (x0, y), (x1, _y) = ax.transData.transform([(10, 12), (502, 12)])
    row = image[image.shape[0] - round(y) - 1, round(x0):round(x1)]
    sleeper = [off(pixel, SLEEPER) <= 4 for pixel in row]
    runs = [len(run) for run in "".join("x" if s else " " for s in sleeper).split()]
    assert len(runs) == 16 and min(runs) == max(runs)


def test_climbing_track_is_cut_between_its_sleepers_and_flat_track_stays_whole():
    catalog = default_catalog()
    (straight,) = _track_chunks(catalog["straight"].all_centrelines(6.0), 32)
    assert straight[2] is None and len(straight[4]) == 4  # one outlined deck
    ramp = list(_track_chunks(catalog["ramp"].all_centrelines(6.0), 32))
    # One piece per sleeper; only the ends of the path have end lines.
    assert len(ramp) == 10 and all(len(chunk[4]) == 1 for chunk in ramp)
    assert len(ramp[0][2]) == len(ramp[-1][2]) == 3
    assert all(len(chunk[2]) == 2 for chunk in ramp[1:-1])
    heights = [chunk[0] for chunk in ramp]
    assert heights == sorted(heights) and 0 < heights[0] < heights[-1] < 57.6
    # The deck is tinted finer than it is cut: about every 18 mm.
    tints = [tint for chunk in ramp for tint, _deck in chunk[1]]
    assert tints == sorted(tints) and len(tints) >= 18
    # Each sleeper sits well clear of the cuts, where the next deck starts.
    for index, (_height, decks, _edges, _rails, (sleeper,)) in enumerate(ramp):
        x = (sleeper[0][0] + sleeper[1][0]) / 2
        xs = [point[0] for _tint, deck in decks for point in deck]
        if index:
            assert x - min(xs) >= 10
        if index < len(ramp) - 1:
            assert max(xs) - x >= 10


def test_flat_track_draws_as_one_outlined_deck_per_path():
    from matplotlib.collections import LineCollection, PolyCollection
    from matplotlib.figure import Figure

    catalog = default_catalog()
    oval = build_chain([(catalog["curve"], 0, 1)] * 6 + [(catalog["straight"], 0, 1)] * 2
                       + [(catalog["curve"], 0, 1)] * 6 + [(catalog["switch"], 0, 1)])
    ax = Figure().subplots()
    render_layout(oval, ax=ax)
    decks = [c for c in ax.collections if isinstance(c, PolyCollection)]
    lines = [c for c in ax.collections if isinstance(c, LineCollection)]
    assert len(decks) == 1 and len(decks[0].get_paths()) == 16  # the switch has two
    assert decks[0].get_linewidths()[0] == 0.8 and decks[0].get_antialiased()[0]
    # Sleepers then rails: no separate edge lines on flat track.
    assert [c.get_linewidths()[0] for c in lines] == [2.2, 1.6]


@pytest.mark.parametrize("suffix", ["png", "svg"])
def test_a_callers_figure_saves_climbing_track(tmp_path, suffix):
    from matplotlib.figure import Figure

    catalog = default_catalog()
    bridge = build_chain([(catalog["ramp"], 0, 1), (catalog["span"], 0, 1)])
    figure = Figure()
    ax = figure.subplots()
    target = tmp_path / f"bridge.{suffix}"
    assert render_layout(bridge, path=str(target), ax=ax, title="$plain$") is figure
    assert target.stat().st_size > 100
    assert ax.get_title() == "$plain$" and not ax.title.get_parse_math()


def test_saving_a_file_touches_neither_the_backend_nor_open_figures(layout, tmp_path):
    import matplotlib.pyplot as plt

    backend, before = matplotlib.get_backend(), plt.get_fignums()
    render_layout(layout, path=str(tmp_path / "ring.png"))
    assert (tmp_path / "ring.png").stat().st_size > 0
    assert matplotlib.get_backend() == backend and plt.get_fignums() == before


def test_a_callers_axes_keep_their_figure_open(layout, tmp_path):
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots()
    try:
        render_layout(layout, path=str(tmp_path / "ring.png"), ax=ax)
        assert fig.number in plt.get_fignums()
    finally:
        plt.close(fig)


def test_a_failed_save_leaves_no_figure_behind(layout, tmp_path):
    import matplotlib.pyplot as plt

    before = plt.get_fignums()
    with pytest.raises(OSError):
        render_layout(layout, path=str(tmp_path / "missing" / "ring.png"))
    assert plt.get_fignums() == before


def test_the_default_title_is_plain_text(tmp_path):
    # Dollar signs in a piece id are no mathematics: read as math, this one failed
    # the save.
    from duplotrain.pieces import parse_piece

    piece = parse_piece({"id": "arc$\\frac$", "paths": [
        {"segments": [{"type": "arc", "radius": 256, "degrees": 30}]}]})
    figure = render_layout(build_chain([(piece, 0, 1)] * 12), path=str(tmp_path / "ring.png"))
    assert figure.axes[0].get_title().startswith("12 arc$\\frac$  |")


def test_heights_count_from_the_lowest_track_and_stand_clear_of_stones():
    from matplotlib.figure import Figure

    catalog = default_catalog()
    ramp, span, straight = catalog["ramp"], catalog["span"], catalog["straight"]
    # Down from a crest, the walk's own heights run below zero; up to one, the
    # straight at the crest stands on bricks.
    down = build_chain([(span, 1, 0), (ramp, 1, 0), (straight, 0, 1)])
    up = build_chain([(ramp, 0, 1), (span, 0, 1), (straight, 0, 1)])
    for layout, labels in ((down, ["+29mm", "+67mm"]), (up, ["+29mm", "+67mm", "+77mm"])):
        ax = Figure().subplots()
        render_layout(layout, ax=ax)
        assert sorted(text.get_text() for text in ax.texts if text.get_text()) == labels
    # The label of a piece carrying a stone moves below the stone.
    ax = Figure().subplots()
    render_layout(up.with_accessory(2, "stone_direction"), ax=ax)
    offsets = {text.get_text(): tuple(text.xyann) for text in ax.texts if text.get_text()}
    assert offsets["+77mm"] == (0, -12) and offsets["+29mm"] == (0, 0)


def test_track_on_slight_slopes_is_labelled_once_it_stands_a_brick_high():
    from matplotlib.figure import Figure

    catalog = default_catalog()
    slope, straight = catalog["slope"], catalog["straight"]
    # A slight slope rises 5.6 mm: track less than a brick (19.2 mm) up rests on its
    # joints and gets no label; four slopes up, it stands on bricks.
    for slopes, labels in ((1, []), (3, []), (4, ["+22mm"])):
        ax = Figure().subplots()
        render_layout(build_chain([(slope, 0, 1)] * slopes + [(straight, 0, 1)]), ax=ax)
        assert [text.get_text() for text in ax.texts if text.get_text()] == labels


def test_track_is_labelled_from_a_whole_brick_up():
    from fractions import Fraction

    from matplotlib.figure import Figure

    from duplotrain.geometry import ORIGIN, Pose
    from duplotrain.layout import Layout

    straight = default_catalog()["straight"]
    brick = Fraction(96, 5)  # one DUPLO brick, 19.2 mm
    # A straight a whole brick above the floor track stands on one brick; a tenth of
    # a millimetre lower, it stands on none.
    for rise, labels in ((brick, ["+19mm"]), (brick - Fraction(1, 10), [])):
        layout, _ = Layout().with_piece(straight, ORIGIN)
        layout, _ = layout.with_piece(straight, Pose.make(y=200, z=rise))
        ax = Figure().subplots()
        render_layout(layout, ax=ax)
        assert [text.get_text() for text in ax.texts if text.get_text()] == labels
