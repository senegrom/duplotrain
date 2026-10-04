"""Rendering: height labels, and pyplot's backend and figures left as the caller had them."""

import pytest

matplotlib = pytest.importorskip("matplotlib")

from duplotrain.catalog import default_catalog  # noqa: E402
from duplotrain.layout import build_chain  # noqa: E402
from duplotrain.render import render_layout  # noqa: E402


@pytest.fixture()
def layout():
    return build_chain([(default_catalog()["curve"], 0, 1)] * 12)


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
