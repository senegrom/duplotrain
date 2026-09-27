"""Rendering to a file leaves pyplot's backend and figures as the caller had them."""

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
