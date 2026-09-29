"""Raster regressions for locally ordered exported track, not solver geometry."""
import pytest

np = pytest.importorskip('numpy')
pytest.importorskip('matplotlib')
from matplotlib.backends.backend_agg import FigureCanvasAgg  # noqa: E402
from matplotlib.figure import Figure  # noqa: E402

from duplotrain.catalog import default_catalog  # noqa: E402
from duplotrain.geometry import Pose  # noqa: E402
from duplotrain.layout import Layout, Placement  # noqa: E402
from duplotrain.pieces import parse_piece  # noqa: E402
from duplotrain.render import RAIL, _track_chunks, elevation_color, render_layout  # noqa: E402


def rgb(hex_color):
    return np.array([int(hex_color[i:i + 2], 16) for i in (1, 3, 5)])


def canvas_for(layout, limits):
    figure = Figure(figsize=(9, 5))
    canvas = FigureCanvasAgg(figure)
    ax = figure.subplots()
    render_layout(layout, ax=ax, title='Crossing layers')
    ax.set_xlim(*limits[:2])
    ax.set_ylim(*limits[2:])
    canvas.draw()
    image = np.asarray(canvas.buffer_rgba())

    def pixel(x, y):
        sx, sy = ax.transData.transform((x, y))
        return image[image.shape[0] - round(sy) - 1, round(sx), :3].astype(int)

    return figure, ax, pixel


@pytest.mark.parametrize('reverse', [False, True])
@pytest.mark.parametrize('z', [-100, 0, 100])
def test_ground_rail_hidden_by_standard_ramp(reverse, z):
    catalog = default_catalog()
    placements = [Placement(catalog['ramp'], Pose.make(0, 0, z)),
                  Placement(catalog['straight'], Pose.make(310, -64, z, 6))]
    layout = Layout(placements[::-1] if reverse else placements)
    before = layout
    _figure, _ax, pixel = canvas_for(layout, (245, 335, -45, 45))
    actual = pixel(286, 8)
    assert np.max(np.abs(actual - rgb(elevation_color(286 / 320 * 57.6)))) <= 3
    assert np.max(np.abs(actual - rgb(RAIL))) > 40
    assert layout == before


@pytest.mark.parametrize('reverse', [False, True])
def test_one_ramp_goes_under_one_crossing_and_over_another(reverse):
    catalog = default_catalog()
    ramp = parse_piece({'id': 'long_climb', 'width': 64, 'category': 'bridge',
                        'paths': [{'segments': [{'type': 'ramp', 'run': 320, 'rise': 200}]}]})
    placements = [Placement(ramp, Pose.make(-160, 0, 0)),
                  Placement(catalog['straight'], Pose.make(-120, -64, 100, 6)),
                  Placement(catalog['straight'], Pose.make(120, -64, 100, 6))]
    layout = Layout(placements[::-1] if reverse else placements)
    _figure, _ax, pixel = canvas_for(layout, (-165, 165, -45, 45))
    # The first straight is above the climb, so its rail is visible; the other
    # straight is below the SAME climb and its rail must be hidden by the deck.
    assert np.max(np.abs(pixel(-144, 8) - rgb(RAIL))) <= 5
    assert np.max(np.abs(pixel(96, 8) - rgb(elevation_color(160)))) <= 8


def test_flat_path_not_fragmented_and_ramp_has_no_internal_end_caps():
    catalog = default_catalog()
    straight = list(_track_chunks(catalog['straight'].all_centrelines(6), 32))
    assert len(straight) == 1 and len(straight[0][2]) == 4
    ramp = list(_track_chunks(catalog['ramp'].all_centrelines(6), 32))
    assert len(ramp) > 2
    assert len(ramp[0][2]) == len(ramp[-1][2]) == 3
    assert all(len(chunk[2]) == 2 for chunk in ramp[1:-1])
    assert sum(len(chunk[4]) for chunk in ramp) == 10


@pytest.mark.parametrize('suffix', ['png', 'svg'])
def test_output_formats_and_caller_figure_remain_supported(tmp_path, suffix):
    catalog = default_catalog()
    layout = Layout([Placement(catalog['straight'], Pose.make())])
    fig = Figure()
    ax = fig.subplots()
    target = tmp_path / f'layout.{suffix}'
    result = render_layout(layout, path=str(target), ax=ax, title='$plain$')
    assert result is fig and target.stat().st_size > 100
    assert ax.get_title() == '$plain$' and not ax.title.get_parse_math()
