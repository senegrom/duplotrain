"""Regressions from the second repository review: geometry, atomicity and CLI inputs."""

import json

import pytest
from click.testing import CliRunner

from duplotrain import (
    NetworkConfig,
    SolverConfig,
    build_chain,
    default_catalog,
    enumerate_networks,
    parse_piece,
    solve,
)
from duplotrain.cli import main
from duplotrain.explore import congruence_key
from duplotrain.gui import Session, dispatch_session
from duplotrain.solver import _solution_overlaps


@pytest.mark.parametrize("radius,width", [(512, 96), (1024, 192), ("3585/7", 96)])
def test_network_retains_a_valid_wide_circle(radius, width):
    catalog = default_catalog()
    catalog["curve"] = parse_piece({
        "id": "curve", "width": width,
        "paths": [{"segments": [
            {"type": "arc", "radius": radius, "degrees": 30},
        ]}],
    })
    circle = build_chain([(catalog["curve"], 0, 1)] * 12)
    circle = circle.join((0, 0), (11, 1))
    assert circle.is_closed and not circle.joint_issues()
    assert not _solution_overlaps(circle, 0, 120.0, 8.0)

    loops = solve(
        {"curve": 12}, catalog,
        SolverConfig(min_pieces=12, use_all_pieces=True, max_results=100),
    )
    assert len(loops.solutions) == 1 and loops.stats.complete
    networks = enumerate_networks(
        {"curve": 12}, catalog,
        NetworkConfig(min_pieces=12, max_pieces=12,
                      use_all_pieces=True, max_results=100),
    )
    assert networks.stats.complete and networks.stats.stop_reason == "exhausted"
    assert len(networks.layouts) == 1, "a valid circle was pruned before emission"


def test_rejected_solve_preserves_session_revision():
    catalog = default_catalog()
    unjoined_circle = build_chain([(catalog["curve"], 0, 1)] * 12)
    session = Session(catalog=catalog, inventory={"curve": 12}, history=[unjoined_circle])
    before = session.snapshot(), session.revision, session._candidate_revision
    with pytest.raises(ValueError, match="already mate"):
        dispatch_session(session, "/api/solve", {
            "revision": session.revision, "reversing": True,
        })
    after = session.snapshot(), session.revision, session._candidate_revision
    unchanged = after == before
    assert unchanged, "a rejected request changed revision/candidate state"


def long_straight_catalog():
    catalog = default_catalog()
    catalog["long"] = parse_piece({
        "id": "long", "width": 64,
        "paths": [{"segments": [{"type": "straight", "run": 256}]}],
    })
    return catalog


def test_congruence_is_independent_of_straight_segmentation():
    catalog = long_straight_catalog()
    split = build_chain([(catalog["straight"], 0, 1)] * 2)
    whole = build_chain([(catalog["long"], 0, 1)])
    assert split.pose_of((0, 0)) == whole.pose_of((0, 0))
    assert split.pose_of((1, 1)) == whole.pose_of((0, 1))
    same_curve_key = congruence_key(split) == congruence_key(whole)
    assert same_curve_key, (
        "the same 256 mm centreline has a 34-point key versus a 33-point key"
    )


def test_network_dedup_does_not_return_the_same_buffered_bar_twice():
    result = enumerate_networks(
        {"straight": 2, "long": 1, "buffer": 2}, long_straight_catalog(),
        NetworkConfig(min_pieces=3, max_pieces=4),
    )
    same_bar = [lay for lay in result.layouts if lay.track_length() == 384.0]
    # Both are identical straight centrelines from x=-320 to x=64, with
    # identical 64 mm widths and buffers; only the internal segmentation differs.
    assert len(same_bar) == 1, "the long rail and two short rails were counted twice"


@pytest.mark.parametrize("inventory", [
    {"curve": 12.75},
    {"curve": 12, "straight": True},
])
def test_cli_rejects_raw_noninteger_inventory(tmp_path, inventory):
    path = tmp_path / "inventory.json"
    path.write_text(json.dumps(inventory), encoding="utf-8")
    result = CliRunner().invoke(main, ["solve", "--inventory", str(path)])
    assert result.exit_code != 0, "CLI converted invalid counts into valid integers"


def test_cli_rejects_negative_piece_flags():
    result = CliRunner().invoke(main, ["solve", "--curve", "12", "--straight", "-4"])
    assert result.exit_code != 0, "CLI silently dropped the negative count"


def test_true_wide_piece_overlap_is_still_rejected():
    catalog = default_catalog()
    catalog["curve"] = parse_piece({
        "id": "curve", "width": 160,
        "paths": [{"segments": [{"type": "arc", "radius": 256, "degrees": 30}]}],
    })
    circle = build_chain([(catalog["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    assert _solution_overlaps(circle, 0, 120.0, 8.0)
    result = enumerate_networks(
        {"curve": 12}, catalog,
        NetworkConfig(min_pieces=12, max_pieces=12, use_all_pieces=True),
    )
    assert result.stats.complete and result.layouts == []
