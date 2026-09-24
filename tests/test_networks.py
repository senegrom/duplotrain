"""Network enumeration and the exhaustive hunt for perfectly looping networks."""

import pytest

from duplotrain import Pose, SolverConfig, build_chain, parse_piece, solve
from duplotrain.catalog import default_catalog
from duplotrain.drive import classify
from duplotrain.exact import Alg
from duplotrain.explore import congruence_key, find_perfect_networks
from duplotrain.networks import NetworkConfig, enumerate_networks
from duplotrain.solver import _solution_overlaps
from duplotrain.symmetry import placement_key
from tests.test_congruence import long_straight_catalog


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


def test_shuttle_is_the_only_buffered_bar(catalog):
    result = enumerate_networks(
        {"straight": 3, "buffer": 2},
        catalog,
        NetworkConfig(use_all_pieces=True, max_pieces=5),
    )
    assert len(result.layouts) == 1
    layout = result.layouts[0]
    assert layout.is_closed  # buffer faces are sealed, not loose
    assert layout.piece_counts == {"straight": 3, "buffer": 2}


@pytest.mark.parametrize("inventory, owned, expected", [
    # The shuttle needs a guard stone at each buffer face: two stones.
    ({"straight": 3, "buffer": 2}, 1, 0),
    ({"straight": 3, "buffer": 2}, 2, 1),
    # The ring needs one mid-piece stone, which is optional only when owned.
    ({"curve": 12, "straight": 2}, 0, 0),
    ({"curve": 12, "straight": 2}, 1, 1),
])
def test_perfect_networks_use_only_the_stones_owned(catalog, inventory, owned, expected):
    perfect = find_perfect_networks(
        inventory, catalog, {"stone_direction": owned} if owned else {},
        NetworkConfig(use_all_pieces=True, max_pieces=sum(inventory.values())),
    )
    assert perfect.stats.complete and len(perfect) == expected
    for layout, verdict in perfect:
        assert verdict.perfectly_looping
        stones = [entry for entry in layout.accessories if entry[1] == "stone_direction"]
        assert len(stones) == len(layout.accessories) == owned
        if "buffer" in inventory:
            # Both buffer faces got their mandatory guard stones.
            guarded = {(entry[0], entry[2]) for entry in stones}
            assert guarded == {layout.links[(i, 0)] for i, p in enumerate(layout.placements)
                               if p.piece.id == "buffer"}
        else:
            assert [len(entry) for entry in stones] == [2]  # mid-piece, on a straight


def test_star_of_three_arms_is_never_perfect(catalog):
    """The sticky-tongue theorem: dead-end caps REFLECT, so a train ping-pongs
    between two arms of a 3-armed star forever and the third arm is never visited.
    A reflecting cap preserves the tongue; only a lobe (branch-to-branch loop)
    alternates it."""
    result = enumerate_networks(
        {"switch": 1, "straight": 3, "buffer": 3},
        catalog,
        NetworkConfig(use_all_pieces=True, max_pieces=7),
    )
    stars = [
        layout
        for layout in result.layouts
        if layout.piece_counts.get("switch") == 1
        and layout.piece_counts.get("buffer") == 3
    ]
    assert stars, "the Y-star network must be buildable"

    perfect = find_perfect_networks(
        {"switch": 1, "straight": 3, "buffer": 3},
        catalog,
        {"stone_direction": 3},
        NetworkConfig(use_all_pieces=True, max_pieces=7),
    )
    assert perfect == []  # looping at best, never perfect

    # Pick the symmetric star (one straight per arm) so every guard stone has a
    # straight to clip onto, and check the ladder verdict directly.
    def symmetric(layout):
        return all(
            layout.placements[layout.links[(i, 0)][0]].piece.id == "straight"
            for i, p in enumerate(layout.placements)
            if p.piece.id == "buffer"
        )

    star = next(s for s in stars if symmetric(s))
    guarded = star
    for index, placement in enumerate(star.placements):
        if placement.piece.id != "buffer":
            continue
        neighbour, port = star.links[(index, 0)]
        guarded = guarded.with_accessory(neighbour, "stone_direction", at_port=port)
    verdict = classify(guarded)
    assert verdict.looping  # nobody derails or stalls...
    assert not verdict.completely_looping  # ...but the third arm is never visited


def test_lattice_frames_convert_back_to_exact_layout_poses(catalog):
    from duplotrain import build_chain
    from duplotrain.geometry import ORIGIN
    from duplotrain.solver import _compile_lattice, _flat, _moves_for, _pose_to_lattice

    pieces = {pid: catalog[pid] for pid in ("straight", "curve", "switch", "ramp")}
    moves = {pid: _moves_for(p) for pid, p in pieces.items()}
    eng = _compile_lattice(ORIGIN, ORIGIN, pieces, moves)
    layout = build_chain([(catalog["curve"], 0, 1), (catalog["straight"], 0, 1),
                          (catalog["switch"], 0, 2), (catalog["ramp"], 1, 0),
                          (catalog["curve"], 1, 0)])
    for placement in layout:
        frame = _flat(_pose_to_lattice(placement.frame))
        assert eng.to_pose(frame) == placement.frame
        assert _flat(_pose_to_lattice(eng.to_pose(frame))) == frame


def test_enumerated_networks_equal_their_replayed_constructions(catalog):
    # The layouts are assembled directly from engine frames and the search's own
    # link map; replaying them through the checked constructors gives the same.
    from duplotrain import Layout

    result = enumerate_networks({"buffer": 2, "straight": 2, "curve": 3}, catalog,
                                NetworkConfig(max_pieces=7, max_results=50, max_nodes=200_000))
    assert result.layouts
    for layout in result.layouts:
        replayed = Layout()
        for index, placement in enumerate(layout.placements):
            if index == 0:
                replayed, _ = replayed.with_piece(placement.piece, placement.frame)
                continue
            # Every later piece is linked to an earlier one: attach it there.
            entry, at = next(
                (port, other) for (i, port), other in layout.links.items()
                if i == index and other[0] < index
            )
            replayed, new_index = replayed.attach(placement.piece, entry, at)
            assert new_index == index
        for a, b in layout.links.items():
            if a < b and a not in replayed.links:
                replayed = replayed.join(a, b)
        assert replayed == layout and not layout.joint_issues()


def _found(result):
    return [(tuple((p.piece.id, p.frame) for p in layout.placements), dict(layout.links))
            for layout in result.layouts]


@pytest.mark.parametrize("inventory, config", [
    ({"straight": 3, "buffer": 2}, dict(use_all_pieces=True, max_pieces=5)),
    ({"buffer": 2, "straight": 2, "curve": 2}, dict(max_pieces=6, max_results=100)),
    ({"switch": 1, "curve": 4, "straight": 1, "buffer": 2}, dict(max_pieces=8, max_results=100)),
    ({"crossing": 1, "curve": 4, "straight": 1, "buffer": 2}, dict(max_pieces=8, max_results=100)),
])
def test_reachability_prune_keeps_every_network_in_order(catalog, inventory, config):
    cfg = NetworkConfig(max_nodes=500_000, **config)
    plain = enumerate_networks(inventory, catalog, NetworkConfig(lookahead=0, max_nodes=500_000,
                                                                 **config))
    fast = enumerate_networks(inventory, catalog, cfg)
    assert plain.stats.complete and fast.stats.complete
    assert plain.stats.stop_reason == fast.stats.stop_reason == "exhausted"
    assert _found(fast) == _found(plain)
    assert fast.stats.nodes <= plain.stats.nodes
    assert {congruence_key(layout) for layout in fast.layouts} == {
        congruence_key(layout) for layout in plain.layouts}


def test_reachability_prune_cuts_the_ring_enumeration(catalog):
    # Twelve curves close one network, the circle, with or without the prune.
    plain = enumerate_networks({"curve": 12}, catalog,
                               NetworkConfig(use_all_pieces=True, max_pieces=12, lookahead=0))
    fast = enumerate_networks({"curve": 12}, catalog,
                              NetworkConfig(use_all_pieces=True, max_pieces=12))
    assert plain.stats.complete and fast.stats.complete
    assert plain.stats.stop_reason == fast.stats.stop_reason == "exhausted"
    assert _found(fast) == _found(plain) and len(fast.layouts) == 1
    assert fast.layouts[0].is_closed and fast.layouts[0].piece_counts == {"curve": 12}
    assert fast.stats.pruned_reachability > 0
    assert fast.stats.nodes * 50 < plain.stats.nodes


@pytest.mark.parametrize("inventory, max_pieces, expected", [
    ({"level_crossing": 2, "buffer": 2}, 4, 0),  # only plate against plate would close
    # One of these ovals would close its last joint plate to plate.
    ({"curve": 12, "level_crossing": 4, "straight": 2}, 18, 6),
])
def test_overhanging_plates_never_mate_in_a_network(catalog, inventory, max_pieces, expected):
    # Two level-crossing road plates overhang their joint: neither an attached
    # piece nor a closing join may put one against the other.
    result = enumerate_networks(inventory, catalog, NetworkConfig(
        use_all_pieces=True, max_pieces=max_pieces, max_results=100))
    assert result.stats.complete and len(result.layouts) == expected
    for layout in result.layouts:
        assert not layout.joint_issues()
        assert not any(layout.placements[a[0]].piece.end_overhang > 0
                       and layout.placements[b[0]].piece.end_overhang > 0
                       for a, b in layout.links.items())


def test_network_progress_is_reported_every_4096_nodes(catalog):
    calls = []
    result = enumerate_networks({"curve": 8, "straight": 2}, catalog, NetworkConfig(
        max_pieces=10, lookahead=0, progress=calls.append))
    assert result.stats.complete and result.stats.nodes > 2 * 4096
    assert calls == [4096 * k for k in range(1, result.stats.nodes // 4096 + 1)]


def test_reachability_prune_respects_caps_and_junction_closures(catalog):
    # Two open ends with two buffers in stock may both be capped; with one
    # buffer only one end may be stranded; a teardrop closes into its own switch.
    stranded = enumerate_networks({"straight": 4, "buffer": 2}, catalog,
                                  NetworkConfig(use_all_pieces=True, max_pieces=6))
    assert len(stranded.layouts) == 1 and stranded.stats.complete
    teardrop = enumerate_networks({"switch": 1, "curve": 12, "buffer": 1}, catalog,
                                  NetworkConfig(use_all_pieces=True, max_pieces=14,
                                                max_results=50, max_nodes=500_000))
    assert teardrop.layouts and teardrop.stats.complete
    assert all(layout.is_closed for layout in teardrop.layouts)


@pytest.mark.parametrize("lookahead", [-1, 13, 2.5, "10"])
def test_invalid_network_lookahead_is_rejected(lookahead):
    with pytest.raises(ValueError, match="completion_lookahead"):
        NetworkConfig(lookahead=lookahead)


@pytest.mark.parametrize("inventory, max_pieces, use_all, expected", [
    ({"buffer": 2, "straight": 2, "curve": 2}, 6, False, 21),
    ({"switch": 1, "curve": 4, "straight": 1, "buffer": 2}, 8, False, 49),
    ({"crossing": 1, "straight": 4, "buffer": 4}, 9, True, 11),
    ({"switch": 1, "curve": 3, "buffer": 3}, 7, True, 40),
    ({"crossing": 1, "curve": 4, "buffer": 2, "straight": 1}, 8, False, 49),
    ({"switch": 2, "straight": 2, "buffer": 4}, 8, True, 33),
])
def test_root_passes_find_every_class_once(catalog, inventory, max_pieces, use_all, expected):
    # Class counts pinned from the enumerator before a pass withdrew the types
    # whose passes came earlier. Every representative is rooted at the smallest
    # type it contains: the pass of that type found it first.
    result = enumerate_networks(inventory, catalog, NetworkConfig(
        max_pieces=max_pieces, use_all_pieces=use_all, max_results=100, max_nodes=500_000))
    assert result.stats.complete and len(result.layouts) == expected
    assert len({congruence_key(layout) for layout in result.layouts}) == expected
    for layout in result.layouts:
        assert layout.placements[0].piece.id == min(p.piece.id for p in layout.placements)


def test_network_field_bins_only_placements_a_query_reached(catalog, monkeypatch):
    from duplotrain.collision import CollisionField

    names = ("_prepare", "_clashes_prepared", "add_deferred", "_bin_deferred")
    originals = {name: getattr(CollisionField, name) for name in names}
    calls = dict.fromkeys(names, 0)

    def counting(name):
        def method(field, *args, **kwargs):
            calls[name] += 1
            return originals[name](field, *args, **kwargs)
        return method

    for name in names:
        monkeypatch.setattr(CollisionField, name, counting(name))
    result = enumerate_networks({"buffer": 2, "straight": 3, "curve": 3}, catalog,
                                NetworkConfig(max_pieces=8, max_results=500, max_nodes=200_000))
    assert len(result.layouts) == 109
    # Samples are translated and binned once per point test, once per deferred
    # placement a later query reached, and once per root pass; the audits of the
    # found networks prepare eagerly, twice per placement of at most eight.
    assert calls["add_deferred"] > 0 and calls["_clashes_prepared"] > 0
    search = calls["_prepare"] - 2 * sum(len(layout) for layout in result.layouts)
    assert search <= calls["_clashes_prepared"] + calls["_bin_deferred"] + 3


def test_two_stranded_ends_can_share_one_cap_through_a_new_switch():
    # buffer-switch-two lobes-switch-buffer: after [buffer, switch] both branch
    # ends are stranded with one buffer left, yet a second switch merges them.
    catalog = default_catalog()
    inventory = {"switch": 2, "curve": 4, "buffer": 2}
    pruned = enumerate_networks(inventory, catalog, NetworkConfig(max_pieces=8))
    unpruned = enumerate_networks(inventory, catalog, NetworkConfig(max_pieces=8, lookahead=0))
    assert pruned.stats.complete and len(pruned.layouts) == len(unpruned.layouts) == 14
    assert any(sorted(p.piece.id for p in layout.placements).count("buffer") == 2
               and sorted(p.piece.id for p in layout.placements).count("switch") == 2
               for layout in pruned.layouts)


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


def test_network_dedup_does_not_return_the_same_buffered_bar_twice():
    result = enumerate_networks(
        {"straight": 2, "long": 1, "buffer": 2}, long_straight_catalog(),
        NetworkConfig(min_pieces=3, max_pieces=4),
    )
    same_bar = [lay for lay in result.layouts if lay.track_length() == 384.0]
    # Both are identical straight centrelines from x=-320 to x=64, with
    # identical 64 mm widths and buffers; only the internal segmentation differs.
    assert len(same_bar) == 1, "the long rail and two short rails were counted twice"


def _oval_catalog():
    return {
        "long": parse_piece({"id": "long", "width": 64, "paths": [{"segments": [
            {"type": "straight", "run": "2559/10"},
        ]}]}),
        "bend": parse_piece({"id": "bend", "width": 64, "paths": [{"segments": [
            {"type": "arc", "radius": 256, "degrees": 60},
        ]}]}),
    }


def _exact_piece_key(layout):
    """Independent whole-piece orbit oracle; only for equal piece inventories."""
    ports = [p.port_pose(i) for p in layout for i in range(len(p.piece.ports))]
    centre = tuple(sum((getattr(p, axis) for p in ports), Alg(0)) / len(ports)
                   for axis in ("x", "y", "z"))
    candidates = []
    for heading in range(24):
        for mirror in (False, True):
            items = []
            for placement in layout:
                f = placement.frame
                centred = Pose(f.x - centre[0], f.y - centre[1], f.z - centre[2], f.heading)
                items.append((placement.piece.id, placement_key(
                    placement.piece, centred.rotated_about_origin(heading), mirror)))
            candidates.append(tuple(sorted(items)))
    return min(candidates)


def test_networks_do_not_count_the_decimal_tie_oval_twice():
    inventory, catalog = {"long": 2, "bend": 6}, _oval_catalog()
    result = enumerate_networks(inventory, catalog, NetworkConfig(
        use_all_pieces=True, max_pieces=8, max_results=100, max_nodes=100_000,
    ))
    reference = solve(inventory, catalog, SolverConfig(use_all_pieces=True, max_results=100))
    assert result.stats.complete and reference.stats.complete
    assert len(result.layouts) == len(reference.solutions) == 1
    assert _exact_piece_key(result.layouts[0]) == _exact_piece_key(reference.solutions[0].layout)
    assert result.layouts[0].is_closed and not result.layouts[0].joint_issues()
    assert not _solution_overlaps(result.layouts[0], 0, 120, 8)
