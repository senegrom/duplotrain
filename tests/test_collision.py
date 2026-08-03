"""The collision field: wide-piece reach, position independence, z clearance."""

from duplotrain.collision import CollisionField


def straight_line(y: float, z: float = 0.0, x0: float = 0.0, x1: float = 128.0, step: float = 8.0):
    points = []
    x = x0
    while x <= x1:
        points.append((x, y, z))
        x += step
    return points


def test_wide_piece_collision_is_position_independent():
    """Regression: the fixed 3x3 cell scan missed overlaps beyond 96 mm.

    Two 160 mm level-crossing plates interact out to 158 mm; whether their rows land
    in adjacent grid cells must not decide whether the overlap is seen.
    """
    lc_half = 80.0

    field = CollisionField()
    field.add(0, straight_line(40.0), lc_half)
    # 152.5 mm apart: inside the 158 mm limit, but two grid rows away.
    assert field.clashes(straight_line(192.5), lc_half, ignore=set())

    field = CollisionField()
    field.add(0, straight_line(95.0), lc_half)
    # Level crossing vs plain 64 mm track: limit 110 mm.
    assert field.clashes(straight_line(192.5), 32.0, ignore=set())

    # The same geometry translated arbitrarily gives the same verdicts.
    for dx, dy in [(1000.0, -500.0), (-37.0, 2049.5), (48.0, 48.0)]:
        field = CollisionField()
        field.add(0, [(x + dx, y + dy, z) for x, y, z in straight_line(40.0)], lc_half)
        assert field.clashes(
            [(x + dx, y + dy, z) for x, y, z in straight_line(192.5)],
            lc_half,
            ignore=set(),
        )


def test_plain_track_thresholds_unchanged():
    field = CollisionField()
    field.add(0, straight_line(0.0), 32.0)
    # Flush parallel tracks (64 mm apart) stay legal...
    assert not field.clashes(straight_line(64.0), 32.0, ignore=set())
    # ...but anything closer than the touch margin is an overlap.
    assert field.clashes(straight_line(60.0), 32.0, ignore=set())


def test_pop_restores_reach_bookkeeping():
    field = CollisionField()
    field.add(0, straight_line(0.0), 32.0)
    field.add(1, straight_line(400.0), 80.0)  # widens the max stored half-width
    field.pop()
    # With the wide cloud gone, a probe near where it was must be clean again,
    # and the narrow cloud still collides as before.
    assert not field.clashes(straight_line(400.0), 80.0, ignore=set())
    assert field.clashes(straight_line(30.0), 32.0, ignore=set())


def test_z_clearance_lets_high_track_over_low():
    """An elevated deck passes over ground track only above the clearance."""
    ground = straight_line(0.0, z=0.0)

    field = CollisionField()  # default clearance: 120 mm
    field.add(0, ground, 32.0)
    deck_at_77 = straight_line(0.0, z=76.8)
    assert field.clashes(deck_at_77, 32.0, ignore=set())  # bridge crest: too low

    field = CollisionField(clearance=50.0)
    field.add(0, ground, 32.0)
    assert not field.clashes(deck_at_77, 32.0, ignore=set())  # user-lowered bar