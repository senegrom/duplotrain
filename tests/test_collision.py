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


def test_cell_box_pretest_never_changes_a_verdict():
    """The box test only skips cell clouds that no sample pair could bring within
    the limit; every verdict must equal the plain pairwise scan's."""
    import random

    from duplotrain.collision import DEFAULT_CLEARANCE, TOUCH_MARGIN, UNDERPASS_MIN

    rng = random.Random(11)

    def cloud(n, spread=600.0):
        cx, cy = rng.uniform(-spread, spread), rng.uniform(-spread, spread)
        cz = rng.choice([0.0, 0.0, 57.6, 76.8])
        return [(cx + rng.uniform(-70, 70), cy + rng.uniform(-70, 70), cz) for _ in range(n)]

    def naive(stored, points, half, ignore, underpass):
        for index, (pts, width, arch) in enumerate(stored):
            if index in ignore:
                continue
            limit = half + width - TOUCH_MARGIN
            for x, y, z in points:
                for px, py, pz in pts:
                    dz = z - pz
                    if dz >= DEFAULT_CLEARANCE or dz <= -DEFAULT_CLEARANCE:
                        continue
                    if arch and dz <= -UNDERPASS_MIN:
                        continue
                    if underpass and dz >= UNDERPASS_MIN:
                        continue
                    if (x - px) ** 2 + (y - py) ** 2 < limit * limit:
                        return True
        return False

    verdicts = {True: 0, False: 0}
    for _ in range(40):
        field = CollisionField()
        stored = []
        for index in range(rng.randint(1, 12)):
            pts, width = cloud(rng.randint(3, 40)), rng.choice([32.0, 32.0, 80.0])
            arch = rng.random() < 0.3
            field.add(index, pts, width, underpass=arch)
            stored.append((pts, width, arch))
        for _ in range(25):
            points, half = cloud(rng.randint(3, 30), 500.0), rng.choice([32.0, 80.0])
            ignore = {rng.randrange(len(stored))} if rng.random() < 0.3 else set()
            underpass = rng.random() < 0.3
            expected = naive(stored, points, half, ignore, underpass)
            assert field.clashes(points, half, ignore, underpass=underpass) is expected
            verdicts[expected] += 1
    assert verdicts[True] > 50 and verdicts[False] > 50
