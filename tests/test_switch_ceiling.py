"""The switch ceiling: no perfect layout has 3+ switches (abstract exhaustion).

Runs the wiring enumerator from docs/switch_ceiling_proof.py over all abstract
networks of n switches (ports joined by paths or capped with guarded-buffer
reflectors -- which also subsumes every mid-path direction stone, since a stone
splits its path into two reflector stubs) and simulates the exact tongue
automaton from every start and every initial tongue assignment.

Expected: exactly ONE perfect wiring at n=1 (teardrop + guarded tail), exactly
ONE at n=2 (the dogbone), and NONE at n=3.  Path lengths and geometry are
irrelevant to the sweep question, so this is a proof for layouts of any size.
"""

import importlib.util
import pathlib

import pytest

_PROOF = pathlib.Path(__file__).resolve().parent.parent / "docs" / "switch_ceiling_proof.py"


@pytest.fixture(scope="module")
def proof():
    spec = importlib.util.spec_from_file_location("switch_ceiling_proof", _PROOF)
    module = importlib.util.module_from_spec(spec)
    # The module prints its report on import; that's fine under pytest -s.
    spec.loader.exec_module(module)
    return module


def perfect_wirings(proof, n):
    out = []
    for edges, caps in proof.all_wirings(n):
        if not edges or not proof.is_connected(n, edges, caps):
            continue
        if proof.classify_wiring(n, edges, caps):
            out.append((edges, caps))
    return out


def test_one_switch_teardrop_is_the_only_perfect_wiring(proof):
    found = perfect_wirings(proof, 1)
    assert found == [((((0, "L"), (0, "R")),), ((0, "S"),))]


def test_two_switches_dogbone_is_the_only_perfect_wiring(proof):
    found = perfect_wirings(proof, 2)
    assert len(found) == 1
    edges, caps = found[0]
    assert caps == ()
    assert set(edges) == {
        ((0, "S"), (1, "S")),
        ((0, "L"), (0, "R")),
        ((1, "L"), (1, "R")),
    }


def test_three_switches_never_perfect(proof):
    assert perfect_wirings(proof, 3) == []
