"""The benchmark scripts still run against the current API: one quick pass each."""
import importlib
import json
import sys

import pytest


@pytest.mark.parametrize("name,args", [
    ("completion", ["--case", "offset_circle_slop_5"]),
    ("collision_index", ["--extra-loops", "0", "--count-bounds"]),
    ("editor_completion", []),
    ("editor_payload", []),
    ("editor_presentation", []),
])
def test_benchmark_script_runs_and_reports_json(name, args, monkeypatch, capsys):
    script = importlib.import_module(f"benchmarks.{name}")
    monkeypatch.setattr(sys, "argv", [name, "--repeats", "1", *args])
    script.main()
    lines = capsys.readouterr().out.splitlines()
    assert len(lines) >= 2 and all(isinstance(json.loads(line), dict) for line in lines)
    if name == "editor_completion":  # docs/performance.md#representative-times
        rows = {row["case"]: row for row in map(json.loads, lines[1:])}
        assert rows["mixed_gap"]["nodes"] == 138
        reported = [rows[f"reported_{stock}_{end}"] for stock in ("finite", "unlimited")
                    for end in ("forward", "reverse")]
        assert [row["nodes"] for row in reported] == [1742, 718, 1878, 854]
        # Eight 24-piece closings each, which the benchmark audits as it goes.
        assert all(row["found"] == 8 and row["added"] == [24] * 8 for row in reported)
