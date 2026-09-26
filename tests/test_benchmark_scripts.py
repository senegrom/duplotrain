"""The benchmark scripts still run against the current API: one quick pass each."""
import importlib
import json
import sys

import pytest


@pytest.mark.parametrize("name,args", [
    ("completion", ["--case", "offset_circle_slop_5"]),
    ("collision_index", ["--extra-loops", "0"]),
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
