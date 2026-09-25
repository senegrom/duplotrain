"""Malformed catalogue input is reported by the existing CLI error boundary."""
import json

import pytest
from click.testing import CliRunner

from duplotrain.cli import main


@pytest.mark.parametrize("field,value", [("run", 10**400), ("width", 10**400),
                                         ("width", 1e12), ("end_overhang", 1e12)])
def test_huge_catalogue_values_are_polite_cli_failures(tmp_path, field, value):
    spec = {"id": "oversized", "paths": [{"segments": [{"type": "straight", "run": 128}]}]}
    if field == "run":
        spec["paths"][0]["segments"][0][field] = value
    else:
        spec[field] = value
    path = tmp_path / "bad-catalogue.json"
    path.write_text(json.dumps({"pieces": [spec]}))
    result = CliRunner().invoke(main, ["pieces", "--catalog", str(path)])
    assert result.exit_code == 1
    assert "bad catalogue file" in result.output
    assert "Traceback" not in result.output
    assert not isinstance(result.exception, OverflowError)
