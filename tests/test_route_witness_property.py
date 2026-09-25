"""Keep upstream witness priority and identify the failed universal property."""
import json
from pathlib import Path

from duplotrain.catalog import default_catalog
from duplotrain.drive import classify, drive
from duplotrain.editor import Session
from duplotrain.editor_routes import RouteJob
from duplotrain.layout import layout_from_dict


def test_counterexample_property_matches_ordinary_classifier_on_bridge_gap():
    data = json.loads((Path(__file__).parent / "fixtures/bridge-gap.json").read_text())
    layout = layout_from_dict(data, default_catalog())
    job = RouteJob(Session(history=[layout]), {"max_runs": 10000})
    while job.status == "running":
        job.tick()
    response = job.response()
    assert response["complete"]
    assert response["counterexample_property"] == "looping"
    witness = response["counterexample"]
    ordinary = classify(layout, max_runs=10000).counterexample
    assert tuple(witness["start"]) == ordinary[0]
    assert witness["switch_states"] == ordinary[1]
    assert witness["outcome"] == ordinary[2] == "derailed"
    assert drive(layout, start=tuple(witness["start"]),
                 switch_states=witness["switch_states"]).outcome == "derailed"


def test_priority_label_tracks_known_failure_without_universal_claim():
    data = json.loads((Path(__file__).parent / "fixtures/bridge-gap.json").read_text())
    job = RouteJob(Session(history=[layout_from_dict(data, default_catalog())]), {})
    assert job.response()["counterexample_property"] is None
    for key in ("perfectly", "completely", "looping"):
        witness = {"start": [0, 0], "outcome": "endless", "property_for_test": key}
        job.failures[key] = witness
        response = job.response()
        assert response["counterexample_property"] == key
        assert response["counterexample"] is witness
        assert response["classification"] is None
        assert not response["complete"]
    job.close()
