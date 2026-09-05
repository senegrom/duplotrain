from pathlib import Path
p = Path('pyproject.toml')
s = p.read_text()
s = s.replace('    "slow: long-running full enumerations (deselect with -m \'not slow\')",', '    "slow: long-running full enumerations (deselect with -m \'not slow\')",\n    "browser: real browser integration tests (requires playwright and browser binaries)",', 1)
p.write_text(s)
p = Path('.github/workflows/state-law-check.yml')
s = p.read_text()
s = s.replace('  workflow_dispatch:', '  pull_request:\n    paths:\n      - theory/lean/**\n      - .github/workflows/state-law-check.yml\n  workflow_dispatch:', 1)
p.write_text(s)
p = Path('tests/test_gui.py')
p.write_text(p.read_text() + '''

@pytest.mark.parametrize("coefficient", ["1e999999999", "1/0"])
def test_invalid_numeric_import_returns_json_and_preserves_state(server, coefficient):
    _, before = server("/api/attach", {"piece": "straight", "entry": 0, "at": None})
    _, data = server("/api/export")
    data["placements"][0]["frame"]["x"][0] = coefficient
    status, error = server("/api/import", {"data": data})
    assert status == 409
    assert "error" in error
    _, after = server("/api/state")
    assert before == after


def test_non_object_body_and_invalid_port_return_json(server):
    status, error = server("/api/inventory", [])
    assert status == 409
    assert "object" in error["error"]
    status, error = server("/api/attach", {"piece": "straight", "entry": -1, "at": None})
    assert status == 409
    assert "port" in error["error"]
''')
p = Path('README.md')
p.write_text(p.read_text() + '''

## Editor recovery and application checks

The editor automatically saves exact layout geometry, owned track and stone counts,
and sandbox mode in this browser's local storage. A fresh engine restores that session;
an already-running local server keeps its newer session. Storage is device/browser-local,
not a cloud backup. Export JSON for a portable copy of the layout. Storage or recovery
errors are shown without overwriting an unreadable checkpoint. Clear remains undoable
within the current session; undo history is not persisted across engine restarts.

On phones, the canvas sits above the scrolling controls. Drag to pan, pinch or use
+/− to zoom, and use the visible Remove tool to delete a stone or piece. Completion
cards require Preview before Apply. Inventory changes invalidate old suggestions.

Completion searches report whether the inventory was exhausted or a node, result or
piece limit stopped the search. The editor starts at 26 added pieces; Search deeper
increases that limit, up to 128. An unsuccessful capped search is not a proof that
no layout exists. Arc shortcuts and staged searches are explicitly non-exhaustive.

Run application checks locally:

```sh
python -m pip install -e '.[dev]'
ruff check src webapp
python -m pytest -m 'not slow and not browser'
node --test tests/web/*.test.cjs
# Browser integration, including the real Pyodide worker:
python -m pip install playwright
python -m playwright install chromium webkit
python webapp/build.py
DUPLOTRAIN_STATIC_DIST="$PWD/webapp/dist" python -m pytest tests/browser -m browser
DUPLOTRAIN_BROWSER=webkit DUPLOTRAIN_STATIC_DIST="$PWD/webapp/dist" python -m pytest tests/browser -m browser
```

Application CI runs these checks on pushes and pull requests, including a clean base
installation without matplotlib. The independent Lean workflow checks proof changes.
Package license metadata reads the repository's LICENSE file (GNU AGPL v3), rather
than declaring an inconsistent MIT license.
''')
