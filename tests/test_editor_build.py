"""Shared frontend sources and one tested, unprivileged Pages build."""

import importlib.util
import re
import shutil
import tomllib
from pathlib import Path

import pytest

ROOT = Path(__file__).parents[1]
spec = importlib.util.spec_from_file_location("asset_build", ROOT / "webapp/build.py")
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)


@pytest.mark.parametrize("pages", [False, True])
def test_build_copies_external_sources_without_extracting_html(monkeypatch, tmp_path, pages):
    monkeypatch.setattr(build, "DIST", tmp_path)
    (tmp_path / "app.js").write_text("stale extracted script")
    build.build_index(meta_csp=pages)
    html = (tmp_path / "index.html").read_text()
    assert not (tmp_path / "app.js").exists()
    assert "<script>" not in html and "<style>" not in html
    assert html.index('src="./boot.js?v=__V__" defer') < html.index(
        'src="./editor.js?v=__V__" defer'
    )
    assert 'href="./editor.css?v=__V__"' in html
    assert ('http-equiv="Content-Security-Policy"' in html) == pages
    for name in (*build.EDITOR_SCRIPTS, "editor.css"):
        assert (tmp_path / name).read_bytes() == build.text_bytes(
            ROOT / "src/duplotrain/static" / name
        )


@pytest.fixture()
def synthetic_runtime_build(monkeypatch, tmp_path):
    # This is a stamp/asset test, not a dependency-verification substitute.
    # The separate build-security suite checks reviewed archive hashes and types.
    source = tmp_path / "source"
    shutil.copytree(ROOT / "src/duplotrain", source / "src/duplotrain",
                    ignore=shutil.ignore_patterns("__pycache__"))
    runtime = tmp_path / "runtime"
    runtime.mkdir()
    for name in build.PYODIDE_FILES:
        (runtime / name).write_bytes(b"synthetic test runtime")
    dist = tmp_path / "dist"
    monkeypatch.setattr(build, "ROOT", source)
    monkeypatch.setattr(build, "DIST", dist)
    monkeypatch.setattr(build, "fetch_pyodide", lambda _version: runtime)
    monkeypatch.setattr(build.sys, "argv", ["build.py", "--pages"])
    return source, dist


@pytest.mark.parametrize("name", [*build.EDITOR_SCRIPTS, "editor.css", "editor.html"])
def test_all_frontend_sources_change_the_stamp_and_rebuild_is_deterministic(
    synthetic_runtime_build, name,
):
    source, dist = synthetic_runtime_build
    build.main()
    before = {p.relative_to(dist): p.read_bytes() for p in dist.rglob("*") if p.is_file()}
    build.main()
    assert before == {p.relative_to(dist): p.read_bytes()
                      for p in dist.rglob("*") if p.is_file()}
    old = next(dist.glob("duplotrain-src-*.zip")).name
    asset = source / "src/duplotrain/static" / name
    asset.write_text(asset.read_text() + "\n")
    build.main()
    assert len(list(dist.glob("duplotrain-src-*.zip"))) == 1
    assert next(dist.glob("duplotrain-src-*.zip")).name != old
    assert "__V__" not in (dist / "index.html").read_text()


def test_local_and_built_editor_assets_are_in_package_data():
    project = tomllib.loads((ROOT / "pyproject.toml").read_text())
    patterns = project["tool"]["setuptools"]["package-data"]["duplotrain"]
    assert "static/*.js" in patterns and "static/*.css" in patterns
    extras = project["project"]["optional-dependencies"]
    assert any(dep.startswith("matplotlib") for dep in extras["test"])
    assert not any(dep.startswith(("matplotlib", "ruff")) for dep in extras["browser"])
    assert any(dep.startswith("playwright") for dep in extras["browser"])


def workflow_jobs():
    # Explicit job boundaries, rather than adding a YAML runtime dependency just
    # for this structural regression. GitHub validates the actual workflow syntax.
    text = (ROOT / ".github/workflows/app-check.yml").read_text()
    parts = re.split(r"^  ([\w-]+):\n", text.split("jobs:\n", 1)[1], flags=re.MULTILINE)
    return text, dict(zip(parts[1::2], parts[2::2], strict=True))


def test_ci_builds_once_tests_same_artifact_and_never_rebuilds_with_deploy_permissions():
    text, jobs = workflow_jobs()
    assert text.count("run: ruff check") == 1
    assert text.count("run: node --test") == 1
    assert text.count("run: python webapp/build.py") == 1
    assert "--pages" in jobs["build"]
    assert "pages: write" not in jobs["build"]
    assert "id-token: write" not in jobs["build"]
    assert "artifact_id: ${{ steps.bundle.outputs.artifact_id }}" in jobs["build"]
    assert "artifact-ids: ${{ needs.build.outputs.artifact_id }}" in jobs["browser"]
    assert "EXPECTED_SHA256: ${{ needs.build.outputs.sha256 }}" in jobs["browser"]
    assert "filter='data'" in jobs["browser"]
    deploy = jobs["deploy"]
    assert "needs: [quality, python, base-install, build, browser]" in deploy
    assert "github.event_name != 'pull_request' && github.ref == 'refs/heads/main'" in deploy
    assert "actions/checkout@" not in deploy and "run:" not in deploy
    assert "actions/deploy-pages@" in deploy
    assert "workflow_run:" not in text and "pull_request_target:" not in text


def test_ci_keeps_both_versions_both_browsers_and_minimal_install():
    _, jobs = workflow_jobs()
    assert "python: ['3.12', '3.13']" in jobs["python"]
    assert "browser: [chromium, webkit]" in jobs["browser"]
    assert "DUPLOTRAIN_REQUIRE_BROWSER: '1'" in jobs["browser"]
    assert 'not slow and not browser' in jobs["python"]
    assert 'find_spec(\'matplotlib\') is None' in jobs["base-install"]
    assert 'duplotrain solve' in jobs["base-install"]


def test_deferred_scripts_match_the_build_allowlist_and_single_snapshot_owner():
    from duplotrain.gui import _EDITOR_ASSETS

    static = ROOT / "src/duplotrain/static"
    html = (static / "editor.html").read_text()
    names = re.findall(r'<script src="\./([^"?]+)" defer></script>', html)
    assert tuple(names) == build.EDITOR_SCRIPTS
    assert all("/" + name in _EDITOR_ASSETS for name in names)
    sources = [(static / name).read_text() for name in names]
    assert sum(source.count("let S = null;") for source in sources) == 1
    assert sum(source.count('document.addEventListener("DOMContentLoaded"')
               for source in sources) == 1


def test_moving_bytes_between_frontend_files_changes_the_stamp(synthetic_runtime_build):
    source, dist = synthetic_runtime_build
    build.main()
    old = next(dist.glob("duplotrain-src-*.zip")).name
    static = source / "src/duplotrain/static"
    first, second = (static / name for name in build.EDITOR_SCRIPTS[:2])
    text = first.read_text()
    first.write_text(text[:-1])
    second.write_text(text[-1] + second.read_text())
    build.main()
    assert next(dist.glob("duplotrain-src-*.zip")).name != old
