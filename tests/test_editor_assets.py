"""The local editor serves exactly its allowlisted icon and manifest assets."""

import http.client
import json
import re
from importlib import resources

import pytest

from duplotrain.gui import _EDITOR_ASSETS, Session
from tests.editor_support import running_server


@pytest.fixture()
def editor_port():
    with running_server(Session()) as server:
        yield server.server_port


def get(port, path):
    conn = http.client.HTTPConnection("127.0.0.1", port, timeout=3)
    try:
        conn.request("GET", path)
        response = conn.getresponse()
        return response.status, dict(response.getheaders()), response.read()
    finally:
        conn.close()


def packaged(path):
    return resources.files("duplotrain").joinpath("static" + path).read_bytes()


@pytest.mark.parametrize("path", sorted(_EDITOR_ASSETS))
def test_every_allowlisted_asset_is_served_verbatim(editor_port, path):
    status, headers, body = get(editor_port, path + "?v=1")
    assert status == 200
    assert headers["Content-Type"] == _EDITOR_ASSETS[path]
    assert headers["X-Content-Type-Options"] == "nosniff"
    assert body and body == packaged(path)


def test_editor_html_and_manifest_reference_only_allowlisted_assets():
    # docs/icons.md: bump the revision in the HTML, manifest and allowlist together.
    html = packaged("/editor.html").decode("utf-8")
    referenced = set(re.findall(r'<(?:link[^>]*href|script[^>]*src)="\./([^"]+)"', html))
    assert "manifest.webmanifest" in referenced
    manifest = json.loads(packaged("/manifest.webmanifest"))
    referenced.update(icon["src"].removeprefix("./") for icon in manifest["icons"])
    assert len(referenced) >= 10
    assert all("/" + name in _EDITOR_ASSETS for name in referenced)
    # The conventional discovery names are aliases of the versioned files.
    assert packaged("/favicon.ico") == packaged("/icons/duplotrain-favicon-v1.ico")
    assert packaged("/apple-touch-icon.png") == packaged("/icons/duplotrain-apple-180-v1.png")


@pytest.mark.parametrize("path", [
    "/icons/../editor.html", "/static/editor.html", "/icons/duplotrain-app-192-v1.png/",
    "/ICONS/duplotrain-app-192-v1.png", "/icons/duplotrain-app-192-v2.png",
    "/duplotrain-icon.svg.bak", "/pyproject.toml", "/icons/duplotrain-app-192-v1.png/..",
    "/icons/", "/icons",
])
def test_paths_outside_the_allowlist_are_refused_without_touching_the_filesystem(
    editor_port, path,
):
    status, headers, body = get(editor_port, path)
    assert status == 404
    assert headers["Content-Type"] == "application/json"
    assert "error" in json.loads(body)
