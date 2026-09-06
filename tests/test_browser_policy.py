"""Test skip/failure policy without needing a browser or Playwright installed.

Availability is decided by attempting the launch, not by probing
``executable_path``: that path names one build directory and playwright may
launch a different installed build, which silently skipped the whole browser
suite on machines where it passes.
"""

import builtins
import importlib.util
import sys
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock

import pytest

spec = importlib.util.spec_from_file_location(
    "browser_policy", Path(__file__).parent / "browser" / "conftest.py"
)
policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(policy)


@pytest.fixture()
def local_env(monkeypatch):
    for key in ("CI", "DUPLOTRAIN_REQUIRE_BROWSER", "DUPLOTRAIN_BROWSER_PATH"):
        monkeypatch.delenv(key, raising=False)


class FakePlaywrightError(Exception):
    """Stands in for playwright.sync_api.Error."""


def missing_executable(path):
    return FakePlaywrightError(
        f"BrowserType.launch: Executable doesn't exist at {path}"
    )


def browser_type(path, error=None):
    return SimpleNamespace(
        name="chromium", executable_path=str(path), launch=Mock(side_effect=error)
    )


@pytest.fixture(autouse=True)
def fake_playwright_error(monkeypatch):
    """launch_browser imports Error lazily; give it one we can raise."""
    module = SimpleNamespace(Error=FakePlaywrightError)
    monkeypatch.setitem(sys.modules, "playwright.sync_api", module)


def test_absent_default_browser_skips_locally(local_env, tmp_path):
    path = tmp_path / "missing"
    browser = browser_type(path, missing_executable(path))
    with pytest.raises(pytest.skip.Exception, match="not installed"):
        policy.launch_browser(browser)
    browser.launch.assert_called_once()


def test_reported_path_absent_but_browser_launches(local_env, tmp_path):
    """The regression: playwright reports a path it does not launch from."""
    browser = browser_type(tmp_path / "never-created")
    assert policy.launch_browser(browser) is browser.launch.return_value
    browser.launch.assert_called_once_with(headless=True)


@pytest.mark.parametrize("flag", ["CI", "DUPLOTRAIN_REQUIRE_BROWSER"])
def test_absent_browser_fails_in_ci(local_env, monkeypatch, tmp_path, flag):
    monkeypatch.setenv(flag, "1")
    path = tmp_path / "missing"
    browser = browser_type(path, missing_executable(path))
    with pytest.raises(FakePlaywrightError, match="Executable doesn't exist"):
        policy.launch_browser(browser)
    browser.launch.assert_called_once()


def test_explicit_bad_browser_path_is_not_skipped(local_env, monkeypatch, tmp_path):
    monkeypatch.setenv("DUPLOTRAIN_BROWSER_PATH", str(tmp_path / "explicit-missing"))
    browser = browser_type(tmp_path / "missing", RuntimeError("bad custom path"))
    with pytest.raises(RuntimeError, match="bad custom path"):
        policy.launch_browser(browser)


def test_unexpected_startup_failure_is_not_skipped(local_env, tmp_path):
    path = tmp_path / "installed"
    path.touch()
    browser = browser_type(path, RuntimeError("browser crashed"))
    with pytest.raises(RuntimeError, match="browser crashed"):
        policy.launch_browser(browser)


def test_installed_browser_is_launched(local_env, tmp_path):
    path = tmp_path / "installed"
    path.touch()
    browser = browser_type(path)
    assert policy.launch_browser(browser) is browser.launch.return_value
    browser.launch.assert_called_once_with(headless=True)


@pytest.mark.parametrize("ci", [False, True])
def test_missing_playwright_is_optional_only_locally(local_env, monkeypatch, ci):
    if ci:
        monkeypatch.setenv("DUPLOTRAIN_REQUIRE_BROWSER", "1")
    original_import = builtins.__import__

    def missing(name, *args, **kwargs):
        if name == "playwright.sync_api":
            raise ModuleNotFoundError("no playwright", name="playwright")
        return original_import(name, *args, **kwargs)

    monkeypatch.setattr(builtins, "__import__", missing)
    expected = ModuleNotFoundError if ci else pytest.skip.Exception
    with pytest.raises(expected):
        next(policy.browser.__wrapped__())
