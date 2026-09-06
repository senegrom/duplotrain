"""Local missing-browser skips must not turn CI failures into green checks."""

import os
from pathlib import Path

import pytest


def required_browser() -> bool:
    return bool(os.environ.get("CI")) or os.environ.get("DUPLOTRAIN_REQUIRE_BROWSER") == "1"


def launch_browser(browser_type):
    executable = os.environ.get("DUPLOTRAIN_BROWSER_PATH")
    if (not executable and not required_browser()
            and not Path(browser_type.executable_path).is_file()):
        pytest.skip(f"{browser_type.name} not installed; run python -m playwright install")
    kwargs = {"headless": True}
    if executable:
        kwargs["executable_path"] = executable
    # Unexpected startup errors (crashes, missing OS libraries, bad paths) fail.
    return browser_type.launch(**kwargs)


@pytest.fixture(scope="module")
def browser():
    try:
        from playwright.sync_api import sync_playwright
    except ModuleNotFoundError as exc:
        if required_browser() or exc.name not in {"playwright", "playwright.sync_api"}:
            raise
        pytest.skip("playwright is not installed")
    with sync_playwright() as manager:
        name = os.environ.get("DUPLOTRAIN_BROWSER", "chromium")
        instance = launch_browser(getattr(manager, name))
        try:
            yield instance
        finally:
            instance.close()
