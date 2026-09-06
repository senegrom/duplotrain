"""Local missing-browser skips must not turn CI failures into green checks."""

import os

import pytest


def required_browser() -> bool:
    return bool(os.environ.get("CI")) or os.environ.get("DUPLOTRAIN_REQUIRE_BROWSER") == "1"


def launch_browser(browser_type):
    """Launch, or skip only when the browser is genuinely not downloaded.

    ``browser_type.executable_path`` names one build directory and is not a
    reliable presence test: playwright may launch a different installed build,
    so probing that path skipped browser tests on machines where they pass.
    """
    from playwright.sync_api import Error  # only reached once playwright imported

    executable = os.environ.get("DUPLOTRAIN_BROWSER_PATH")
    kwargs = {"headless": True}
    if executable:
        kwargs["executable_path"] = executable
    try:
        return browser_type.launch(**kwargs)
    except Error as exc:
        # Unexpected startup errors (crashes, missing OS libraries) still fail.
        if required_browser() or "Executable doesn't exist" not in str(exc):
            raise
        pytest.skip(f"{browser_type.name} not installed; run python -m playwright install")


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
