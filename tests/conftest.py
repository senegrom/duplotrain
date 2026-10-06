"""Fixtures shared by the test modules."""

import pytest

from duplotrain.catalog import default_catalog


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()
