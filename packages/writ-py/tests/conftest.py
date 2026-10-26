from __future__ import annotations

from collections.abc import Callable

import pytest

from writ import Kernel, MemoryStore, Store, load_kernel


@pytest.fixture(scope="session")
def kernel() -> Kernel:
    return load_kernel()


@pytest.fixture(params=[MemoryStore], ids=["MemoryStore"])
def make(request: pytest.FixtureRequest) -> Callable[[], Store]:
    """The store under test: the store and gate suites run against each store listed here."""
    factory: Callable[[], Store] = request.param
    return factory
