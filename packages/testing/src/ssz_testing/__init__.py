"""Test tools for generating SSZ conformance test vectors."""

from collections.abc import Callable

from ssz.exceptions import ValueFault
from ssz_testing.fixtures import (
    FIXTURE_FORMATS,
    ExpectedRejection,
    SSZFixture,
    SSZTest,
)

SSZTestFiller = Callable[..., SSZFixture]
"""Type of the ssz_test fixture: builds, generates, and collects an SSZ vector."""

__all__ = [
    "FIXTURE_FORMATS",
    "ExpectedRejection",
    "SSZFixture",
    "SSZTest",
    "SSZTestFiller",
    "ValueFault",
]
