"""Test tools for generating SSZ conformance test vectors."""

from typing import Protocol

from ssz.exceptions import ValueFault
from ssz.ssz_base import SSZType
from ssz_testing.fixtures import (
    FIXTURE_FORMATS,
    ExpectedRejection,
    SSZFixture,
    SSZTest,
)


class SSZTestFiller(Protocol):
    """Type of the ssz_test fixture: builds, generates, and collects an SSZ vector."""

    # Spelled out rather than a callable of any arguments, so a bad call is a type error.
    def __call__(
        self,
        *,
        type_name: str,
        value: SSZType,
        raw_bytes: str | None = None,
        expected_rejection: ExpectedRejection | None = None,
    ) -> SSZFixture:
        """Build the spec from these fields, generate the vector, and collect it."""
        ...


__all__ = [
    "FIXTURE_FORMATS",
    "ExpectedRejection",
    "SSZFixture",
    "SSZTest",
    "SSZTestFiller",
    "ValueFault",
]
