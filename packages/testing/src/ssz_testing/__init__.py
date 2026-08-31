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

    # Spelled out rather than left as a callable of any arguments, so that a misspelled
    # keyword or a missing one is a type error at the call site rather than at fill time.
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
