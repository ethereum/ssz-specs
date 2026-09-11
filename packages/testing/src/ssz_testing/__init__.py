"""Test tools for generating SSZ conformance test vectors."""

from typing import Protocol

from ssz.exceptions import TypeFault, ValueFault
from ssz.paths import PathStep
from ssz.ssz_base import SSZType
from ssz_testing.fixtures import (
    BaseTestSpec,
    DeclaredField,
    DeclaredOption,
    ExpectedRejection,
    TypeDescriptor,
    describe_type,
)
from ssz_testing.gindex_fixtures import (
    ELEMENT_COUNT_STEP,
    FIELD_LAYOUT_STEP,
    TYPE_SELECTOR_STEP,
    GindexFixture,
    GindexPathStep,
    GindexTest,
    MixedInWord,
    MixinStep,
)
from ssz_testing.proof_fixtures import (
    MultiproofFixture,
    MultiproofMutation,
    MultiproofTest,
    ProofFixture,
    ProofMutation,
    ProofTest,
)
from ssz_testing.serialization import SSZFixture, SSZTest
from ssz_testing.type_builder import build_declaration
from ssz_testing.type_rejections import TypeRejectionFixture, TypeRejectionTest


class SSZTestFiller(Protocol):
    """Type of the ssz_test fixture: builds, generates, and collects an SSZ vector."""

    # Spelled out rather than a callable of any arguments, so a bad call is a type error.
    def __call__(
        self,
        *,
        case_id: str,
        type_name: str,
        value: SSZType,
        raw_bytes: str | None = None,
        expected_rejection: ExpectedRejection | None = None,
    ) -> SSZFixture:
        """Build the spec from these fields, generate the vector, and collect it."""
        ...


class TypeRejectionFiller(Protocol):
    """Type of the ssz_type_rejection fixture: attempts an illegal declaration and collects it."""

    def __call__(
        self,
        *,
        case_id: str,
        type_name: str,
        type_descriptor: TypeDescriptor,
        rejection_reason: TypeFault,
        exact_message: str,
    ) -> TypeRejectionFixture:
        """Build the spec from these fields, generate the vector, and collect it."""
        ...


class GindexTestFiller(Protocol):
    """Type of the ssz_gindex_test fixture: builds, generates, and collects a gindex vector."""

    def __call__(
        self,
        *,
        case_id: str,
        type_name: str,
        ssz_type: type[SSZType],
        path: tuple[GindexPathStep, ...] = (),
        gindex: int | None = None,
        refusal: TypeFault | ValueFault | None = None,
    ) -> GindexFixture:
        """Build the spec from these fields, generate the vector, and collect it."""
        ...


class ProofTestFiller(Protocol):
    """Type of the proof_test fixture: builds, generates, and collects one Merkle branch."""

    def __call__(
        self,
        *,
        case_id: str,
        type_name: str,
        value: SSZType,
        path: tuple[PathStep, ...] = (),
        expected_index: int | None = None,
        mutation: ProofMutation | None = None,
        stricter_than_spec: str | None = None,
        expected_rejection: ExpectedRejection | None = None,
    ) -> ProofFixture:
        """Build the spec from these fields, generate the vector, and collect it."""
        ...


class MultiproofTestFiller(Protocol):
    """Type of the multiproof_test fixture: builds, generates, and collects one multiproof."""

    def __call__(
        self,
        *,
        case_id: str,
        type_name: str,
        value: SSZType,
        paths: tuple[tuple[PathStep, ...], ...],
        expected_indices: tuple[int, ...] | None = None,
        expected_helper_indices: tuple[int, ...] | None = None,
        mutation: MultiproofMutation | None = None,
        stricter_than_spec: str | None = None,
        expected_rejection: ExpectedRejection | None = None,
    ) -> MultiproofFixture:
        """Build the spec from these fields, generate the vector, and collect it."""
        ...


FIXTURE_FORMATS: tuple[type[BaseTestSpec], ...] = (
    SSZTest,
    TypeRejectionTest,
    GindexTest,
    ProofTest,
    MultiproofTest,
)


__all__ = [
    "ELEMENT_COUNT_STEP",
    "FIELD_LAYOUT_STEP",
    "FIXTURE_FORMATS",
    "TYPE_SELECTOR_STEP",
    "DeclaredField",
    "DeclaredOption",
    "ExpectedRejection",
    "GindexFixture",
    "GindexPathStep",
    "GindexTest",
    "GindexTestFiller",
    "MixedInWord",
    "MixinStep",
    "MultiproofFixture",
    "MultiproofMutation",
    "MultiproofTest",
    "MultiproofTestFiller",
    "ProofFixture",
    "ProofMutation",
    "ProofTest",
    "ProofTestFiller",
    "SSZFixture",
    "SSZTest",
    "SSZTestFiller",
    "TypeDescriptor",
    "TypeFault",
    "TypeRejectionFiller",
    "TypeRejectionFixture",
    "TypeRejectionTest",
    "ValueFault",
    "build_declaration",
    "describe_type",
]
