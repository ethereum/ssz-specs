"""Fixture format for SSZ serialization: a value round-tripped, or bytes a decoder must refuse."""

from collections.abc import Mapping
from typing import Any, ClassVar

from pydantic import Field, computed_field, field_serializer

from ssz.base import json_writer
from ssz.exceptions import SSZError
from ssz.roots import hash_tree_root
from ssz.ssz_base import SSZType
from ssz_testing.fixtures import (
    BaseConsensusFixture,
    BaseTestSpec,
    TypeDescriptor,
    describe_type,
)
from ssz_testing.hex_codec import from_hex, to_hex


class SSZFixture(BaseConsensusFixture):
    """Emitted vector for SSZ conformance."""

    format_name: ClassVar[str] = "ssz_test"

    type_name: str
    """SSZ type class name."""

    ssz_type: type[SSZType] = Field(exclude=True)
    """The declaration the vector is about, which the type name has to stand for."""

    serialized: str
    """Hex bytes handed to the decoder: the encoding of the value, or the input it must refuse."""

    value: SSZType | None = None
    """The SSZ value under test, absent on a vector whose bytes decode to no value."""

    root: str | None = None
    """Hex tree root, absent on a vector whose bytes decode to no value."""

    @field_serializer("value", when_used="json-unless-none")
    def serialize_value(self, ssz_value: SSZType) -> Any:
        """Render the value as the SSZ JSON mapping of its own type spells it."""
        return json_writer(type(ssz_value)).dump_python(ssz_value, mode="json")

    @computed_field
    @property
    def type_descriptor(self) -> TypeDescriptor:
        """The declaration of that type, read off the class so no vector can misstate it."""
        return describe_type(self.ssz_type)

    def declared_types(self) -> Mapping[str, TypeDescriptor]:
        """The one name this vector emits, against the declaration it was filled from."""
        return {self.type_name: self.type_descriptor}

    def case_type_name(self) -> str:
        """The declared type name this vector is about."""
        return self.type_name

    def case_kind(self) -> str:
        """The kind the declaration already states, spelled as a directory can hold it."""
        return self.type_descriptor.directory_name


class SSZTest(BaseTestSpec):
    """Spec for SSZ conformance, running either a roundtrip or a decode-failure check."""

    format_name: ClassVar[str] = "ssz_test"
    description: ClassVar[str] = "Tests SSZ serialization roundtrip and hash_tree_root"

    type_name: str
    """SSZ type class name."""

    value: SSZType
    """
    The SSZ value under test.

    In decode-failure mode only its class matters, since the class supplies the decoder.
    """

    raw_bytes: str | None = None
    """Hex malformed input, consulted only in decode-failure mode."""

    def generate(self) -> SSZFixture:
        """Verify SSZ roundtrip and re-encoding, or decode-failure, and produce the output."""
        if self.expected_rejection is not None:
            return self._generate_decode_failure()

        ssz_bytes = self.value.encode_bytes()
        decoded = self.value.decode_bytes(ssz_bytes)

        assert decoded == self.value, (
            f"SSZ roundtrip failed for {self.type_name}: "
            f"original != decoded\n"
            f"Original: {self.value}\n"
            f"Decoded: {decoded}"
        )

        # Re-encoding an accepted value must reproduce its bytes, or one value has two encodings.
        reencoded = decoded.encode_bytes()
        assert reencoded == ssz_bytes, (
            f"SSZ encoding is not canonical for {self.type_name}: "
            f"re-encoding the decoded value gave other bytes\n"
            f"Encoded: {to_hex(ssz_bytes)}\n"
            f"Re-encoded: {to_hex(reencoded)}"
        )

        root = hash_tree_root(self.value)

        return SSZFixture(
            type_name=self.type_name,
            ssz_type=type(self.value),
            serialized=to_hex(ssz_bytes),
            value=self.value,
            root=to_hex(root),
        )

    def _generate_decode_failure(self) -> SSZFixture:
        """
        Assert decoding the malformed bytes raises, and emit the type, those bytes and the fault.

        Nothing decoded, so the vector carries no value and no root to compare against.
        """
        if self.raw_bytes is None:
            raise ValueError("raw_bytes is required when expected_rejection is set")

        raw = from_hex(self.raw_bytes)
        decoder = type(self.value)
        exception_raised: SSZError[Any] | None = None
        try:
            decoder.decode_bytes(raw)
        # Only an SSZ refusal is a vector; anything else is a bug, and crashes the fill.
        except SSZError as exception:
            exception_raised = exception

        return SSZFixture(
            type_name=self.type_name,
            ssz_type=decoder,
            serialized=to_hex(raw),
            rejection_reason=self.assert_decode_rejection(
                exception_raised, f"{decoder.__name__}.decode_bytes"
            ),
        )
