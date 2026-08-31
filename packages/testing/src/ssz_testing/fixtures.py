"""Fixture formats for SSZ conformance test vectors: input specs and emitted fixtures."""

import hashlib
import json
from abc import abstractmethod
from functools import cached_property
from typing import Any, ClassVar, Self

from pydantic import BaseModel, ConfigDict, Field, field_serializer
from pydantic.alias_generators import to_camel

from ssz.boolean import Boolean
from ssz.exceptions import SSZError, ValueFault
from ssz.roots import hash_tree_root
from ssz.ssz_base import SSZModel, SSZType
from ssz_testing.hex_codec import from_hex, to_hex


class CamelModel(BaseModel):
    """Base model that serializes field names as camelCase for cross-client vectors."""

    model_config = ConfigDict(
        alias_generator=to_camel,
        populate_by_name=True,
        validate_default=True,
        arbitrary_types_allowed=True,
    )

    def to_json(self, **kwargs: Any) -> dict[str, Any]:
        """
        Serialize to a JSON-encodable dict with camelCase keys.

        Serialization mode is pinned to JSON.
        Alias style is pinned to camelCase.
        A caller that overrides either almost certainly expects the override to apply.
        The override is rejected to avoid silently surprising the caller.

        Raises:
            TypeError: If mode or by_alias is passed as a keyword argument.
        """
        if "mode" in kwargs or "by_alias" in kwargs:
            raise TypeError(
                "to_json() does not accept 'mode' or 'by_alias'; "
                "mode is pinned to 'json' and by_alias to True"
            )

        return self.model_dump(
            mode="json",
            by_alias=True,
            **kwargs,
        )


class FixtureInfo(CamelModel):
    """Metadata envelope emitted alongside every fixture."""

    model_config = CamelModel.model_config | {"extra": "forbid", "frozen": True, "strict": True}

    comment: str = "`ssz-specs` generated test"
    """Provenance note for consumers."""

    test_id: str
    """Unique identifier for the test case."""

    description: str
    """Human-readable description of the test."""

    fixture_format: str
    """Name of the fixture format that produced this vector."""


class ExpectedRejection(CamelModel):
    """
    Author-side expectation that an input must be rejected.

    The fault names which refusal has to fire, and its name is what the vector emits.
    """

    model_config = CamelModel.model_config | {"extra": "forbid", "frozen": True, "strict": True}

    reason: ValueFault
    """The fault the decoder must raise on this input."""

    message_substring: str | None = None
    """
    Substring the raised exception message must contain.

    When None, any exception is accepted.
    Fill-time self-check only; never serialized into vectors.
    """

    exact_message: str | None = None
    """
    Full exception message the rejection must equal.

    When set, the raised message must equal this string exactly.
    Fill-time self-check only; never serialized into vectors.
    """

    def assert_message_matches(self, exception: Exception, context: str) -> None:
        """
        Check the raised message against the authored expectation.

        The exact match takes precedence over the substring when both are set.

        Args:
            exception: The exception the negative path raised.
            context: Caller label woven into the failure message.

        Raises:
            AssertionError: When the message contradicts the expectation.
        """
        actual_message = str(exception)
        if self.exact_message is not None and actual_message != self.exact_message:
            raise AssertionError(
                f"{context} failed with wrong error message.\n"
                f"  Expected exact message: {self.exact_message!r}\n"
                f"  Actual message: {actual_message!r}"
            )
        if self.message_substring is not None and self.message_substring not in actual_message:
            raise AssertionError(
                f"{context} failed with wrong error message.\n"
                f"  Expected message containing: {self.message_substring!r}\n"
                f"  Actual message: {actual_message!r}"
            )


class BaseConsensusFixture(CamelModel):
    """
    Base for every emitted fixture.

    A fixture is the frozen, serializable result of generating a test.
    Input specs produce one; nothing mutates it afterwards.
    """

    model_config = CamelModel.model_config | {"frozen": True}

    format_name: ClassVar[str] = ""
    """The name of this fixture format (e.g., 'ssz_test')."""

    info: FixtureInfo | None = Field(default=None, exclude=True)
    """Metadata about the test (description, format, etc.)."""

    rejection_reason: ValueFault | None = None
    """The fault a negative vector's input is rejected with, and the field clients assert on."""

    @field_serializer("rejection_reason", when_used="json-unless-none")
    def serialize_rejection_reason(self, fault: ValueFault) -> str:
        """Emit the fault's name, its stable tag, rather than the sentence it renders."""
        return fault.name

    def with_info(self, info: FixtureInfo) -> Self:
        """Return a copy carrying the metadata envelope."""
        return self.model_copy(update={"info": info})

    @cached_property
    def json_dict(self) -> dict[str, Any]:
        """JSON representation of the fixture, excluding the metadata envelope."""
        return self.to_json(exclude_none=True)

    @cached_property
    def hash(self) -> str:
        """Deterministic hash of the fixture, computed from its JSON representation."""
        json_str = json.dumps(
            self.json_dict,
            sort_keys=True,
            separators=(",", ":"),
        )
        fixture_digest = hashlib.sha256(json_str.encode("utf-8")).hexdigest()
        return f"0x{fixture_digest}"

    def json_dict_with_info(self) -> dict[str, Any]:
        """
        Return the JSON representation with the metadata envelope included.

        Raises:
            AssertionError: When the metadata envelope was never attached.
        """
        assert self.info is not None, "fixture is missing its metadata envelope"
        dict_with_info = self.json_dict.copy()
        dict_with_info["_info"] = {"hash": self.hash, **self.info.to_json()}
        return dict_with_info


class BaseTestSpec(CamelModel):
    """
    Base for author-facing test input specs.

    A spec is the frozen description a test author writes.
    Generating it runs the spec code and returns a separate fixture object.
    """

    model_config = CamelModel.model_config | {"frozen": True}

    format_name: ClassVar[str] = ""
    """The name of this fixture format (e.g., 'ssz_test')."""

    description: ClassVar[str] = "Unknown fixture format"
    """Human-readable description of what this fixture tests."""

    expected_rejection: ExpectedRejection | None = None
    """
    Expected rejection for invalid tests.

    If set, the input must be rejected during processing.
    Never serialized: the emitted contract is the fixture's reason field.
    """

    @abstractmethod
    def generate(self) -> BaseConsensusFixture:
        """
        Run the spec code and return the emitted fixture.

        Raises:
            AssertionError: If processing disagrees with the authored expectations.
        """

    def assert_expected_outcome(self, exception_raised: Exception | None) -> None:
        """
        Compare a self-verification outcome against the configured expectation.

        Args:
            exception_raised: The exception the verifier raised, or None on success.

        Raises:
            AssertionError: When the outcome disagrees with the expectation.
        """
        # No expectation means the input is honest and must process cleanly.
        if self.expected_rejection is None:
            if exception_raised is not None:
                raise AssertionError(f"Verifier rejected an honest input: {exception_raised}")
            return

        # An expectation that produced no exception means the flaw went undetected.
        if exception_raised is None:
            raise AssertionError(
                f"Expected rejection {self.expected_rejection.reason} but processing succeeded"
            )

        # A wrong message means the rejection fired for the wrong reason.
        self.expected_rejection.assert_message_matches(exception_raised, "Verifier")

    def assert_decode_rejection(
        self,
        exception_raised: SSZError[Any] | None,
        decoder_name: str,
    ) -> ValueFault:
        """
        Check a decode-failure outcome, and resolve the fault the vector emits.

        Args:
            exception_raised: The refusal the decoder raised, or None on success.
            decoder_name: Decoder label for failure messages.

        Returns:
            The fault emitted into the test vector.

        Raises:
            ValueError: When the authored expectation is missing.
            AssertionError: When decoding succeeds, or refuses for another reason.
        """
        if self.expected_rejection is None:
            raise ValueError("decode-failure vectors require expected_rejection to be set")
        if exception_raised is None:
            raise AssertionError(
                f"Expected {decoder_name} to reject the input, but decoding succeeded"
            )
        self.assert_expected_outcome(exception_raised)

        expected = self.expected_rejection.reason
        if exception_raised.fault is not expected:
            raise AssertionError(
                f"{decoder_name} refused for the wrong reason.\n"
                f"  Expected fault: {expected.name}\n"
                f"  Actual fault: {exception_raised.fault.name}"
            )

        # Past that check the authored member is the raised one, so this emits the fault that fired.
        return expected


class SSZFixture(BaseConsensusFixture):
    """Emitted vector for SSZ conformance."""

    format_name: ClassVar[str] = "ssz_test"

    type_name: str
    """SSZ type class name."""

    value: SSZType
    """The SSZ value under test."""

    raw_bytes: str | None = None
    """Hex malformed input, present in decode-failure mode only."""

    serialized: str
    """Hex SSZ bytes, or the malformed input verbatim on decode failure."""

    root: str
    """Hex tree root, empty in decode-failure mode."""

    @field_serializer("value", when_used="json")
    def serialize_value(self, ssz_value: SSZType) -> Any:
        """Convert an SSZ value to a JSON-safe representation."""
        # Collections and containers carry their contents in Pydantic fields.
        if isinstance(ssz_value, SSZModel):
            return ssz_value.model_dump(mode="json")
        # A boolean carries JSON true or false, not the string the fallback would give.
        if isinstance(ssz_value, Boolean):
            return bool(ssz_value)
        if isinstance(ssz_value, bytes):
            return to_hex(ssz_value)
        return str(ssz_value)


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
        """Verify SSZ roundtrip or decode-failure and produce the reference output."""
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

        root = hash_tree_root(self.value)

        return SSZFixture(
            type_name=self.type_name,
            value=self.value,
            raw_bytes=self.raw_bytes,
            serialized=to_hex(ssz_bytes),
            root=to_hex(root),
        )

    def _generate_decode_failure(self) -> SSZFixture:
        """
        Assert decoding the malformed bytes raises.

        The bytes are emitted verbatim so consumers can reproduce the rejected input.
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
            value=self.value,
            raw_bytes=self.raw_bytes,
            serialized=to_hex(raw),
            root="",
            rejection_reason=self.assert_decode_rejection(
                exception_raised, f"{decoder.__name__}.decode_bytes"
            ),
        )


FIXTURE_FORMATS: tuple[type[BaseTestSpec], ...] = (SSZTest,)
"""Canonical registry of every SSZ fixture format; add a class here to make it fillable."""
