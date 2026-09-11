"""Bases every fixture format builds on: input specs, emitted fixtures, type declarations."""

import hashlib
import json
import re
from abc import abstractmethod
from collections.abc import Mapping
from functools import cached_property
from typing import Any, ClassVar, Final, Self

from pydantic import BaseModel, ConfigDict, Field, computed_field, field_serializer
from pydantic.alias_generators import to_camel

from ssz.exceptions import SSZError, ValueFault
from ssz.ssz_base import SSZType


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
    """The case's authored identifier, unique across the run."""

    generated_by: str
    """Node id of the filler that produced the case, for a maintainer tracing it back."""

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

    @computed_field
    @property
    def valid(self) -> bool:
        """Whether a decoder must accept this vector's input, stated rather than inferred."""
        return self.rejection_reason is None

    @field_serializer("rejection_reason", when_used="json-unless-none")
    def serialize_rejection_reason(self, fault: ValueFault) -> str:
        """Emit the fault's name, its stable tag, rather than the sentence it renders."""
        return fault.name

    def with_info(self, info: FixtureInfo) -> Self:
        """Return a copy carrying the metadata envelope."""
        return self.model_copy(update={"info": info})

    def declared_types(self) -> "Mapping[str, TypeDescriptor]":
        """Every type name this fixture emits, against the declaration it has to stand for."""
        return {}

    @abstractmethod
    def case_type_name(self) -> str:
        """The declared type name this vector is about."""

    @abstractmethod
    def case_kind(self) -> str:
        """The SSZ kind the emitted tree files this vector under."""

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


_CAMEL_WORD_BREAK: Final = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
"""Where a CamelCase kind parts into words, leaving the digits of Uint8 attached."""


class TypeDescriptor(CamelModel):
    """An SSZ type declaration in the form a consumer rebuilds the type from."""

    model_config = CamelModel.model_config | {"extra": "forbid", "frozen": True}

    kind: str
    """The SSZ shape this declaration is one of."""

    bits: int | None = None
    """Width of an unsigned integer."""

    length: int | None = None
    """Exact element count of a vector, a bitvector or a byte vector."""

    limit: int | None = None
    """Maximum element count of a list, a bitlist or a byte list."""

    element_type: "TypeDescriptor | None" = None
    """Declaration of what a sequence holds."""

    active_fields: tuple[int, ...] | None = None
    """Layout of a progressive container, one bit per position, set where a field sits."""

    fields: "tuple[DeclaredField, ...] | None" = None
    """A container's fields, in the declaration order the wire format follows."""

    options: "tuple[DeclaredOption, ...] | None" = None
    """A union's options, each against the selector that names it."""

    @property
    def directory_name(self) -> str:
        """The kind this declaration states, spelled as a directory can hold it."""
        return _CAMEL_WORD_BREAK.sub("_", self.kind).lower()


class DeclaredField(CamelModel):
    """One field of a container, against the declaration of what it holds."""

    model_config = CamelModel.model_config | {"extra": "forbid", "frozen": True}

    name: str
    """The field's name, which the JSON value mapping keys it by."""

    type: TypeDescriptor
    """The field's declared type."""


class DeclaredOption(CamelModel):
    """One option of a union, against the selector byte that names it."""

    model_config = CamelModel.model_config | {"extra": "forbid", "frozen": True}

    selector: int
    """The selector byte an encoding of this option leads with."""

    type: TypeDescriptor
    """The option's declared type."""


TypeDescriptor.model_rebuild()

_TYPE_PARAMETERS: Final = ("BITS", "LENGTH", "LIMIT", "ELEMENT_TYPE", "ACTIVE_FIELDS", "OPTIONS")
"""Everything a declaration fixes its wire format and its tree with, beyond its fields."""


def _declared(parameter: Any) -> Any:
    """One type parameter as a descriptor carries it, a nested type recursing into its own."""
    if isinstance(parameter, type) and issubclass(parameter, SSZType):
        return describe_type(parameter)
    if isinstance(parameter, Mapping):
        return [
            DeclaredOption(selector=selector, type=describe_type(option))
            for selector, option in parameter.items()
        ]
    return parameter


def describe_type(ssz_type: type[SSZType]) -> TypeDescriptor:
    """The declaration a consumer rebuilds this type from, read off the class and nothing else."""
    kind = next(
        base.__name__
        for base in ssz_type.__mro__
        # A parametrized base names its element, which ELEMENT_TYPE below already writes out.
        if base.__module__.split(".")[0] == "ssz" and "[" not in base.__name__
    )
    declared: dict[str, Any] = {
        name.lower(): _declared(parameter)
        for name in _TYPE_PARAMETERS
        if (parameter := getattr(ssz_type, name, None)) is not None
    }
    if (field_types := getattr(ssz_type, "_FIELD_TYPES", None)) is not None:
        declared["fields"] = [
            DeclaredField(name=field_name, type=describe_type(field_type))
            for field_name, field_type in field_types
        ]
    return TypeDescriptor(kind=kind, **declared)
