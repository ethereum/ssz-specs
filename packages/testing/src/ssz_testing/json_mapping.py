"""Fixture format for the canonical JSON mapping: the document a value is written as."""

import json
from collections.abc import Mapping
from enum import Enum
from typing import Any, ClassVar

from pydantic import Field, ValidationError, computed_field

from ssz.base import json_writer
from ssz.ssz_base import SSZType
from ssz_testing.fixtures import (
    BaseConsensusFixture,
    BaseTestSpec,
    TypeDescriptor,
    describe_type,
)
from ssz_testing.hex_codec import to_hex


class JsonFault(Enum):
    """Every way a JSON document fails to be a rendering of the type it is read against."""

    HEX_PREFIX = "a hex byte string opens with 0x"
    BITFIELD_PADDING = "a bitfield sets a bit past the length its type declares"
    OVER_LIMIT = "a collection holds more elements than its type admits"
    UNDECLARED_FIELD = "an object names a field its struct does not declare"


class JsonMappingFixture(BaseConsensusFixture):
    """Emitted vector for one JSON document, either the rendering of a value or a refusal."""

    format_name: ClassVar[str] = "ssz_json_test"

    type_name: str
    """SSZ type class name."""

    ssz_type: type[SSZType] = Field(exclude=True)
    """The declaration the document is read against, which the type name has to stand for."""

    document: Any
    """The JSON the mapping assigns the value, or the input a parser must refuse."""

    serialized: str | None = None
    """Hex encoding of the same value, absent on a document that renders no value."""

    not_read_back: str | None = None
    """Why this implementation only wrote the document, absent wherever it also read one."""

    rejection_reason: JsonFault | None = None
    """The fault a parser must refuse this document with, and the field clients assert on."""

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


class JsonMappingTest(BaseTestSpec):
    """Spec for one JSON document, checked against the value it renders or the fault it draws."""

    format_name: ClassVar[str] = "ssz_json_test"
    description: ClassVar[str] = "Tests the canonical JSON mapping of an SSZ type"

    type_name: str
    """SSZ type class name."""

    ssz_type: type[SSZType]
    """The declaration the document is read against."""

    document: Any
    """The JSON under test, authored rather than derived, so the vector states a rendering."""

    value: SSZType | None = None
    """The value the document renders, required unless the document is refused."""

    rejection_reason: JsonFault | None = None
    """The fault the document must be refused with, and the field the vector emits."""

    message_substring: str | None = None
    """Substring the refusal must contain, a fill-time self-check never carried into a vector."""

    not_read_back: str | None = None
    """Why the read direction is unavailable here, which the fill then requires to stay so."""

    def generate(self) -> JsonMappingFixture:
        """Write the value, read the document back, and emit the vector, or check a refusal."""
        if self.rejection_reason is not None:
            return self._generate_refusal(self.rejection_reason)
        if self.value is None:
            raise ValueError("a document that renders a value must state which value")
        if not isinstance(self.value, self.ssz_type):
            raise ValueError(f"{self.type_name} was handed a value of {type(self.value).__name__}")

        mapping = json_writer(self.ssz_type)
        written = json.loads(mapping.dump_json(self.value))
        assert written == self.document, (
            f"{self.type_name} is written as {json.dumps(written)}, "
            f"and the vector states {json.dumps(self.document)}"
        )

        if self.not_read_back is None:
            read_back = mapping.validate_json(json.dumps(self.document))
            assert read_back == self.value, (
                f"{self.type_name} reads {json.dumps(self.document)} back as {read_back}, "
                f"and the vector states {self.value}"
            )
        else:
            self._require_the_read_stays_unavailable(mapping)

        return JsonMappingFixture(
            type_name=self.type_name,
            ssz_type=self.ssz_type,
            document=self.document,
            serialized=to_hex(self.value.encode_bytes()),
            not_read_back=self.not_read_back,
        )

    def _require_the_read_stays_unavailable(self, mapping: Any) -> None:
        """
        Hold a vector to its own note, so a read that starts working turns the fill red.

        Raises:
            AssertionError: When the document this vector calls unreadable now reads back.
        """
        try:
            mapping.validate_json(json.dumps(self.document))
        except ValidationError:
            return
        raise AssertionError(
            f"{self.type_name} now reads its own JSON back, so the vector's note is stale: "
            f"{self.not_read_back}"
        )

    def _generate_refusal(self, fault: JsonFault) -> JsonMappingFixture:
        """
        Assert parsing the document raises, and emit the type, that document and the fault.

        Raises:
            AssertionError: When the document parses, or is refused with another message.
        """
        refusal: ValidationError | None = None
        try:
            # Only a validation error is a vector; anything else is a bug, and crashes the fill.
            json_writer(self.ssz_type).validate_json(json.dumps(self.document))
        except ValidationError as exception:
            refusal = exception

        if refusal is None:
            raise AssertionError(
                f"Expected {self.type_name} to refuse {json.dumps(self.document)}, but it parsed"
            )
        if self.message_substring is not None and self.message_substring not in str(refusal):
            raise AssertionError(
                f"{self.type_name} refused {json.dumps(self.document)} for the wrong reason.\n"
                f"  Expected message containing: {self.message_substring!r}\n"
                f"  Actual message: {str(refusal)!r}"
            )

        return JsonMappingFixture(
            type_name=self.type_name,
            ssz_type=self.ssz_type,
            document=self.document,
            rejection_reason=fault,
        )
