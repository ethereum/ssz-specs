"""What the JSON mapping format emits, and what it refuses to call a passing test."""

import json
from typing import Any

import pytest

from ssz import Byte, CompatibleUnion, Container, List, Uint8, Uint16, Vector
from ssz.base import json_writer
from ssz_testing import JsonFault, JsonMappingTest
from ssz_testing.type_builder import build_declaration


class Pair(Container):
    """A two-field struct, the flattest shape the mapping writes as an object."""

    x: Uint16
    y: Uint16


class Numbers(List[Uint16]):
    """A bounded list, written as an array and refusing an array past its limit."""

    LIMIT = 4


class Digest(Vector[Byte]):
    """A byte-element vector, the shape whose kind decides hex against an array."""

    LENGTH = 2


class Either(CompatibleUnion):
    """A union of one option, the shape this implementation writes but cannot read."""

    OPTIONS = {1: Pair}


def test_a_written_document_carries_the_value_and_the_bytes_beside_it() -> None:
    """A vector states the JSON, the encoding of the same value, and the type behind both."""
    fixture = JsonMappingTest(
        type_name="Pair",
        ssz_type=Pair,
        value=Pair(x=Uint16(1), y=Uint16(2)),
        document={"x": "1", "y": "2"},
    ).generate()

    assert fixture.json_dict == {
        "typeName": "Pair",
        "document": {"x": "1", "y": "2"},
        "serialized": "0x01000200",
        "valid": True,
        "typeDescriptor": {
            "kind": "Container",
            "fields": [
                {"name": "x", "type": {"kind": "Uint16", "bits": 16}},
                {"name": "y", "type": {"kind": "Uint16", "bits": 16}},
            ],
        },
    }


def test_a_vector_is_indexed_by_the_type_name_and_the_kind_it_states() -> None:
    """A case is filed under its kind and claims its name, both read off the declaration."""
    fixture = JsonMappingTest(
        type_name="Pair",
        ssz_type=Pair,
        value=Pair(x=Uint16(1), y=Uint16(2)),
        document={"x": "1", "y": "2"},
    ).generate()

    assert fixture.case_type_name() == "Pair"
    assert fixture.case_kind() == "container"
    assert fixture.declared_types() == {"Pair": fixture.type_descriptor}


def test_a_union_document_is_written_and_the_read_recorded_as_unavailable() -> None:
    """A union renders a selector object, and no JSON reaches its option field to come back."""
    note = "a union declares its option as an is-instance field"
    fixture = JsonMappingTest(
        type_name="Either",
        ssz_type=Either,
        value=Either(selector=Uint8(1), data=Pair(x=Uint16(1), y=Uint16(2))),
        document={"selector": "1", "data": {"x": "1", "y": "2"}},
        not_read_back=note,
    ).generate()

    assert fixture.json_dict["document"] == {"selector": "1", "data": {"x": "1", "y": "2"}}
    assert fixture.json_dict["notReadBack"] == note
    assert fixture.json_dict["serialized"] == "0x0101000200"


def test_a_document_the_mapping_does_not_write_is_not_a_vector() -> None:
    """The document is authored, so a rendering the writer disagrees with fails the fill."""
    spec = JsonMappingTest(
        type_name="Pair",
        ssz_type=Pair,
        value=Pair(x=Uint16(1), y=Uint16(2)),
        document={"x": 1, "y": 2},
    )

    with pytest.raises(AssertionError, match="Pair is written as"):
        spec.generate()


def test_a_value_of_another_type_is_refused() -> None:
    """The declaration and the value have to be about one type, since the vector states one."""
    spec = JsonMappingTest(
        type_name="Pair",
        ssz_type=Pair,
        value=Uint16(1),
        document="1",
    )

    with pytest.raises(ValueError, match="Pair was handed a value of Uint16"):
        spec.generate()


def test_a_written_document_with_no_value_is_refused() -> None:
    """Nothing renders a document on its own, so a positive vector names the value it came from."""
    spec = JsonMappingTest(type_name="Pair", ssz_type=Pair, document={"x": "1", "y": "2"})

    with pytest.raises(ValueError, match="must state which value"):
        spec.generate()


def test_a_refused_document_carries_the_fault_and_no_bytes() -> None:
    """A document that renders no value emits the refusal alone, there being nothing to encode."""
    fixture = JsonMappingTest(
        type_name="Numbers",
        ssz_type=Numbers,
        document=["1", "2", "3", "4", "5"],
        rejection_reason=JsonFault.OVER_LIMIT,
        message_substring="holds at most 4 elements",
    ).generate()

    assert fixture.json_dict == {
        "typeName": "Numbers",
        "document": ["1", "2", "3", "4", "5"],
        "rejectionReason": "OVER_LIMIT",
        "valid": False,
        "typeDescriptor": {
            "kind": "List",
            "limit": 4,
            "elementType": {"kind": "Uint16", "bits": 16},
        },
    }


def test_a_document_the_type_accepts_is_not_a_refusal() -> None:
    """A negative vector has to be refused, or it pins the opposite of what it claims."""
    spec = JsonMappingTest(
        type_name="Numbers",
        ssz_type=Numbers,
        document=["1", "2"],
        rejection_reason=JsonFault.OVER_LIMIT,
    )

    with pytest.raises(AssertionError, match="but it parsed"):
        spec.generate()


def test_a_refusal_for_another_reason_is_not_a_vector() -> None:
    """The authored message pins which rule fired, a refusal alone naming no rule at all."""
    spec = JsonMappingTest(
        type_name="Numbers",
        ssz_type=Numbers,
        document=["1", "2", "3", "4", "5"],
        rejection_reason=JsonFault.OVER_LIMIT,
        message_substring="a delimiter bit",
    )

    with pytest.raises(AssertionError, match="for the wrong reason"):
        spec.generate()


def test_a_document_read_back_as_another_value_is_not_a_vector() -> None:
    """Both directions are checked, so a reader disagreeing with the writer fails the fill."""

    class OneWay(Container):
        """A struct whose reader is bypassed below, standing in for one that disagrees."""

        x: Uint16

    spec = JsonMappingTest(
        type_name="OneWay",
        ssz_type=OneWay,
        value=OneWay(x=Uint16(1)),
        document={"x": "1"},
        not_read_back="this type reads its own JSON back perfectly well",
    )

    with pytest.raises(AssertionError, match="now reads its own JSON back"):
        spec.generate()


@pytest.mark.parametrize(
    "value,document",
    [
        (Digest.of(0x11, 0x22), "0x1122"),
        (Numbers(data=[Uint16(1)]), ["1"]),
        (Pair(x=Uint16(1), y=Uint16(2)), {"x": "1", "y": "2"}),
    ],
    ids=["vector_of_bytes", "list", "container"],
)
def test_a_rebuilt_type_writes_the_same_document(value: Any, document: Any) -> None:
    """The descriptor is the whole contract, so the rebuilt type has to render alike."""
    emitted = JsonMappingTest(
        type_name=type(value).__name__, ssz_type=type(value), value=value, document=document
    ).generate()

    rebuilt = build_declaration(emitted.json_dict["typeDescriptor"], emitted.type_name)
    read_back = json_writer(rebuilt).validate_json(json.dumps(document))

    assert json.loads(json_writer(rebuilt).dump_json(read_back)) == document
