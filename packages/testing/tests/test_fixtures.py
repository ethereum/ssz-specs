"""What a fixture format emits, and what it refuses to call a passing test."""

import json

import pytest

from ssz import (
    Boolean,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    Uint8,
    ValueFault,
)
from ssz_testing.fixtures import (
    BaseConsensusFixture,
    CamelModel,
    ExpectedRejection,
    FixtureInfo,
    SSZFixture,
    SSZTest,
    describe_type,
)
from ssz_testing.hex_codec import from_hex, to_hex


class Bytes2(ByteVector):
    """A two-byte string, for the byte branch of the value serializer."""

    LENGTH = 2


class Pair(Container):
    """A struct, for the model branch of the value serializer."""

    number: Uint8
    flag: Boolean


class Bytes2Again(ByteVector):
    """The same two-byte string under another class name."""

    LENGTH = 2


class Bytes3(ByteVector):
    """A byte longer, so a different shape."""

    LENGTH = 3


class Swapped(Container):
    """The fields of Pair in the other order, so a different shape."""

    flag: Boolean
    number: Uint8


class Numbers(List[Uint8]):
    """A bounded list, for the capacity and element-type parameters."""

    LIMIT = 4
    ELEMENT_TYPE = Uint8


class Square(ProgressiveContainer):
    """A field layout with an interior gap, for the layout parameter."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint8
    color: Uint8


class Circle(ProgressiveContainer):
    """The compatible layout, sharing the position of the second field."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint8
    color: Uint8


class Shape(CompatibleUnion):
    """A union of the two layouts, for the options parameter."""

    OPTIONS = {1: Square, 2: Circle}


INFO = FixtureInfo(
    test_id="uint8/one",
    generated_by="tests/fillers/test_x.py::test_x",
    description="",
    fixture_format="ssz",
)


def test_the_json_mapping_is_pinned_to_camel_case() -> None:
    """An override of the mode or the alias style is refused, not silently ignored."""

    class Named(CamelModel):
        type_name: str

    assert Named(type_name="Uint8").to_json() == {"typeName": "Uint8"}

    with pytest.raises(TypeError, match="does not accept 'mode' or 'by_alias'"):
        Named(type_name="Uint8").to_json(by_alias=False)


def test_a_rejection_holds_the_message_it_was_authored_with() -> None:
    """The exact message wins over the substring, and each says what it found instead."""
    exact = ExpectedRejection(reason=ValueFault.NOT_A_BIT, exact_message="a boolean is 0 or 1")
    exact.assert_message_matches(ValueError("a boolean is 0 or 1"), "Decoder")
    with pytest.raises(AssertionError, match="Expected exact message"):
        exact.assert_message_matches(ValueError("something else"), "Decoder")

    substring = ExpectedRejection(reason=ValueFault.NOT_A_BIT, message_substring="0 or 1")
    substring.assert_message_matches(ValueError("a boolean is 0 or 1"), "Decoder")
    with pytest.raises(AssertionError, match="Expected message containing"):
        substring.assert_message_matches(ValueError("something else"), "Decoder")

    # Neither authored, so any message is accepted.
    silent = ExpectedRejection(reason=ValueFault.NOT_A_BIT)
    silent.assert_message_matches(ValueError("anything at all"), "Decoder")


def test_a_fixture_carries_its_metadata_and_a_hash_of_itself() -> None:
    """The hash covers the vector, not the envelope, so it is stable across a description edit."""
    fixture = SSZTest(type_name="Uint8", value=Uint8(1)).generate()

    with pytest.raises(AssertionError, match="missing its metadata envelope"):
        fixture.json_dict_with_info()

    emitted = fixture.with_info(INFO).json_dict_with_info()
    assert emitted["_info"]["hash"] == fixture.hash
    assert emitted["_info"]["testId"] == INFO.test_id
    assert emitted["serialized"] == "0x01"
    assert "info" not in emitted


def test_a_value_is_emitted_the_way_its_shape_reads() -> None:
    """A struct carries its fields, a boolean carries JSON true or false, and bytes carry hex."""
    values = {
        "Pair": Pair(number=Uint8(1), flag=Boolean(True)),
        "Bytes2": Bytes2(b"\xab\xcd"),
        "Boolean": Boolean(False),
        "Uint8": Uint8(7),
    }
    emitted = {
        name: SSZTest(type_name=name, value=value).generate().json_dict["value"]
        for name, value in values.items()
    }

    assert emitted == {
        "Pair": {"number": "1", "flag": True},
        "Bytes2": "0xabcd",
        "Boolean": False,
        "Uint8": "7",
    }


def test_an_honest_input_that_the_verifier_rejects_fails_the_fill() -> None:
    """A spec with no authored rejection has to process cleanly."""
    honest = SSZTest(type_name="Uint8", value=Uint8(1))
    honest.assert_expected_outcome(None)

    with pytest.raises(AssertionError, match="Verifier rejected an honest input"):
        honest.assert_expected_outcome(ValueError("refused"))


def test_a_flaw_that_goes_undetected_fails_the_fill() -> None:
    """An authored rejection that never fires means the spec accepted something it must not."""
    expectant = SSZTest(
        type_name="Uint8",
        value=Uint8(1),
        raw_bytes="0x0000",
        expected_rejection=ExpectedRejection(reason=ValueFault.SCOPE),
    )

    with pytest.raises(AssertionError, match="but processing succeeded"):
        expectant.assert_expected_outcome(None)


def test_a_decode_failure_emits_the_type_the_bytes_and_the_fault_that_fired() -> None:
    """Nothing decoded, so the vector carries no value and no root, and its bytes appear once."""
    fixture = SSZTest(
        type_name="Uint8",
        value=Uint8(0),
        raw_bytes="0x0000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE, message_substring="and the budget is 2"
        ),
    ).generate()

    assert fixture.rejection_reason is ValueFault.SCOPE
    assert fixture.json_dict == {
        "typeName": "Uint8",
        "typeDescriptor": {"kind": "Uint8", "bits": 8},
        "serialized": "0x0000",
        "rejectionReason": "SCOPE",
        "valid": False,
    }


def test_a_vector_a_decoder_must_accept_reads_as_valid_and_carries_its_value() -> None:
    """A positive vector states its validity too, and holds no rejection reason to assert on."""
    fixture = SSZTest(type_name="Uint8", value=Uint8(1)).generate()

    assert fixture.json_dict == {
        "typeName": "Uint8",
        "typeDescriptor": {"kind": "Uint8", "bits": 8},
        "serialized": "0x01",
        "value": "1",
        "root": "0x01" + "00" * 31,
        "valid": True,
    }


def test_a_decode_failure_vector_needs_bytes_to_reject() -> None:
    """There is no decode failure to record without an input that was decoded."""
    with pytest.raises(ValueError, match="raw_bytes is required"):
        SSZTest(
            type_name="Uint8",
            value=Uint8(0),
            expected_rejection=ExpectedRejection(reason=ValueFault.SCOPE),
        ).generate()


def test_a_rejection_for_the_wrong_reason_is_not_the_authored_one() -> None:
    """Two faults meaning different things must not be traded for one another in a vector."""
    with pytest.raises(AssertionError, match="refused for the wrong reason"):
        SSZTest(
            type_name="Uint8",
            value=Uint8(0),
            raw_bytes="0x0000",
            expected_rejection=ExpectedRejection(reason=ValueFault.NOT_A_BIT),
        ).generate()


def test_bytes_a_decoder_accepts_are_not_a_decode_failure() -> None:
    """An input the decoder takes cannot stand as a vector for refusing it."""
    with pytest.raises(AssertionError, match="but decoding succeeded"):
        SSZTest(
            type_name="Uint8",
            value=Uint8(0),
            raw_bytes="0x01",
            expected_rejection=ExpectedRejection(reason=ValueFault.SCOPE),
        ).generate()


def test_a_decode_failure_needs_an_authored_expectation() -> None:
    """The fault a vector emits is the authored one, so a caller with none has nothing to emit."""
    with pytest.raises(ValueError, match="require expected_rejection to be set"):
        SSZTest(type_name="Uint8", value=Uint8(0)).assert_decode_rejection(None, "Uint8")


def test_hex_is_written_and_read_with_its_prefix() -> None:
    """Vectors carry 0x-prefixed hex, and the prefix is optional on the way back in."""
    assert to_hex(b"\xab\xcd") == "0xabcd"
    assert from_hex("0xabcd") == b"\xab\xcd"
    assert from_hex("abcd") == b"\xab\xcd"


def test_a_fixture_hashes_the_same_way_twice() -> None:
    """The hash is taken over the sorted, separator-free JSON, so it does not move with the dict."""
    fixture = SSZTest(type_name="Uint8", value=Uint8(1)).generate()
    expected = json.dumps(fixture.json_dict, sort_keys=True, separators=(",", ":"))

    assert isinstance(fixture, SSZFixture)
    assert fixture.hash.startswith("0x")
    assert len(fixture.hash) == 66
    assert json.loads(expected)["root"] == fixture.root


UINT8 = {"kind": "Uint8", "bits": 8}


def test_a_declaration_is_read_off_the_class_and_not_off_its_name() -> None:
    """Two spellings of one declaration describe alike, and any changed parameter parts them."""
    assert describe_type(Bytes2).to_json(exclude_none=True) == {"kind": "ByteVector", "length": 2}
    assert describe_type(Bytes2Again) == describe_type(Bytes2)
    assert describe_type(Bytes3) != describe_type(Bytes2)

    assert describe_type(Pair).to_json(exclude_none=True) == {
        "kind": "Container",
        "fields": [
            {"name": "number", "type": UINT8},
            {"name": "flag", "type": {"kind": "Boolean"}},
        ],
    }
    assert describe_type(Swapped) != describe_type(Pair)


def test_a_declaration_writes_out_every_parameter_it_fixes() -> None:
    """A capacity, an element type, a field layout and a union's options all read out."""
    assert describe_type(Numbers).to_json(exclude_none=True) == {
        "kind": "List",
        "limit": 4,
        "elementType": UINT8,
    }
    square = {
        "kind": "ProgressiveContainer",
        "activeFields": [1, 0, 1],
        "fields": [{"name": "side", "type": UINT8}, {"name": "color", "type": UINT8}],
    }
    assert describe_type(Square).to_json(exclude_none=True) == square
    assert describe_type(Shape).to_json(exclude_none=True) == {
        "kind": "CompatibleUnion",
        "options": [
            {"selector": 1, "type": square},
            {
                "selector": 2,
                "type": {
                    "kind": "ProgressiveContainer",
                    "activeFields": [0, 1, 1],
                    "fields": [
                        {"name": "radius", "type": UINT8},
                        {"name": "color", "type": UINT8},
                    ],
                },
            },
        ],
    }


def test_a_vector_claims_its_type_name_for_the_declaration_of_its_value() -> None:
    """The name a vector emits is claimed against the declaration of the value under test."""
    fixture = SSZTest(type_name="Pair", value=Pair(number=Uint8(1), flag=Boolean(True))).generate()

    assert fixture.declared_types() == {"Pair": describe_type(Pair)}


def test_a_decode_failure_claims_its_type_name_with_no_value_to_read_it_off() -> None:
    """The shape a negative vector's name stands for comes from the decoder it was refused by."""
    fixture = SSZTest(
        type_name="Pair",
        value=Pair(number=Uint8(1), flag=Boolean(True)),
        raw_bytes="0x010101",
        expected_rejection=ExpectedRejection(reason=ValueFault.SCOPE),
    ).generate()

    assert fixture.value is None
    assert fixture.declared_types() == {"Pair": describe_type(Pair)}


def test_a_fixture_format_that_names_no_type_claims_nothing() -> None:
    """A format emitting no type name holds no name to a declaration."""

    class Bare(BaseConsensusFixture):
        def case_type_name(self) -> str:
            return "Bare"

        def case_kind(self) -> str:
            return "bare"

    assert Bare().declared_types() == {}
