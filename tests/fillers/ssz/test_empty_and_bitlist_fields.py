"""SSZ conformance vectors for a bitlist behind an offset, and for shapes handed no bytes."""

from typing import ClassVar

import pytest

from ssz import BitList, Boolean, ByteVector, Container, List, Uint8, Uint64, Uint256, Vector
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault


class SampleBitList12(BitList):
    """Bitlist capped at twelve bits, a variable-size shape a struct reaches through an offset."""

    LIMIT: ClassVar[int] = 12


class SampleBitListField(Container):
    """A one-byte field and a bitlist, so the fixed part is that byte and one offset."""

    head: Uint8
    flags: SampleBitList12


class EmptyBytes4(ByteVector):
    """Four-byte byte vector, the fixed byte array of the empty-input cases."""

    LENGTH: ClassVar[int] = 4


class EmptyUint64Vector2(Vector[Uint64]):
    """Two eight-byte elements, the fixed vector of the empty-input cases."""

    LENGTH: ClassVar[int] = 2


class EmptyFixedPair(Container):
    """Two fixed-size fields and no offset, so the struct has a byte width of its own."""

    head: Uint8
    tail: Uint64


class EmptyUint64List4(List[Uint64]):
    """Bounded list of eight-byte elements, the one shape here whose empty input is a value."""

    LIMIT: ClassVar[int] = 4


FLAG_BITS = [Boolean(bit) for bit in (1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1)]
"""Eleven bits, one more than a byte holds, so the delimiter lands in a second byte."""


@pytest.mark.tags("offsets")
def test_bitlist_field_behind_offset(ssz_test: SSZTestFiller) -> None:
    """
    A container holding a bitlist reaches it through an offset.

    Given
    -----
    - a container of a one-byte field and a bitlist capped at twelve bits.
    - a bitlist of eleven bits, whose delimiter spills into a second byte.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - the offset is five, the one-byte field plus the four bytes of the offset itself.
    - a bitlist is variable-size, so the struct writes an offset for it and not its bytes.
    """
    ssz_test(
        case_id="bitlist_field/behind_offset",
        type_name="SampleBitListField",
        value=SampleBitListField(head=Uint8(0x2A), flags=SampleBitList12(data=FLAG_BITS)),
    )


@pytest.mark.tags("offsets", "empty")
def test_bitlist_field_empty_span(ssz_test: SSZTestFiller) -> None:
    """
    A container whose offset leaves the bitlist no bytes is rejected.

    Given
    -----
    - a container of a one-byte field and a bitlist capped at twelve bits.
    - the input bytes 0x2a05000000, whose offset of five is where the fixed part ends.
    - nothing after that offset, so the span handed to the bitlist is empty.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that an empty input encodes no value.
    - the refusal names the field the empty span belonged to.
    - the empty bitlist is not spelled this way: it still carries its delimiter, as 0x01.
    """
    ssz_test(
        case_id="bitlist_field/invalid/empty_span",
        type_name="SampleBitListField",
        value=SampleBitListField.default(),
        raw_bytes="0x2a05000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.EMPTY_ENCODING,
            exact_message="flags: an empty input encodes no value",
        ),
    )


@pytest.mark.tags("offsets", "malleability")
def test_bitlist_field_no_delimiter(ssz_test: SSZTestFiller) -> None:
    """
    A container whose bitlist body sets no delimiter is rejected.

    Given
    -----
    - a container of a one-byte field and a bitlist capped at twelve bits.
    - the input bytes 0x2a0500000000, whose offset of five is where the fixed part ends.
    - a body of one zero byte, which sets no bit and so carries no delimiter.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the encoding sets no delimiter bit.
    - a valid offset does not excuse the body it points at.
    """
    ssz_test(
        case_id="bitlist_field/invalid/no_delimiter",
        type_name="SampleBitListField",
        value=SampleBitListField.default(),
        raw_bytes="0x2a0500000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NO_DELIMITER,
            exact_message="flags: the encoding sets no delimiter bit",
        ),
    )


@pytest.mark.tags("boundary", "empty")
def test_empty_input_uint8(ssz_test: SSZTestFiller) -> None:
    """
    A one-byte unsigned integer given no bytes at all is rejected.

    Given
    -----
    - the type Uint8, the narrowest integer, which spans one byte.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the absent byte is not read as zero.
    """
    ssz_test(
        case_id="empty_input/invalid/uint8",
        type_name="Uint8",
        value=Uint8(0),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="Uint8 spans 1 bytes, and the budget is 0",
        ),
    )


@pytest.mark.tags("boundary", "empty")
def test_empty_input_uint64(ssz_test: SSZTestFiller) -> None:
    """
    An eight-byte unsigned integer given no bytes at all is rejected.

    Given
    -----
    - the type Uint64, which spans eight bytes.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the input is not padded out to the declared width.
    """
    ssz_test(
        case_id="empty_input/invalid/uint64",
        type_name="Uint64",
        value=Uint64(0),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="Uint64 spans 8 bytes, and the budget is 0",
        ),
    )


@pytest.mark.tags("boundary", "empty")
def test_empty_input_uint256(ssz_test: SSZTestFiller) -> None:
    """
    A thirty-two-byte unsigned integer given no bytes at all is rejected.

    Given
    -----
    - the type Uint256, the widest integer, which spans thirty-two bytes.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the count of missing bytes does not soften the refusal.
    """
    ssz_test(
        case_id="empty_input/invalid/uint256",
        type_name="Uint256",
        value=Uint256(0),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="Uint256 spans 32 bytes, and the budget is 0",
        ),
    )


@pytest.mark.tags("boundary", "empty")
def test_empty_input_byte_vector(ssz_test: SSZTestFiller) -> None:
    """
    A fixed byte array given no bytes at all is rejected.

    Given
    -----
    - a byte vector of length four.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - the all-zero value of this type is four bytes, and no input at all is not it.
    """
    ssz_test(
        case_id="empty_input/invalid/byte_vector",
        type_name="EmptyBytes4",
        value=EmptyBytes4.default(),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="EmptyBytes4 spans 4 bytes, and the budget is 0",
        ),
    )


@pytest.mark.tags("boundary", "empty")
def test_empty_input_fixed_vector(ssz_test: SSZTestFiller) -> None:
    """
    A fixed vector given no bytes at all is rejected.

    Given
    -----
    - a vector of two eight-byte elements, which spans sixteen bytes.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the type's width and the budget disagree.
    - a declared count admits no reading of an empty input as no elements.
    """
    ssz_test(
        case_id="empty_input/invalid/fixed_vector",
        type_name="EmptyUint64Vector2",
        value=EmptyUint64Vector2.default(),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="EmptyUint64Vector2 spans 16 bytes, and the budget is 0",
        ),
    )


@pytest.mark.tags("boundary", "empty")
def test_empty_input_fixed_container(ssz_test: SSZTestFiller) -> None:
    """
    A fixed-size container given no bytes at all is rejected.

    Given
    -----
    - a container of a one-byte field and an eight-byte field, which spans nine bytes.
    - an empty input.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that a budget of nothing is not the nine bytes the container spans.
    - the refusal names the container, the budget being settled before any field is read.
    """
    ssz_test(
        case_id="empty_input/invalid/fixed_container",
        type_name="EmptyFixedPair",
        value=EmptyFixedPair.default(),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="EmptyFixedPair spans 9 bytes, and the budget is 0",
        ),
    )


@pytest.mark.tags("boundary", "empty")
def test_empty_input_list(ssz_test: SSZTestFiller) -> None:
    """
    A list given no bytes at all is the empty list.

    Given
    -----
    - a list of at most four eight-byte elements.
    - the empty list of that type, whose encoding is no bytes at all.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the decoded value equals the original.
    - a list carries no count of its own, so its byte count is what says how many it holds.
    - this is the one shape here that accepts the input every fixed-size shape refuses.
    """
    ssz_test(
        case_id="empty_input/list_is_empty",
        type_name="EmptyUint64List4",
        value=EmptyUint64List4(data=[]),
    )
