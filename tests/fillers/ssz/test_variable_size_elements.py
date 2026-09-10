"""SSZ conformance vectors for a sequence whose elements are themselves variable-size."""

from typing import ClassVar

import pytest

from ssz import ByteList, Container, List, Uint32, Vector
from ssz_testing import SSZTestFiller

pytestmark = pytest.mark.tags("offsets")


class VarElemByteList8(ByteList):
    """Byte list of up to 8 bytes, the variable-size element every sequence here holds."""

    LIMIT: ClassVar[int] = 8


class VarElemList5(List[VarElemByteList8]):
    """List of up to 5 variable-size elements, a capacity that is not a power of two."""

    LIMIT: ClassVar[int] = 5
    ELEMENT_TYPE = VarElemByteList8


class VarElemVector3(Vector[VarElemByteList8]):
    """Vector of exactly 3 of the same variable-size element, its count declared not implied."""

    LENGTH: ClassVar[int] = 3
    ELEMENT_TYPE = VarElemByteList8


class VarElemInnerList4(List[VarElemByteList8]):
    """List of up to 4 variable-size elements, held as an element so its table nests."""

    LIMIT: ClassVar[int] = 4
    ELEMENT_TYPE = VarElemByteList8


class VarElemOuterList3(List[VarElemInnerList4]):
    """List of up to 3 lists, so every body it opens leads with an offset table of its own."""

    LIMIT: ClassVar[int] = 3
    ELEMENT_TYPE = VarElemInnerList4


class VarElemRecord(Container):
    """Struct of a fixed field and a variable-size one, which makes the struct variable-size."""

    tag: Uint32
    payload: VarElemByteList8


class VarElemRecordList4(List[VarElemRecord]):
    """List of up to 4 of those structs, a capacity that is a power of two."""

    LIMIT: ClassVar[int] = 4
    ELEMENT_TYPE = VarElemRecord


def _element(data: bytes) -> VarElemByteList8:
    """One variable-size element holding the given bytes."""
    return VarElemByteList8(data=data)


THREE_ELEMENTS = [_element(b"\xaa"), _element(b"\xbb\xcc\xdd\xee"), _element(b"\x11\x22")]
"""Three elements of one, four and two bytes, shared by the list and the vector that follow."""


def test_list_three_elements_of_different_lengths(ssz_test: SSZTestFiller) -> None:
    """
    A list of three variable-size elements round-trips through its offset table.

    Given
    -----
    - a list of up to five byte lists, holding elements of one, four and two bytes.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding leads with three offsets of 12, 13 and 17, then the bodies in order.
    - the element count is recovered as the first offset divided by four, nothing else stating it.
    - the tree is three leaves under a capacity of five, padded to eight, with the count mixed in.
    """
    ssz_test(
        case_id="variable_elements/bytelist8_list5/three_lengths",
        type_name="VarElemList5",
        value=VarElemList5(data=THREE_ELEMENTS),
    )


@pytest.mark.tags("boundary")
def test_list_empty(ssz_test: SSZTestFiller) -> None:
    """
    An empty list of variable-size elements encodes to no bytes at all.

    Given
    -----
    - a list of up to five byte lists, holding nothing.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is empty: a count of zero leaves no offset to write, so there is no table.
    - the empty input is not malformed, and decodes back to the empty list.
    - the tree is no leaf under a capacity of five, padded to eight, with a count of zero mixed in.
    """
    ssz_test(
        case_id="variable_elements/bytelist8_list5/empty",
        type_name="VarElemList5",
        value=VarElemList5(data=[]),
    )


@pytest.mark.tags("boundary")
def test_list_one_empty_element(ssz_test: SSZTestFiller) -> None:
    """
    A list holding one empty element encodes to a table and nothing after it.

    Given
    -----
    - a list of up to five byte lists, holding a single element of zero bytes.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is 0x04000000, one offset of four, with no body after it.
    - this is not the empty list, which writes no table: four bytes and zero bytes differ.
    - the two roots differ too, one leaf against none and a count of one against zero.
    """
    ssz_test(
        case_id="variable_elements/bytelist8_list5/one_empty_element",
        type_name="VarElemList5",
        value=VarElemList5(data=[_element(b"")]),
    )


def test_list_middle_element_empty(ssz_test: SSZTestFiller) -> None:
    """
    A list whose middle element is empty repeats an offset, which is well-formed.

    Given
    -----
    - a list of up to five byte lists, holding two bytes, nothing, then three bytes.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the offsets are 12, 14 and 14, the repeated pair being the empty element's own span.
    - a table has to ascend but need not strictly, so equal neighbours are accepted.
    - the tree is three leaves, the middle one the root of an empty byte list, not a zero leaf.
    """
    ssz_test(
        case_id="variable_elements/bytelist8_list5/middle_element_empty",
        type_name="VarElemList5",
        value=VarElemList5(data=[_element(b"\xaa\xbb"), _element(b""), _element(b"\xcc\xdd\xee")]),
    )


@pytest.mark.tags("boundary", "limit")
def test_list_at_limit(ssz_test: SSZTestFiller) -> None:
    """
    A list filled to its declared capacity round-trips, and still pads its tree.

    Given
    -----
    - a list of up to five byte lists, holding five elements of one to eight bytes.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the first offset is twenty, five offsets of four, which is the largest count accepted.
    - the last element runs to eight bytes, the element type's own capacity.
    - the tree still pads: five leaves under a capacity of five widen to eight, not to five.
    """
    ssz_test(
        case_id="variable_elements/bytelist8_list5/at_limit",
        type_name="VarElemList5",
        value=VarElemList5(
            data=[
                _element(b"\x01"),
                _element(b"\x02\x03"),
                _element(b"\x04\x05\x06"),
                _element(b"\x07\x08\x09\x0a"),
                _element(b"\x0b" * 8),
            ]
        ),
    )


def test_vector_declared_count(ssz_test: SSZTestFiller) -> None:
    """
    A vector of variable-size elements takes its count from the declaration, not the table.

    Given
    -----
    - a vector of exactly three byte lists, holding the same elements as the three-element list.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is byte-identical to that list's: the same table, the same bodies.
    - the count is fixed at three by the type, so the first offset confirms it rather than sets it.
    - the roots differ: three leaves padded to four, and no count mixed in.
    """
    ssz_test(
        case_id="variable_elements/bytelist8_vector3/declared_count",
        type_name="VarElemVector3",
        value=VarElemVector3(data=THREE_ELEMENTS),
    )


def test_list_of_lists(ssz_test: SSZTestFiller) -> None:
    """
    A list whose elements are lists nests one offset table inside another.

    Given
    -----
    - a list of up to three inner lists, holding one element, none, then two.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the outer offsets are 12, 18 and 18, and each body it opens is read as a table of its own.
    - an inner offset is measured from its own body's start, not from the start of the input.
    - the empty inner list is four bytes shorter than one holding an empty element would be.
    - the tree is three leaves under a capacity of three, padded to four, each leaf a list's root.
    """
    ssz_test(
        case_id="variable_elements/nested_list3/table_of_tables",
        type_name="VarElemOuterList3",
        value=VarElemOuterList3(
            data=[
                VarElemInnerList4(data=[_element(b"\xaa\xbb")]),
                VarElemInnerList4(data=[]),
                VarElemInnerList4(data=[_element(b"\xcc"), _element(b"\xdd\xee\xff")]),
            ]
        ),
    )


@pytest.mark.tags("limit")
def test_list_of_variable_size_containers(ssz_test: SSZTestFiller) -> None:
    """
    A list of variable-size structs indexes each struct's own fixed part.

    Given
    -----
    - a list of up to four structs, each a four-byte tag and a byte list.
    - four of them, filling the capacity, with distinct tags and payloads of 1, 0, 3 and 8 bytes.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the outer offsets are 16, 25, 33 and 44, one per struct.
    - each struct opens with its tag and one offset of eight, its own fixed part being eight bytes.
    - the struct with an empty payload is still eight bytes, its offset pointing to its own end.
    - the tree is four leaves under a capacity of four, the one shape here that pads nothing.
    """
    ssz_test(
        case_id="variable_elements/record_list4/at_limit",
        type_name="VarElemRecordList4",
        value=VarElemRecordList4(
            data=[
                VarElemRecord(tag=Uint32(1), payload=_element(b"\xa1")),
                VarElemRecord(tag=Uint32(0x00010203), payload=_element(b"")),
                VarElemRecord(tag=Uint32(2**32 - 1), payload=_element(b"\xb1\xb2\xb3")),
                VarElemRecord(tag=Uint32(7), payload=_element(b"\xc1" * 8)),
            ]
        ),
    )
