"""SSZ conformance test vectors for the compatible-merkleization rules EIP-8016 unions rest on."""

from typing import ClassVar

import pytest

from ssz import (
    BitList,
    BitVector,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    ProgressiveList,
    SSZType,
    Uint8,
    Uint64,
    Uint256,
    Vector,
)
from ssz_testing import (
    DeclaredOption,
    SSZTestFiller,
    TypeDescriptor,
    TypeFault,
    TypeRejectionFiller,
    describe_type,
)

pytestmark = pytest.mark.tags("union")

CLASHING_OPTIONS = "options 1 and 2 merkleize differently"
"""The refusal every pair below earns, the fault naming the selectors and not the shapes."""


def union_of(left: type[SSZType], right: type[SSZType]) -> TypeDescriptor:
    """A two-option union declaration over the given pair, each option read off its own class."""
    return TypeDescriptor(
        kind="CompatibleUnion",
        options=(
            DeclaredOption(selector=1, type=describe_type(left)),
            DeclaredOption(selector=2, type=describe_type(right)),
        ),
    )


class CompatBitList4(BitList):
    """Bitlist capped at four bits."""

    LIMIT: ClassVar[int] = 4


class CompatBitList8(BitList):
    """Bitlist capped at eight bits, twice the capacity of the four-bit one."""

    LIMIT: ClassVar[int] = 8


class CompatBitVector4(BitVector):
    """Bitvector of four bits."""

    LENGTH: ClassVar[int] = 4


class CompatBitVector8(BitVector):
    """Bitvector of eight bits, twice the width of the four-bit one."""

    LENGTH: ClassVar[int] = 8


class CompatUint64List4(List[Uint64]):
    """List of eight-byte integers capped at four elements."""

    LIMIT: ClassVar[int] = 4


class CompatUint64List8(List[Uint64]):
    """List of eight-byte integers capped at eight elements."""

    LIMIT: ClassVar[int] = 8


class CompatUint256List4(List[Uint256]):
    """List of thirty-two-byte integers capped at four elements, the same capacity, wider."""

    LIMIT: ClassVar[int] = 4


class CompatUint64Vector4(Vector[Uint64]):
    """Four eight-byte integers."""

    LENGTH: ClassVar[int] = 4


class CompatUint64Vector8(Vector[Uint64]):
    """Eight eight-byte integers."""

    LENGTH: ClassVar[int] = 8


class CompatPair(Container):
    """Two-field struct, the reference the two variations below depart from."""

    amount: Uint64
    tag: Uint8


class CompatPairReordered(Container):
    """The same two field names and types, declared in the other order."""

    tag: Uint8
    amount: Uint64


class CompatPairRenamed(Container):
    """The same two positions and widths, the second field under another name."""

    amount: Uint64
    label: Uint8


class CompatAmountAtZero(ProgressiveContainer):
    """Layout holding an amount at position 0 and a tag at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    amount: Uint64
    tag: Uint8


class CompatTotalAtZero(ProgressiveContainer):
    """The same layout, position 0 holding a total instead of an amount."""

    ACTIVE_FIELDS = (1, 0, 1)

    total: Uint64
    tag: Uint8


class CompatAmountAtOne(ProgressiveContainer):
    """The same two field names, the amount moved from position 0 to position 1."""

    ACTIVE_FIELDS = (0, 1, 1)

    amount: Uint64
    tag: Uint8


class CompatBytes4(ByteVector):
    """Four-byte string, the specification's alias for four single bytes in a row."""

    LENGTH: ClassVar[int] = 4


class CompatUint8Vector4(Vector[Uint8]):
    """The same four bytes written out as a vector of one-byte integers."""

    LENGTH: ClassVar[int] = 4


class CompatByteSpellingUnion(CompatibleUnion):
    """Union offering one four-byte array under both of its spellings."""

    OPTIONS = {1: CompatBytes4, 2: CompatUint8Vector4}


class CompatSquare(ProgressiveContainer):
    """EIP-7495's own example: a side at position 0, a gap, then a color at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint64
    color: Uint8


class CompatCircle(ProgressiveContainer):
    """The other half of that example: a gap, then a radius at position 1 and a color at 2."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint64
    color: Uint8


class CompatSquareStream(ProgressiveList[CompatSquare]):
    """Unbounded run of the first shape."""


class CompatCircleStream(ProgressiveList[CompatCircle]):
    """Unbounded run of the second shape."""


class CompatShapeStreamUnion(CompatibleUnion):
    """Union over two progressive lists whose element types are themselves compatible."""

    OPTIONS = {1: CompatSquareStream, 2: CompatCircleStream}


class CompatSquareRecord(Container):
    """Struct pairing a tag with the first shape."""

    tag: Uint8
    shape: CompatSquare


class CompatCircleRecord(Container):
    """Struct pairing a tag with the second shape, which is not the first one restated."""

    tag: Uint8
    shape: CompatCircle


class CompatShapeRecordUnion(CompatibleUnion):
    """Union over two structs that differ in their declarations and still merkleize alike."""

    OPTIONS = {1: CompatSquareRecord, 2: CompatCircleRecord}


def test_bitlists_of_two_capacities_are_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a union over bitlists of two capacities is refused.

    Given
    -----
    - a union offering a bitlist capped at four bits and one capped at eight.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, two bitlists agreeing only when they share a capacity.
    - both options pack into a single chunk and mix their bit count in above it.
    - comparing the emitted tree shape alone would let this pair through.
    """
    ssz_type_rejection(
        case_id="compatibility/incompatible/bitlist_capacities",
        type_name="ClashingBitListCapacityUnion",
        type_descriptor=union_of(CompatBitList4, CompatBitList8),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message=CLASHING_OPTIONS,
    )


def test_bitvectors_of_two_capacities_are_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a union over bitvectors of two capacities is refused.

    Given
    -----
    - a union offering a bitvector of four bits and one of eight.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, two bitvectors agreeing only when they share a capacity.
    - both encode to one byte and root to one chunk.
    - the capacity that separates them reaches neither the wire nor the tree.
    """
    ssz_type_rejection(
        case_id="compatibility/incompatible/bitvector_capacities",
        type_name="ClashingBitVectorCapacityUnion",
        type_descriptor=union_of(CompatBitVector4, CompatBitVector8),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message=CLASHING_OPTIONS,
    )


def test_lists_of_two_capacities_are_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a union over lists of one element type at two capacities is refused.

    Given
    -----
    - a union offering an eight-byte-integer list capped at four elements and one at eight.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a list answering for its capacity as well as its element type.
    - the capacity fixes the padding depth, so one element sits at two generalized indices.
    """
    ssz_type_rejection(
        case_id="compatibility/incompatible/list_capacities",
        type_name="ClashingListCapacityUnion",
        type_descriptor=union_of(CompatUint64List4, CompatUint64List8),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message=CLASHING_OPTIONS,
    )


def test_lists_over_two_element_types_are_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a union over lists of one capacity holding two element types is refused.

    Given
    -----
    - a union offering lists of eight-byte and thirty-two-byte integers, both capped at four.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, the shared capacity settling only half of the rule.
    - four narrow elements pack into one chunk where four wide ones fill four.
    - the two options therefore root over trees of different depths.
    """
    ssz_type_rejection(
        case_id="compatibility/incompatible/list_element_types",
        type_name="ClashingListElementUnion",
        type_descriptor=union_of(CompatUint64List4, CompatUint256List4),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message=CLASHING_OPTIONS,
    )


def test_vectors_of_two_lengths_are_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a union over vectors of one element type at two lengths is refused.

    Given
    -----
    - a union offering four eight-byte integers and eight of them.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a vector answering for its length as well as its element type.
    - a vector mixes no length in, so only the declarations tell the two options apart.
    - a reader that counted chunks alone would find them alike.
    """
    ssz_type_rejection(
        case_id="compatibility/incompatible/vector_lengths",
        type_name="ClashingVectorLengthUnion",
        type_descriptor=union_of(CompatUint64Vector4, CompatUint64Vector8),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message=CLASHING_OPTIONS,
    )


def test_containers_with_the_fields_reordered_are_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a union over two structs naming the same fields in two orders is refused.

    Given
    -----
    - a union offering an amount-then-tag struct and the same two fields the other way round.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a struct answering for its field names in the order it declares them.
    - both options hold one field of each name and root over two chunks.
    - only the order separates them, and it decides which name each proof reaches.
    """
    ssz_type_rejection(
        case_id="compatibility/incompatible/container_fields_reordered",
        type_name="ClashingReorderedFieldsUnion",
        type_descriptor=union_of(CompatPair, CompatPairReordered),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message=CLASHING_OPTIONS,
    )


def test_containers_differing_by_a_field_name_are_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a union over two structs whose second field is named differently is refused.

    Given
    -----
    - a union offering a struct of an amount and a tag, and one of an amount and a label.
    - the two second fields share a width and a position.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, the rule asking for shared names and not merely for matching types.
    - one value of each option holding the same two numbers encodes and roots identically.
    - nothing but the names distinguishes them.
    - a proof is addressed by name.
    """
    ssz_type_rejection(
        case_id="compatibility/incompatible/container_field_renamed",
        type_name="ClashingRenamedFieldUnion",
        type_descriptor=union_of(CompatPair, CompatPairRenamed),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message=CLASHING_OPTIONS,
    )


def test_layouts_holding_two_names_at_one_position_are_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a union over two layouts that set one position to two names is refused.

    Given
    -----
    - a union offering two progressive containers, both setting positions 0 and 2.
    - position 2 holds a tag in each.
    - position 0 holds an amount in the first and a total in the second.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a position set in both layouts having to hold one field name.
    - the shared position 2 agrees, so the refusal rests on position 0 alone.
    """
    ssz_type_rejection(
        case_id="compatibility/incompatible/layout_position_two_names",
        type_name="ClashingLayoutNameUnion",
        type_descriptor=union_of(CompatAmountAtZero, CompatTotalAtZero),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message=CLASHING_OPTIONS,
    )


def test_layouts_holding_one_name_at_two_positions_are_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a union over two layouts that place one field name at two positions is refused.

    Given
    -----
    - a union offering a progressive container with an amount at 0 and a tag at 2.
    - the other option puts the amount at position 1 and the tag at position 2.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a name set in both types having to sit at one position.
    - position 2 is the only one set in both layouts.
    - it holds the same tag in each, so shared positions alone would accept this pair.
    - a proof for the amount would reach position 0 under one option and 1 under the other.
    """
    ssz_type_rejection(
        case_id="compatibility/incompatible/layout_name_two_positions",
        type_name="ClashingLayoutPositionUnion",
        type_descriptor=union_of(CompatAmountAtZero, CompatAmountAtOne),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message=CLASHING_OPTIONS,
    )


def test_union_over_a_byte_array_holding_the_array_spelling(ssz_test: SSZTestFiller) -> None:
    """
    A union declaring a four-byte array against four one-byte integers round-trips its array.

    Given
    -----
    - a union whose options are a four-byte string and a vector of four one-byte integers.
    - the specification calls those one type under two spellings.
    - a value holding the four-byte string under selector 1.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the declaration stands, the two spellings being compatible rather than merely alike.
    - the encoding is the selector byte followed by the four bytes.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="compatibility/byte_array_spellings/byte_vector",
        type_name="CompatByteSpellingUnion",
        value=CompatByteSpellingUnion(selector=Uint8(1), data=CompatBytes4(b"\xde\xad\xbe\xef")),
    )


def test_union_over_a_byte_array_holding_the_element_spelling(ssz_test: SSZTestFiller) -> None:
    """
    The same union round-trips the vector spelling of the very same four bytes.

    Given
    -----
    - the same union, and a value holding the four one-byte integers under selector 2.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the payload bytes match the array case exactly, only the selector byte differing.
    - the root differs from the array case, the selector mixing in above the same subtree.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="compatibility/byte_array_spellings/uint8_vector",
        type_name="CompatByteSpellingUnion",
        value=CompatByteSpellingUnion(
            selector=Uint8(2),
            data=CompatUint8Vector4(data=[Uint8(0xDE), Uint8(0xAD), Uint8(0xBE), Uint8(0xEF)]),
        ),
    )


def test_union_over_progressive_lists_holding_the_first_element_type(
    ssz_test: SSZTestFiller,
) -> None:
    """
    A union over two progressive lists of compatible elements round-trips the first of them.

    Given
    -----
    - two compatible progressive containers, sharing position 2 and setting 0 and 1.
    - a union whose options are the unbounded runs of those two shapes.
    - a value holding two of the first shape under selector 1.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the declaration stands, a progressive list answering for its element type alone.
    - the two options carry no capacity, so nothing beyond the element rule is asked of them.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="compatibility/progressive_list_elements/square",
        type_name="CompatShapeStreamUnion",
        value=CompatShapeStreamUnion(
            selector=Uint8(1),
            data=CompatSquareStream(
                data=[
                    CompatSquare(side=Uint64(3), color=Uint8(1)),
                    CompatSquare(side=Uint64(4), color=Uint8(2)),
                ]
            ),
        ),
    )


def test_union_over_progressive_lists_holding_the_second_element_type(
    ssz_test: SSZTestFiller,
) -> None:
    """
    The same union round-trips a run of the other shape.

    Given
    -----
    - the same union, and a value holding two of the second shape under selector 2.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the element type differs from the first case while the option shape does not.
    - each element roots over the same spine, its layout mixed in above the fields.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="compatibility/progressive_list_elements/circle",
        type_name="CompatShapeStreamUnion",
        value=CompatShapeStreamUnion(
            selector=Uint8(2),
            data=CompatCircleStream(
                data=[
                    CompatCircle(radius=Uint64(3), color=Uint8(1)),
                    CompatCircle(radius=Uint64(4), color=Uint8(2)),
                ]
            ),
        ),
    )


def test_union_over_two_distinct_containers_holding_the_first(ssz_test: SSZTestFiller) -> None:
    """
    A union over two structs that differ in their declarations round-trips the first of them.

    Given
    -----
    - two structs naming a tag and a shape in that order, over the two compatible layouts.
    - the pair is therefore not one declaration restated.
    - a value holding the first struct under selector 1.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the declaration stands, the two structs sharing their field names in order.
    - each of those names holds compatible types.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="compatibility/container_field_types/square",
        type_name="CompatShapeRecordUnion",
        value=CompatShapeRecordUnion(
            selector=Uint8(1),
            data=CompatSquareRecord(
                tag=Uint8(9), shape=CompatSquare(side=Uint64(5), color=Uint8(6))
            ),
        ),
    )


def test_union_over_two_distinct_containers_holding_the_second(ssz_test: SSZTestFiller) -> None:
    """
    The same union round-trips the other struct, whose shape field holds the other layout.

    Given
    -----
    - the same union, and a value holding the second struct under selector 2.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the two options encode to the same number of bytes.
    - their shape fields differ only in which position the layout sets.
    - the roots differ, each shape mixing its own layout in above its fields.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="compatibility/container_field_types/circle",
        type_name="CompatShapeRecordUnion",
        value=CompatShapeRecordUnion(
            selector=Uint8(2),
            data=CompatCircleRecord(
                tag=Uint8(9), shape=CompatCircle(radius=Uint64(5), color=Uint8(6))
            ),
        ),
    )
