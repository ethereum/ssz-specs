"""SSZ conformance test vectors for the EIP-8016 compatible union."""

from ssz import (
    CompatibleUnion,
    Container,
    List,
    ProgressiveContainer,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint64,
)
from ssz_testing import ExpectedRejection, RejectionReason, SSZTestFiller


class SampleSquare(ProgressiveContainer):
    """
    EIP-7495's own example: a field at position 0, a gap, then a field at position 2.

    It is the first option of the union below, and shares position 2 with the second.
    """

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class SampleCircle(ProgressiveContainer):
    """
    The other half of that example: a leading gap, then fields at positions 1 and 2.

    It encodes to the same three bytes as SampleSquare, so within a union the selector
    byte is the only thing on the wire that tells the two options apart.
    """

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class SampleUint16List4(List[Uint16]):
    """Bounded list of two-byte elements, a variable-size union option."""

    LIMIT = 4
    ELEMENT_TYPE = Uint16


class SampleUint16List4Alias(SampleUint16List4):
    """Second spelling of the same list, compatible with it by the identity rule."""


class SampleSquareProgressiveList(ProgressiveList[SampleSquare]):
    """Progressive list of the first shape."""

    ELEMENT_TYPE = SampleSquare


class SampleCircleProgressiveList(ProgressiveList[SampleCircle]):
    """Progressive list of the second shape, differing only in the element type."""

    ELEMENT_TYPE = SampleCircle


class SampleShape(CompatibleUnion):
    """EIP-8016's own example, with the first shape repeated under the highest selector."""

    OPTIONS = {1: SampleSquare, 2: SampleCircle, 127: SampleSquare}


class SampleNumbers(CompatibleUnion):
    """Union over a variable-size option, so the payload has no fixed width."""

    OPTIONS = {1: SampleUint16List4, 2: SampleUint16List4Alias}


class SampleEmptyProne(CompatibleUnion):
    """
    Union whose options differ only in the element type of a progressive list.

    Both options root alike when the list is empty, so the selector is the only thing
    separating the two values. This is the security consideration of EIP-8016.
    """

    OPTIONS = {1: SampleSquareProgressiveList, 2: SampleCircleProgressiveList}


class SampleSquareOnly(CompatibleUnion):
    """Single-option union, the second member of the union of unions below."""

    OPTIONS = {5: SampleSquare}


class SampleNestedShape(CompatibleUnion):
    """Union of unions: each option is itself a compatible union."""

    OPTIONS = {1: SampleShape, 2: SampleSquareOnly}


class SampleShapeContainer(Container):
    """Ordinary container reaching a union through an offset."""

    tag: Uint64
    body: SampleShape


class SampleShapeProgressiveContainer(ProgressiveContainer):
    """Progressive container reaching a union through an offset, with a gap before it."""

    ACTIVE_FIELDS = (1, 0, 1)

    tag: Uint64
    body: SampleShape


class SampleShapeProgressiveList(ProgressiveList[SampleShape]):
    """Progressive list of unions, whose variable-size bodies need an offset table."""

    ELEMENT_TYPE = SampleShape


def test_compatible_union_first_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding its first option round-trips unchanged.

    Given
    -----
    - a union declaring a progressive container under selector 1.
    - a value holding that option.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the selector byte followed by the option's own three bytes.
    - the root is the option's own root with the selector mixed in as a full chunk.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleShape",
        value=SampleShape(
            selector=Uint8(1),
            data=SampleSquare(side=Uint16(0x1234), color=Uint8(0x42)),
        ),
    )


def test_compatible_union_second_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding its second option round-trips unchanged.

    Given
    -----
    - the same union, and a value holding the option under selector 2.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the payload bytes match the first option's exactly.
    - the root differs, because the option's layout and the selector both differ.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleShape",
        value=SampleShape(
            selector=Uint8(2),
            data=SampleCircle(radius=Uint16(0x1234), color=Uint8(0x42)),
        ),
    )


def test_compatible_union_highest_selector(ssz_test: SSZTestFiller) -> None:
    """
    A union holding an option under selector 127 round-trips unchanged.

    Given
    -----
    - the same union, whose selector 127 names the same option as selector 1.
    - a value holding that option under the higher selector.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the selector byte is 0x7f, the top of the legal range.
    - the root differs from the same payload under selector 1.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleShape",
        value=SampleShape(
            selector=Uint8(127),
            data=SampleSquare(side=Uint16(0x1234), color=Uint8(0x42)),
        ),
    )


def test_compatible_union_variable_size_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a variable-size option round-trips unchanged.

    Given
    -----
    - a union over a bounded list of two-byte elements.
    - a value holding two elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the list body follows the selector directly, with no offset between them.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleNumbers",
        value=SampleNumbers(
            selector=Uint8(1),
            data=SampleUint16List4(data=[Uint16(1), Uint16(2)]),
        ),
    )


def test_compatible_union_empty_variable_size_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding an empty variable-size option round-trips unchanged.

    Given
    -----
    - the same union, holding a list with no elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the selector byte alone.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleNumbers",
        value=SampleNumbers(selector=Uint8(2), data=SampleUint16List4Alias(data=[])),
    )


def test_compatible_union_empty_list_options_separated_by_the_selector(
    ssz_test: SSZTestFiller,
) -> None:
    """
    A union whose empty options collide below the selector round-trips unchanged.

    Given
    -----
    - a union whose two options differ only in the element type of a progressive list.
    - a value holding the first option, empty.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the payload roots to the zero terminator with a zero count, as the other option
      would too.
    - the mixed-in selector is what separates this value from the same-shaped one under
      selector 2.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleEmptyProne",
        value=SampleEmptyProne(selector=Uint8(1), data=SampleSquareProgressiveList(data=[])),
    )


def test_compatible_union_other_empty_list_option(ssz_test: SSZTestFiller) -> None:
    """
    The other half of that pair round-trips unchanged and roots differently.

    Given
    -----
    - the same union, holding the second option, empty.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is one byte, differing from the first option's only in the selector.
    - the root differs from the first option's for that reason alone.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleEmptyProne",
        value=SampleEmptyProne(selector=Uint8(2), data=SampleCircleProgressiveList(data=[])),
    )


def test_compatible_union_of_unions(ssz_test: SSZTestFiller) -> None:
    """
    A union whose option is itself a union round-trips unchanged.

    Given
    -----
    - an outer union whose first option is the shape union.
    - a value holding the inner union, which in turn holds its second option.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - two selector bytes lead, one per level, before any payload byte.
    - each level mixes its own selector into the root of the level below it.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleNestedShape",
        value=SampleNestedShape(
            selector=Uint8(1),
            data=SampleShape(
                selector=Uint8(2),
                data=SampleCircle(radius=Uint16(0x1234), color=Uint8(0x42)),
            ),
        ),
    )


def test_container_holding_a_compatible_union(ssz_test: SSZTestFiller) -> None:
    """
    An ordinary container holding a union round-trips unchanged.

    Given
    -----
    - a container with an eight-byte tag and a union field.
    - a union value whose every option happens to be fixed-size.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - one offset follows the fixed part, because a union is always variable-size.
    - the union contributes its selector-mixed root as an ordinary leaf.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleShapeContainer",
        value=SampleShapeContainer(
            tag=Uint64(7),
            body=SampleShape(
                selector=Uint8(1),
                data=SampleSquare(side=Uint16(0x1234), color=Uint8(0x42)),
            ),
        ),
    )


def test_progressive_container_holding_a_compatible_union(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container holding a union round-trips unchanged.

    Given
    -----
    - a layout with a gap between the tag and the union field.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the gap costs no bytes, so the encoding matches the ordinary container's.
    - the union's root is the leaf at position 2, under the mixed-in layout word.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleShapeProgressiveContainer",
        value=SampleShapeProgressiveContainer(
            tag=Uint64(7),
            body=SampleShape(
                selector=Uint8(1),
                data=SampleSquare(side=Uint16(0x1234), color=Uint8(0x42)),
            ),
        ),
    )


def test_progressive_list_of_compatible_unions(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list of unions round-trips unchanged.

    Given
    -----
    - a progressive list whose elements are unions, holding one option each.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the elements are variable-size, so an offset table precedes the bodies.
    - each element hands its own selector-mixed root to the spine as one leaf.
    - the decoded value equals the original.
    """
    ssz_test(
        type_name="SampleShapeProgressiveList",
        value=SampleShapeProgressiveList(
            data=[
                SampleShape(selector=Uint8(1), data=SampleSquare(side=Uint16(1), color=Uint8(2))),
                SampleShape(selector=Uint8(2), data=SampleCircle(radius=Uint16(3), color=Uint8(4))),
            ]
        ),
    )


def test_compatible_union_decode_failure_empty_input(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union from an empty input is rejected.

    Given
    -----
    - a union whose every encoding opens with a selector byte.
    - an input of zero bytes.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget holds no selector at all.
    """
    ssz_test(
        type_name="SampleShape",
        value=SampleShape(
            selector=Uint8(1),
            data=SampleSquare(side=Uint16(0x1234), color=Uint8(0x42)),
        ),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=RejectionReason.DECODE_ERROR,
            exact_message="SampleShape: scope 0 holds no selector",
        ),
    )


def test_compatible_union_decode_failure_undeclared_selector(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose selector names no option is rejected.

    Given
    -----
    - a union declaring selectors 1, 2 and 127.
    - the input bytes 0x03341242, whose selector is inside the legal range and undeclared.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected before any payload byte is read.
    - the reason is that the selector names no option of this union.
    """
    ssz_test(
        type_name="SampleShape",
        value=SampleShape(
            selector=Uint8(1),
            data=SampleSquare(side=Uint16(0x1234), color=Uint8(0x42)),
        ),
        raw_bytes="0x03341242",
        expected_rejection=ExpectedRejection(
            reason=RejectionReason.DECODE_ERROR,
            exact_message="SampleShape: invalid union options, selector 3 names no option",
        ),
    )


def test_compatible_union_decode_failure_reserved_zero_selector(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose selector is the reserved zero is rejected.

    Given
    -----
    - the input bytes 0x00341242, whose leading byte is the reserved selector.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that zero can never name an option, so an uninitialized value cannot
      pass as a valid one.
    """
    ssz_test(
        type_name="SampleShape",
        value=SampleShape(
            selector=Uint8(1),
            data=SampleSquare(side=Uint16(0x1234), color=Uint8(0x42)),
        ),
        raw_bytes="0x00341242",
        expected_rejection=ExpectedRejection(
            reason=RejectionReason.DECODE_ERROR,
            exact_message="SampleShape: invalid union options, selector 0 names no option",
        ),
    )


def test_compatible_union_decode_failure_trailing_byte(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union with a spare byte after the payload is rejected.

    Given
    -----
    - a union whose selected option is three bytes wide.
    - the input bytes 0x0134124200, one byte longer than the canonical encoding.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that a canonical encoding maps to exactly one value.
    - the rest of the budget belongs to the option, so the option reports the surplus.
    """
    ssz_test(
        type_name="SampleShape",
        value=SampleShape(
            selector=Uint8(1),
            data=SampleSquare(side=Uint16(0x1234), color=Uint8(0x42)),
        ),
        raw_bytes="0x0134124200",
        expected_rejection=ExpectedRejection(
            reason=RejectionReason.DECODE_ERROR,
            exact_message="SampleSquare: expected 3 bytes, got 4",
        ),
    )


def test_compatible_union_decode_failure_truncated_payload(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose payload is cut short is rejected.

    Given
    -----
    - a union whose selected option opens with a two-byte field.
    - the input bytes 0x0134, which leave that field one byte short.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason surfaces from the option itself, since the rest of the budget is its own.
    """
    ssz_test(
        type_name="SampleShape",
        value=SampleShape(
            selector=Uint8(1),
            data=SampleSquare(side=Uint16(0x1234), color=Uint8(0x42)),
        ),
        raw_bytes="0x0134",
        expected_rejection=ExpectedRejection(
            reason=RejectionReason.DECODE_ERROR,
            exact_message="Uint16: expected 2 bytes, got 1",
        ),
    )
