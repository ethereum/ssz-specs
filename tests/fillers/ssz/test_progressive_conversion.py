"""SSZ conformance test vectors for the EIP-7688 bounded-to-progressive conversion."""

from typing import ClassVar

import pytest

from ssz import (
    BitList,
    Boolean,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveList,
    SSZType,
    Uint16,
    Uint64,
    hash_tree_root,
)
from ssz_testing import SSZTestFiller


def check_shared_payload(first: SSZType, second: SSZType, serialized: str) -> None:
    """
    Check that both shapes still write the one encoding the pair's two vectors carry.

    Raises:
        AssertionError: When either shape has drifted from the authored bytes.
    """
    for value in (first, second):
        encoded = f"0x{value.encode_bytes().hex()}"
        if encoded != serialized:
            raise AssertionError(
                f"{type(value).__name__} now encodes to {encoded}, and the vectors say {serialized}"
            )


def check_one_payload_two_roots(
    first: SSZType,
    second: SSZType,
    serialized: str,
    first_root: str,
    second_root: str,
) -> None:
    """
    Check the conversion keeps the bytes and moves the root, against the authored literals.

    Raises:
        AssertionError: When either encoding drifts, when either root drifts, or when the two
            shapes merkleize alike.
    """
    check_shared_payload(first, second, serialized)
    for value, expected in ((first, first_root), (second, second_root)):
        actual = f"0x{hash_tree_root(value).hex()}"
        if actual != expected:
            raise AssertionError(
                f"{type(value).__name__} now roots to {actual}, and its vector says {expected}"
            )
    if first_root == second_root:
        raise AssertionError(
            f"{type(first).__name__} and {type(second).__name__} merkleize alike, "
            f"so nothing in the root shows the conversion happened"
        )


def check_one_payload_one_root(first: SSZType, second: SSZType, serialized: str, root: str) -> None:
    """
    Check two shapes that share their encoding and their root, against the authored literals.

    Raises:
        AssertionError: When either encoding drifts, or when either root is no longer the
            authored one.
    """
    check_shared_payload(first, second, serialized)
    for value in (first, second):
        actual = f"0x{hash_tree_root(value).hex()}"
        if actual != root:
            raise AssertionError(
                f"{type(value).__name__} now roots to {actual}, and its vector says {root}"
            )


class ConversionUint64List16(List[Uint64]):
    """Bounded list of eight-byte elements, the shape a fork converts away from."""

    LIMIT: ClassVar[int] = 16
    ELEMENT_TYPE = Uint64


class ConversionUint64List8(List[Uint64]):
    """The same element type at half the capacity, so the encoding can be read against two."""

    LIMIT: ClassVar[int] = 8
    ELEMENT_TYPE = Uint64


class ConversionUint64ProgressiveList(ProgressiveList[Uint64]):
    """The progressive twin, carrying the same element type and no capacity."""

    ELEMENT_TYPE = Uint64


class ConversionBitList2048(BitList):
    """Bounded bitfield at the committee size, the shape aggregation bits convert away from."""

    LIMIT: ClassVar[int] = 2048


class ConversionUint16List4(List[Uint16]):
    """Variable-size element, held fixed across the conversion so only the outer shape moves."""

    LIMIT: ClassVar[int] = 4
    ELEMENT_TYPE = Uint16


class ConversionNestedList4(List[ConversionUint16List4]):
    """Bounded list of variable-size elements, whose encoding opens with an offset table."""

    LIMIT: ClassVar[int] = 4
    ELEMENT_TYPE = ConversionUint16List4


class ConversionNestedProgressiveList(ProgressiveList[ConversionUint16List4]):
    """The progressive twin over that same variable-size element type."""

    ELEMENT_TYPE = ConversionUint16List4


class ConversionBodyBounded(Container):
    """Container over the pre-conversion field types, in the shape of an indexed attestation."""

    slot: Uint64
    attesting_indices: ConversionUint64List16
    aggregation_bits: ConversionBitList2048


class ConversionBodyProgressive(Container):
    """The same container with both capacities dropped, which is the EIP-7688 fork step."""

    slot: Uint64
    attesting_indices: ConversionUint64ProgressiveList
    aggregation_bits: ProgressiveBitList


CONVERSION_INDICES = [Uint64(1), Uint64(2), Uint64(3)]
"""Three elements, packing into a single chunk on either side of the conversion."""

CONVERSION_BITS = [Boolean(bit) for bit in (1, 0, 1, 1, 0, 1, 0, 0, 1)]
"""Nine bits, so the delimiter spills into a second byte."""

CONVERSION_NESTED = [
    ConversionUint16List4(data=[Uint16(1), Uint16(2)]),
    ConversionUint16List4(data=[]),
    ConversionUint16List4(data=[Uint16(3), Uint16(4), Uint16(5)]),
]
"""Three variable-size elements of differing widths, one of them empty."""

BOUNDED_INDICES = ConversionUint64List16(data=CONVERSION_INDICES)
PROGRESSIVE_INDICES = ConversionUint64ProgressiveList(data=CONVERSION_INDICES)
NARROWER_BOUNDED_INDICES = ConversionUint64List8(data=CONVERSION_INDICES)

EMPTY_BOUNDED_INDICES = ConversionUint64List16(data=[])
EMPTY_PROGRESSIVE_INDICES = ConversionUint64ProgressiveList(data=[])

BOUNDED_BITS = ConversionBitList2048(data=CONVERSION_BITS)
PROGRESSIVE_BITS = ProgressiveBitList(data=CONVERSION_BITS)

EMPTY_BOUNDED_BITS = ConversionBitList2048(data=[])
EMPTY_PROGRESSIVE_BITS = ProgressiveBitList(data=[])

BOUNDED_NESTED = ConversionNestedList4(data=CONVERSION_NESTED)
PROGRESSIVE_NESTED = ConversionNestedProgressiveList(data=CONVERSION_NESTED)

BOUNDED_BODY = ConversionBodyBounded(
    slot=Uint64(0x1234),
    attesting_indices=BOUNDED_INDICES,
    aggregation_bits=BOUNDED_BITS,
)
PROGRESSIVE_BODY = ConversionBodyProgressive(
    slot=Uint64(0x1234),
    attesting_indices=PROGRESSIVE_INDICES,
    aggregation_bits=PROGRESSIVE_BITS,
)

INDICES_PAYLOAD = "0x010000000000000002000000000000000300000000000000"
BOUNDED_INDICES_ROOT = "0xed114baf42aac42d5c115ed017862e26138544d8e8fbd9b58466da9dfa0b2f55"
PROGRESSIVE_INDICES_ROOT = "0x7e0adeccea8b17f07c3d1531a414d0b1f25543d5ddd519604ce30d5af83b1859"

EMPTY_PAYLOAD = "0x"
EMPTY_BOUNDED_INDICES_ROOT = "0x28ba1834a3a7b657460ce79fa3a1d909ab8828fd557659d4d0554a9bdbc0ec30"
EMPTY_PROGRESSIVE_INDICES_ROOT = (
    "0xf5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
)

BITS_PAYLOAD = "0x2d03"
BOUNDED_BITS_ROOT = "0xa8765ed64f47f80966b0f8f369f2b8ba9f054968ae8676392280b148ac503409"
PROGRESSIVE_BITS_ROOT = "0x51efd1ea949ac906bed4b4316689f9524e5dd44e886b8bf09207ea2c03ebaf49"

EMPTY_BITS_PAYLOAD = "0x01"
EMPTY_BOUNDED_BITS_ROOT = "0xe8e527e84f666163a90ef900e013f56b0a4d020148b2224057b719f351b003a6"
EMPTY_PROGRESSIVE_BITS_ROOT = "0xf5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"

NESTED_PAYLOAD = "0x0c000000100000001000000001000200030004000500"
BOUNDED_NESTED_ROOT = "0x29c0d2b5c5ce86600acb444184276acbabd3d4ce0b35112a61dab84128a41a6e"
PROGRESSIVE_NESTED_ROOT = "0xd77cae5a5c1c9abf94c554bf3136fe87d08a3bf1b0b6269c3fd842e3126d9e8a"

BODY_PAYLOAD = (
    "0x341200000000000010000000280000000100000000000000020000000000000003000000000000002d03"
)
BOUNDED_BODY_ROOT = "0xc68b1dd24f55b5794187a1883cfe280bb18af5b6dacdf5b0c2403ab02acdccd7"
PROGRESSIVE_BODY_ROOT = "0x42073831a2fbde48a19c8123ccc0a71852e5f9dc989b5ba0273a36ef5609ee81"


def test_bounded_list_of_uint64(ssz_test: SSZTestFiller) -> None:
    """
    A bounded list of eight-byte elements, against the progressive list beside it.

    Given
    -----
    - a list of capacity sixteen holding the three elements 1, 2 and 3.
    - a progressive list over that same element type holding those same three.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the 24 bytes 0x010000000000000002000000000000000300000000000000.
    - the progressive list beside this one writes those very same 24 bytes, which is what
      EIP-7688 means by a conversion that leaves serialization unchanged.
    - either type decodes the other's bytes, there being only one payload between them.
    - only the root separates the two, the capacity being all that shapes the tree here.
    """
    check_one_payload_two_roots(
        BOUNDED_INDICES,
        PROGRESSIVE_INDICES,
        INDICES_PAYLOAD,
        BOUNDED_INDICES_ROOT,
        PROGRESSIVE_INDICES_ROOT,
    )
    ssz_test(
        case_id="conversion/uint64_list/bounded",
        type_name="ConversionUint64List16",
        value=BOUNDED_INDICES,
    )


def test_progressive_list_of_uint64(ssz_test: SSZTestFiller) -> None:
    """
    The progressive twin of that bounded list, over the same three elements.

    Given
    -----
    - a progressive list of eight-byte elements holding 1, 2 and 3.
    - the bounded list of capacity sixteen beside it, holding those same three.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the same 24 bytes the bounded list writes.
    - the root differs from the bounded list's: the bounded tree pads to the four chunks its
      capacity needs, and the progressive spine grows to the one chunk the data fills.
    - a fork widening the capacity this way is therefore free on the wire and visible in the root.
    """
    check_one_payload_two_roots(
        BOUNDED_INDICES,
        PROGRESSIVE_INDICES,
        INDICES_PAYLOAD,
        BOUNDED_INDICES_ROOT,
        PROGRESSIVE_INDICES_ROOT,
    )
    ssz_test(
        case_id="conversion/uint64_list/progressive",
        type_name="ConversionUint64ProgressiveList",
        value=PROGRESSIVE_INDICES,
    )


def test_bounded_list_at_a_second_capacity(ssz_test: SSZTestFiller) -> None:
    """
    That same value under a second capacity, which the encoding is blind to.

    Given
    -----
    - a list of capacity eight holding the same three elements 1, 2 and 3.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the same 24 bytes both other shapes write, so a declared capacity
      contributes no byte to a payload.
    - the root here equals the progressive list's, two chunks of capacity padding to the same
      pair of nodes the spine's first level and terminator make.
    - so a conversion is not always visible in the root, and a consumer must not read a moved
      root as the signal that one happened.
    """
    check_one_payload_one_root(
        NARROWER_BOUNDED_INDICES,
        PROGRESSIVE_INDICES,
        INDICES_PAYLOAD,
        PROGRESSIVE_INDICES_ROOT,
    )
    ssz_test(
        case_id="conversion/uint64_list/bounded_at_a_second_capacity",
        type_name="ConversionUint64List8",
        value=NARROWER_BOUNDED_INDICES,
    )


@pytest.mark.tags("empty")
def test_empty_bounded_list_of_uint64(ssz_test: SSZTestFiller) -> None:
    """
    An empty bounded list, against the empty progressive list beside it.

    Given
    -----
    - a list of capacity sixteen holding no elements.
    - a progressive list over that same element type holding none either.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is empty.
    - the progressive list beside this one encodes to nothing as well.
    - the two roots still differ, both mixing in a count of zero over trees of different
      shapes: four zeroed chunks here, and a bare zero node there.
    """
    check_one_payload_two_roots(
        EMPTY_BOUNDED_INDICES,
        EMPTY_PROGRESSIVE_INDICES,
        EMPTY_PAYLOAD,
        EMPTY_BOUNDED_INDICES_ROOT,
        EMPTY_PROGRESSIVE_INDICES_ROOT,
    )
    ssz_test(
        case_id="conversion/uint64_list/empty/bounded",
        type_name="ConversionUint64List16",
        value=EMPTY_BOUNDED_INDICES,
    )


@pytest.mark.tags("empty")
def test_empty_progressive_list_of_uint64(ssz_test: SSZTestFiller) -> None:
    """
    The empty progressive twin, against the empty bounded list.

    Given
    -----
    - a progressive list of eight-byte elements holding no elements.
    - the bounded list of capacity sixteen beside it, holding none either.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is empty, exactly as the bounded list's is.
    - the root differs from the bounded list's, so the two are told apart on a payload that
      carries nothing at all.
    """
    check_one_payload_two_roots(
        EMPTY_BOUNDED_INDICES,
        EMPTY_PROGRESSIVE_INDICES,
        EMPTY_PAYLOAD,
        EMPTY_BOUNDED_INDICES_ROOT,
        EMPTY_PROGRESSIVE_INDICES_ROOT,
    )
    ssz_test(
        case_id="conversion/uint64_list/empty/progressive",
        type_name="ConversionUint64ProgressiveList",
        value=EMPTY_PROGRESSIVE_INDICES,
    )


def test_bounded_bitlist(ssz_test: SSZTestFiller) -> None:
    """
    A bounded bitlist at the committee size, against the progressive bitlist beside it.

    Given
    -----
    - a bitlist of capacity 2048 holding the nine bits 1, 0, 1, 1, 0, 1, 0, 0, 1.
    - a progressive bitlist holding those same nine.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the two bytes 0x2d03, the ninth bit and the delimiter above it.
    - the progressive bitlist beside this one writes those very same two bytes.
    - only the root separates the two, the capacity being all that shapes the tree here.
    """
    check_one_payload_two_roots(
        BOUNDED_BITS,
        PROGRESSIVE_BITS,
        BITS_PAYLOAD,
        BOUNDED_BITS_ROOT,
        PROGRESSIVE_BITS_ROOT,
    )
    ssz_test(
        case_id="conversion/bitlist/bounded",
        type_name="ConversionBitList2048",
        value=BOUNDED_BITS,
    )


def test_progressive_bitlist(ssz_test: SSZTestFiller) -> None:
    """
    The progressive twin of that bounded bitlist, over the same nine bits.

    Given
    -----
    - a progressive bitlist holding the nine bits 1, 0, 1, 1, 0, 1, 0, 0, 1.
    - the bitlist of capacity 2048 beside it, holding those same nine.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the same two bytes 0x2d03 the bounded bitlist writes.
    - the root differs from the bounded bitlist's: eight chunks of padded capacity there
      against one occupied spine level here.
    """
    check_one_payload_two_roots(
        BOUNDED_BITS,
        PROGRESSIVE_BITS,
        BITS_PAYLOAD,
        BOUNDED_BITS_ROOT,
        PROGRESSIVE_BITS_ROOT,
    )
    ssz_test(
        case_id="conversion/bitlist/progressive",
        type_name="ProgressiveBitList",
        value=PROGRESSIVE_BITS,
    )


@pytest.mark.tags("empty")
def test_empty_bounded_bitlist(ssz_test: SSZTestFiller) -> None:
    """
    An empty bounded bitlist, against the empty progressive bitlist beside it.

    Given
    -----
    - a bitlist of capacity 2048 holding no data bits.
    - a progressive bitlist holding none either.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the single delimiter byte 0x01.
    - the progressive bitlist beside this one writes that same byte.
    - the two roots still differ, both mixing in a count of zero over trees of different shapes.
    """
    check_one_payload_two_roots(
        EMPTY_BOUNDED_BITS,
        EMPTY_PROGRESSIVE_BITS,
        EMPTY_BITS_PAYLOAD,
        EMPTY_BOUNDED_BITS_ROOT,
        EMPTY_PROGRESSIVE_BITS_ROOT,
    )
    ssz_test(
        case_id="conversion/bitlist/empty/bounded",
        type_name="ConversionBitList2048",
        value=EMPTY_BOUNDED_BITS,
    )


@pytest.mark.tags("empty")
def test_empty_progressive_bitlist(ssz_test: SSZTestFiller) -> None:
    """
    The empty progressive twin, against the empty bounded bitlist.

    Given
    -----
    - a progressive bitlist holding no data bits.
    - the bitlist of capacity 2048 beside it, holding none either.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the single delimiter byte 0x01, exactly as the bounded bitlist's is.
    - the root differs from the bounded bitlist's, so the bare delimiter still tells the
      two shapes apart.
    """
    check_one_payload_two_roots(
        EMPTY_BOUNDED_BITS,
        EMPTY_PROGRESSIVE_BITS,
        EMPTY_BITS_PAYLOAD,
        EMPTY_BOUNDED_BITS_ROOT,
        EMPTY_PROGRESSIVE_BITS_ROOT,
    )
    ssz_test(
        case_id="conversion/bitlist/empty/progressive",
        type_name="ProgressiveBitList",
        value=EMPTY_PROGRESSIVE_BITS,
    )


def test_bounded_list_of_variable_size_elements(ssz_test: SSZTestFiller) -> None:
    """
    A bounded list behind an offset table, against the progressive list beside it.

    Given
    -----
    - a list of capacity four holding three inner lists of two-byte elements.
    - inner lists of widths two, zero and three, the element type held fixed across the pair.
    - a progressive list over that same inner type holding those same three.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding opens with a three-entry offset table, then the three bodies.
    - the progressive list beside this one writes those very same 22 bytes, offset table
      included, an offset being counted from the runtime element count and never the capacity.
    - only the root separates the two.
    """
    check_one_payload_two_roots(
        BOUNDED_NESTED,
        PROGRESSIVE_NESTED,
        NESTED_PAYLOAD,
        BOUNDED_NESTED_ROOT,
        PROGRESSIVE_NESTED_ROOT,
    )
    ssz_test(
        case_id="conversion/nested_list/bounded",
        type_name="ConversionNestedList4",
        value=BOUNDED_NESTED,
    )


def test_progressive_list_of_variable_size_elements(ssz_test: SSZTestFiller) -> None:
    """
    The progressive twin over those same variable-size elements.

    Given
    -----
    - a progressive list holding three inner lists of widths two, zero and three.
    - the bounded list of capacity four beside it, holding those same three.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the same 22 bytes the bounded list writes, table and bodies alike.
    - the root differs from the bounded list's, the element roots sitting on a spine here
      rather than in a tree padded to four leaves.
    """
    check_one_payload_two_roots(
        BOUNDED_NESTED,
        PROGRESSIVE_NESTED,
        NESTED_PAYLOAD,
        BOUNDED_NESTED_ROOT,
        PROGRESSIVE_NESTED_ROOT,
    )
    ssz_test(
        case_id="conversion/nested_list/progressive",
        type_name="ConversionNestedProgressiveList",
        value=PROGRESSIVE_NESTED,
    )


def test_container_before_the_conversion(ssz_test: SSZTestFiller) -> None:
    """
    A container over the pre-conversion field types, against the converted one beside it.

    Given
    -----
    - a container holding a slot, a bounded list of indices and a bounded bitlist.
    - the same container with both capacities dropped, holding the same three field values.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the slot, two offsets, then the indices and the aggregation bits.
    - the converted container beside this one writes those very same 42 bytes, which is the
      fork step EIP-7688 describes: a node's payload is unchanged across it.
    - the root differs, so a verifier holding one root can tell which side of the fork it is on.
    """
    check_one_payload_two_roots(
        BOUNDED_BODY,
        PROGRESSIVE_BODY,
        BODY_PAYLOAD,
        BOUNDED_BODY_ROOT,
        PROGRESSIVE_BODY_ROOT,
    )
    ssz_test(
        case_id="conversion/container/bounded",
        type_name="ConversionBodyBounded",
        value=BOUNDED_BODY,
    )


def test_container_after_the_conversion(ssz_test: SSZTestFiller) -> None:
    """
    The converted container, over those same three field values.

    Given
    -----
    - a container holding a slot, a progressive list of indices and a progressive bitlist.
    - the pre-conversion container beside it, holding the same three field values.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the same 42 bytes the pre-conversion container writes.
    - the root differs, both fields having moved to a progressive tree while the container's
      own layout stayed put.
    - so the conversion costs nothing on the wire and everything downstream of a root.
    """
    check_one_payload_two_roots(
        BOUNDED_BODY,
        PROGRESSIVE_BODY,
        BODY_PAYLOAD,
        BOUNDED_BODY_ROOT,
        PROGRESSIVE_BODY_ROOT,
    )
    ssz_test(
        case_id="conversion/container/progressive",
        type_name="ConversionBodyProgressive",
        value=PROGRESSIVE_BODY,
    )
