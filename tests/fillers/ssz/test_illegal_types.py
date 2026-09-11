"""SSZ conformance test vectors for the type declarations the specification calls illegal."""

from typing import Final

import pytest

from ssz import Uint8, Uint16
from ssz_testing import (
    DeclaredField,
    DeclaredOption,
    TypeDescriptor,
    TypeFault,
    TypeRejectionFiller,
    describe_type,
)

pytestmark = pytest.mark.tags("illegal")

UINT8: Final = describe_type(Uint8)
"""A byte-wide integer, read off the real class, every legal part of a declaration being one."""

UINT16: Final = describe_type(Uint16)
"""A two-byte integer, the other half of a union whose options merkleize differently."""

ONE_FIELD: Final = (DeclaredField(name="amount", type=UINT8),)
"""A single named field, enough to give a struct the one thing a layout is counted against."""


def test_a_vector_of_zero_elements_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a vector whose length is zero is refused.

    Given
    -----
    - a vector of bytes declaring a length of zero.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, an exact count of zero pinning the shape to holding nothing.
    - such a shape spans no bytes, so any number of its values sit at one place in an
      encoding, and nothing recovers how many were there.
    """
    ssz_type_rejection(
        case_id="illegal/vector/zero_length",
        type_name="IllegalZeroLengthVector",
        type_descriptor=TypeDescriptor(kind="Vector", length=0, element_type=UINT8),
        rejection_reason=TypeFault.VECTOR_EMPTY,
        exact_message=(
            "IllegalZeroLengthVector declares a length of zero, and a fixed count is at least one"
        ),
    )


def test_a_bitvector_of_zero_bits_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a bitvector whose length is zero is refused.

    Given
    -----
    - a bitvector declaring a length of zero.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, for the reason a zero-length vector is.
    - a bitvector of no bits would encode to no bytes, where every other bitvector
      encodes to at least one.
    """
    ssz_type_rejection(
        case_id="illegal/bit_vector/zero_length",
        type_name="IllegalZeroLengthBitVector",
        type_descriptor=TypeDescriptor(kind="BitVector", length=0),
        rejection_reason=TypeFault.VECTOR_EMPTY,
        exact_message=(
            "IllegalZeroLengthBitVector declares a length of zero, "
            "and a fixed count is at least one"
        ),
    )


def test_a_byte_vector_of_zero_bytes_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a byte vector whose length is zero is refused.

    Given
    -----
    - a byte vector declaring a length of zero.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, the third fixed-count shape reading like the other two.
    - an implementation keying its check on the kind, and not on the count, would let
      this one through where it refuses the vector.
    """
    ssz_type_rejection(
        case_id="illegal/byte_vector/zero_length",
        type_name="IllegalZeroLengthByteVector",
        type_descriptor=TypeDescriptor(kind="ByteVector", length=0),
        rejection_reason=TypeFault.VECTOR_EMPTY,
        exact_message=(
            "IllegalZeroLengthByteVector declares a length of zero, "
            "and a fixed count is at least one"
        ),
    )


def test_a_container_naming_no_field_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a container that names no field is refused.

    Given
    -----
    - a container whose field list is empty.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a struct of no fields spanning no bytes.
    - a list of such values has no count to recover from the bytes it was given.
    """
    ssz_type_rejection(
        case_id="illegal/container/no_fields",
        type_name="IllegalFieldlessContainer",
        type_descriptor=TypeDescriptor(kind="Container", fields=()),
        rejection_reason=TypeFault.CONTAINER_EMPTY,
        exact_message="a struct declares at least one field",
    )


def test_a_list_declaring_a_length_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a list that also pins an exact count is refused.

    Given
    -----
    - a list of bytes bounded at four, which also declares a length of two.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, an exact count being a vector's rule.
    - a list merkleizes from its bound and mixes in its own count, so a second count
      rule would name a tree the shape does not have.
    """
    ssz_type_rejection(
        case_id="illegal/list/declares_a_length",
        type_name="IllegalLengthBearingList",
        type_descriptor=TypeDescriptor(kind="List", limit=4, length=2, element_type=UINT8),
        rejection_reason=TypeFault.NOT_ENTITLED,
        exact_message="IllegalLengthBearingList declares a LENGTH its shape has none of",
    )


def test_a_vector_declaring_a_limit_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a vector that also carries a bound is refused.

    Given
    -----
    - a vector of four bytes, which also declares a limit of four.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, the bound being a list's rule.
    - the two agree here, and the declaration is refused anyway: a shape carries the
      one capacity it has, not every capacity it could be reconciled with.
    """
    ssz_type_rejection(
        case_id="illegal/vector/declares_a_limit",
        type_name="IllegalLimitBearingVector",
        type_descriptor=TypeDescriptor(kind="Vector", length=4, limit=4, element_type=UINT8),
        rejection_reason=TypeFault.NOT_ENTITLED,
        exact_message="IllegalLimitBearingVector declares a LIMIT its shape has none of",
    )


def test_a_progressive_list_declaring_a_length_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a progressive list that pins an exact count is refused.

    Given
    -----
    - a progressive list of bytes declaring a length of two.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, EIP-7916 giving this shape no capacity at all.
    - its tree grows with what it holds, so a declared count names no level of the spine.
    """
    ssz_type_rejection(
        case_id="illegal/progressive_list/declares_a_length",
        type_name="IllegalLengthBearingProgressiveList",
        type_descriptor=TypeDescriptor(kind="ProgressiveList", length=2, element_type=UINT8),
        rejection_reason=TypeFault.NOT_ENTITLED,
        exact_message="IllegalLengthBearingProgressiveList declares a LENGTH its shape has none of",
    )


def test_a_progressive_list_declaring_a_limit_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a progressive list that carries a bound is refused.

    Given
    -----
    - a progressive list of bytes declaring a limit of four.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, for the reason a declared length is.
    - both capacities are named separately, so an implementation refusing one and
      admitting the other is caught by exactly one of the two vectors.
    """
    ssz_type_rejection(
        case_id="illegal/progressive_list/declares_a_limit",
        type_name="IllegalLimitBearingProgressiveList",
        type_descriptor=TypeDescriptor(kind="ProgressiveList", limit=4, element_type=UINT8),
        rejection_reason=TypeFault.NOT_ENTITLED,
        exact_message="IllegalLimitBearingProgressiveList declares a LIMIT its shape has none of",
    )


def test_a_negative_capacity_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a list bounded at a negative number is refused.

    Given
    -----
    - a list of bytes declaring a limit of -1.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a capacity counting what a shape holds.
    - an implementation reading the bound into an unsigned word would see a bound of
      2**64 - 1 rather than a refusal.
    """
    ssz_type_rejection(
        case_id="illegal/list/negative_limit",
        type_name="IllegalNegativeLimitList",
        type_descriptor=TypeDescriptor(kind="List", limit=-1, element_type=UINT8),
        rejection_reason=TypeFault.CAPACITY_NEGATIVE,
        exact_message=(
            "IllegalNegativeLimitList.LIMIT counts what a shape holds, and -1 is not a count"
        ),
    )


def test_a_progressive_container_with_an_empty_layout_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a progressive container whose layout holds no position is refused.

    Given
    -----
    - a progressive container whose active fields are empty, naming no field either.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a layout placing at least one position.
    - this is the progressive counterpart of a field-less container, and it encodes to
      zero bytes the same way.
    """
    ssz_type_rejection(
        case_id="illegal/progressive_container/empty_layout",
        type_name="IllegalEmptyLayoutContainer",
        type_descriptor=TypeDescriptor(kind="ProgressiveContainer", active_fields=(), fields=()),
        rejection_reason=TypeFault.LAYOUT_WIDTH,
        exact_message="a field layout holds at least one position, got 0",
    )


def test_a_progressive_container_layout_ending_on_a_gap_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a progressive container whose layout ends on a gap is refused.

    Given
    -----
    - a progressive container with one field, laid out as (1, 0).

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a layout ending on a field.
    - (1, 0) and (1) place the one field alike and mix in different words, so a
      trailing gap is a second spelling of one shape.
    """
    ssz_type_rejection(
        case_id="illegal/progressive_container/layout_ends_on_a_gap",
        type_name="IllegalTrailingGapContainer",
        type_descriptor=TypeDescriptor(
            kind="ProgressiveContainer", active_fields=(1, 0), fields=ONE_FIELD
        ),
        rejection_reason=TypeFault.LAYOUT_TRAILING_GAP,
        exact_message="a field layout ends on a field, not on a gap",
    )


def test_a_progressive_container_layout_counting_wrong_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a progressive container whose set bits outnumber its fields is refused.

    Given
    -----
    - a progressive container with one field, laid out as (1, 0, 1).

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, the layout setting two positions against one declared field.
    - fields fill the set positions in declaration order, so a mismatch leaves a set
      position with nothing to merkleize at it.
    """
    ssz_type_rejection(
        case_id="illegal/progressive_container/layout_field_count",
        type_name="IllegalFieldCountContainer",
        type_descriptor=TypeDescriptor(
            kind="ProgressiveContainer", active_fields=(1, 0, 1), fields=ONE_FIELD
        ),
        rejection_reason=TypeFault.LAYOUT_FIELD_COUNT,
        exact_message="the layout sets 2 positions, and the struct declares 1",
    )


def test_a_progressive_container_layout_over_the_limit_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a progressive container whose layout is wider than the limit is refused.

    Given
    -----
    - a progressive container with one field at position 256, so a layout of 257 positions.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, EIP-7495 mixing the whole layout in as one 32-byte word.
    - 256 positions fit that word exactly, so the first position past it has nowhere
      in the root to be recorded.
    """
    ssz_type_rejection(
        case_id="illegal/progressive_container/layout_too_wide",
        type_name="IllegalOverWideContainer",
        type_descriptor=TypeDescriptor(
            kind="ProgressiveContainer", active_fields=(0,) * 256 + (1,), fields=ONE_FIELD
        ),
        rejection_reason=TypeFault.LAYOUT_TOO_WIDE,
        exact_message="a field layout holds 257 positions, over the limit of 256",
    )


def test_a_union_declaring_no_option_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a union that offers nothing is refused.

    Given
    -----
    - a union whose option list is empty.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a union declaring at least one option.
    - no byte string decodes into it, since every selector would name no option.
    """
    ssz_type_rejection(
        case_id="illegal/compatible_union/no_options",
        type_name="IllegalOptionlessUnion",
        type_descriptor=TypeDescriptor(kind="CompatibleUnion", options=()),
        rejection_reason=TypeFault.UNION_EMPTY,
        exact_message="a union declares at least one option",
    )


def test_a_union_selector_below_the_range_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a union option under selector zero is refused.

    Given
    -----
    - a union declaring one option under selector 0.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, EIP-8016 opening the selector range at 1.
    - an implementation carrying the older union, whose selectors start at 0, would
      accept this declaration.
    """
    ssz_type_rejection(
        case_id="illegal/compatible_union/selector_below_range",
        type_name="IllegalZeroSelectorUnion",
        type_descriptor=TypeDescriptor(
            kind="CompatibleUnion", options=(DeclaredOption(selector=0, type=UINT8),)
        ),
        rejection_reason=TypeFault.UNION_SELECTOR_RANGE,
        exact_message="selector 0 falls outside 1 through 127",
    )


def test_a_union_selector_above_the_range_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a union option under a selector past 127 is refused.

    Given
    -----
    - a union declaring one option under selector 200.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, EIP-8016 closing the selector range at 127.
    - a selector fits one byte either way, so only the reserved half of that byte
      separates this declaration from a legal one.
    """
    ssz_type_rejection(
        case_id="illegal/compatible_union/selector_above_range",
        type_name="IllegalHighSelectorUnion",
        type_descriptor=TypeDescriptor(
            kind="CompatibleUnion", options=(DeclaredOption(selector=200, type=UINT8),)
        ),
        rejection_reason=TypeFault.UNION_SELECTOR_RANGE,
        exact_message="selector 200 falls outside 1 through 127",
    )


def test_a_union_of_incompatible_options_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a union whose options merkleize differently is refused.

    Given
    -----
    - a union offering a one-byte integer under selector 1 and a two-byte one under 2.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a compatible union resting on every option sharing one tree shape.
    - both options merkleize to a single chunk, and the chunks hold different widths,
      so a proof against one would read as the other.
    """
    ssz_type_rejection(
        case_id="illegal/compatible_union/incompatible_options",
        type_name="IllegalMixedShapeUnion",
        type_descriptor=TypeDescriptor(
            kind="CompatibleUnion",
            options=(
                DeclaredOption(selector=1, type=UINT8),
                DeclaredOption(selector=2, type=UINT16),
            ),
        ),
        rejection_reason=TypeFault.UNION_INCOMPATIBLE,
        exact_message="options 1 and 2 merkleize differently",
    )
