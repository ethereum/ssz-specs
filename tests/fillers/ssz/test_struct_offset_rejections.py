"""SSZ conformance test vectors for the offset table of a vector and of a container."""

from typing import ClassVar

import pytest

from ssz import Container, List, Uint8, Uint16, Uint32, Vector
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("offsets")


class SampleUint16List4(List[Uint16]):
    """Bounded list of two-byte elements, used only as something variable-size to point at."""

    LIMIT: ClassVar[int] = 4


class SampleListVector3(Vector[SampleUint16List4]):
    """Three variable-size elements, so the encoding opens with a table of three offsets."""

    LENGTH: ClassVar[int] = 3


class SampleSpacedFields(Container):
    """A fixed field before the variable ones and another between them."""

    head: Uint8
    first: SampleUint16List4
    middle: Uint32
    second: SampleUint16List4


SPACED_FIELDS = SampleSpacedFields(
    head=Uint8(0xFF),
    first=SampleUint16List4(),
    middle=Uint32(0xDDCCBBAA),
    second=SampleUint16List4(),
)
"""One value of that shape, present only to name the decoder every container case runs."""


def test_vector_budget_below_offset_table(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a vector into a budget too small to hold its offset table is rejected.

    Given
    -----
    - a vector of three variable-size elements, whose table spans twelve bytes.
    - the input bytes 0x0c0000000c000000, which hold two of the three entries.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget is below the width the declared count fixes.
    - the budget is settled before the table is read, so no entry is looked at.
    """
    ssz_test(
        case_id="list_vector3/invalid/budget_below_offset_table",
        type_name="SampleListVector3",
        value=SampleListVector3(),
        raw_bytes="0x0c0000000c000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="SampleListVector3 needs at least 12 bytes, and the budget is 8",
        ),
    )


def test_vector_first_offset_below_table(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a vector whose first offset points inside its own table is rejected.

    Given
    -----
    - a vector of three variable-size elements, whose table spans twelve bytes.
    - a first offset of eight, which lands on the third entry of that table.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset must be the table's width exactly.
    - a list reads the same offset as a count of two, and a declared count admits no such reading.
    """
    ssz_test(
        case_id="list_vector3/invalid/first_offset_below_table",
        type_name="SampleListVector3",
        value=SampleListVector3(),
        raw_bytes="0x080000000c0000000c000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="the first offset is 8, and the fixed part ends at 12",
        ),
    )


def test_vector_first_offset_above_table(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a vector whose first offset skips past its own table is rejected.

    Given
    -----
    - a vector of three variable-size elements, whose table spans twelve bytes.
    - a first offset of sixteen, leaving four bytes belonging to no element.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset must be the table's width exactly.
    - the rest of the table closes over the budget, so only the gap is at fault.
    """
    ssz_test(
        case_id="list_vector3/invalid/first_offset_above_table",
        type_name="SampleListVector3",
        value=SampleListVector3(),
        raw_bytes="0x10000000100000001000000000000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="the first offset is 16, and the fixed part ends at 12",
        ),
    )


def test_vector_offsets_unordered(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a vector whose offsets descend is rejected.

    Given
    -----
    - a vector of three variable-size elements, opening on a first offset of twelve.
    - a second offset of sixteen and a third of fourteen, so the table turns back.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that an offset stands above the one after it.
    - the position of the offending offset prefixes the refusal.
    """
    ssz_test(
        case_id="list_vector3/invalid/offsets_unordered",
        type_name="SampleListVector3",
        value=SampleListVector3(),
        raw_bytes="0x0c000000100000000e00000011112222",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_UNORDERED,
            exact_message="[1]: offset 16 is above the offset after it, 14",
        ),
    )


def test_vector_last_offset_past_budget(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a vector whose last offset runs past the budget is rejected.

    Given
    -----
    - a vector of three variable-size elements, in a budget of sixteen bytes.
    - an ascending table of twelve, sixteen and twenty, whose last entry is outside.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the last offset runs past the budget that closes the table.
    - the table ascends, so the budget is the only boundary it breaks.
    """
    ssz_test(
        case_id="list_vector3/invalid/last_offset_past_budget",
        type_name="SampleListVector3",
        value=SampleListVector3(),
        raw_bytes="0x0c000000100000001400000011112222",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_PAST_SCOPE,
            exact_message="[2]: offset 20 runs past the budget of 16",
        ),
    )


def test_container_budget_below_fixed_part(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a container into a budget too small to hold its fixed part is rejected.

    Given
    -----
    - a container whose fixed part is thirteen bytes, two of them offsets.
    - a budget of twelve bytes, one short of that fixed part.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the fixed part alone does not fit the budget.
    - reading the fixed part anyway would take a byte belonging to whatever follows.
    """
    ssz_test(
        case_id="spaced_fields/invalid/budget_below_fixed_part",
        type_name="SampleSpacedFields",
        value=SPACED_FIELDS,
        raw_bytes="0xff0d000000aabbccdd0d0000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="SampleSpacedFields needs at least 13 bytes, and the budget is 12",
        ),
    )


def test_container_first_offset_below_fixed_part(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a container whose first offset points inside its fixed part is rejected.

    Given
    -----
    - a container whose fixed part is thirteen bytes, two of them offsets.
    - a first offset of twelve, which lands on the last byte of the second offset.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset must end the fixed part exactly.
    - the refusal is about the table, not about a field, so it carries no field name.
    """
    ssz_test(
        case_id="spaced_fields/invalid/first_offset_below_fixed_part",
        type_name="SampleSpacedFields",
        value=SPACED_FIELDS,
        raw_bytes="0xff0c000000aabbccdd0d000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="the first offset is 12, and the fixed part ends at 13",
        ),
    )


def test_container_first_offset_above_fixed_part(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a container whose first offset skips past its fixed part is rejected.

    Given
    -----
    - a container whose fixed part is thirteen bytes, two of them offsets.
    - a first offset of fourteen, leaving a byte belonging to no field.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the first offset must end the fixed part exactly.
    - both offsets agree on fourteen, so only the gap before them is at fault.
    """
    ssz_test(
        case_id="spaced_fields/invalid/first_offset_above_fixed_part",
        type_name="SampleSpacedFields",
        value=SPACED_FIELDS,
        raw_bytes="0xff0e000000aabbccdd0e00000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="the first offset is 14, and the fixed part ends at 13",
        ),
    )


def test_container_offsets_unordered(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a container whose second offset falls below the first is rejected.

    Given
    -----
    - a container whose fixed part is thirteen bytes, two of them offsets.
    - a first offset of thirteen, which is where the fixed part ends.
    - a second offset of twelve, so the second field would begin before the first.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that an offset stands above the one after it.
    - the name of the field holding the offending offset prefixes the refusal.
    """
    ssz_test(
        case_id="spaced_fields/invalid/offsets_unordered",
        type_name="SampleSpacedFields",
        value=SPACED_FIELDS,
        raw_bytes="0xff0d000000aabbccdd0c00000011112222",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_UNORDERED,
            exact_message="first: offset 13 is above the offset after it, 12",
        ),
    )


def test_container_last_offset_past_budget(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a container whose last offset runs past the budget is rejected.

    Given
    -----
    - a container whose fixed part is thirteen bytes, in a budget of seventeen.
    - a first offset of thirteen, and a second of twenty-one, four bytes outside.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the last offset runs past the budget that closes the table.
    - the name of the field holding the offending offset prefixes the refusal.
    """
    ssz_test(
        case_id="spaced_fields/invalid/last_offset_past_budget",
        type_name="SampleSpacedFields",
        value=SPACED_FIELDS,
        raw_bytes="0xff0d000000aabbccdd1500000011112222",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.OFFSET_PAST_SCOPE,
            exact_message="second: offset 21 runs past the budget of 17",
        ),
    )
