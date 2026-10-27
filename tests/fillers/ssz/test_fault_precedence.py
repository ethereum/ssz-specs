"""SSZ conformance test vectors for struct encodings breaking more than one rule at once."""

import pytest

from ssz import Boolean, ByteList, Container, ProgressiveContainer
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("offsets")


class SampleByteList1(ByteList):
    """Byte list holding at most one byte, so a two-byte body breaks its limit."""

    LIMIT = 1


class SampleFlagThenBytes(Container):
    """A fixed field ahead of the only offset."""

    flag: Boolean
    data: SampleByteList1


class SampleBytesThenFlag(Container):
    """A fixed field behind the only offset."""

    data: SampleByteList1
    flag: Boolean


class SampleProgressiveFlagThenBytes(ProgressiveContainer):
    """A fixed field ahead of the only offset, each field merkleized at its own position."""

    ACTIVE_FIELDS = (1, 1)

    flag: Boolean
    data: SampleByteList1


FLAG_THEN_BYTES = SampleFlagThenBytes(flag=Boolean(False), data=SampleByteList1())
"""One value of that shape, present only to name the decoder its cases run."""

BYTES_THEN_FLAG = SampleBytesThenFlag(data=SampleByteList1(), flag=Boolean(False))
"""One value of that shape, present only to name the decoder its case runs."""

PROGRESSIVE_FLAG_THEN_BYTES = SampleProgressiveFlagThenBytes(
    flag=Boolean(False), data=SampleByteList1()
)
"""One value of that shape, present only to name the decoder its case runs."""


def test_fixed_field_before_first_offset(ssz_test: SSZTestFiller) -> None:
    """
    A broken fixed field is refused ahead of a broken first offset.

    Given
    -----
    - a container of a boolean and then an offset, so its fixed part is five bytes.
    - the input bytes 0x0200000000.
    - the boolean byte is 0x02, which is no bit.
    - the offset is zero, which does not end the fixed part.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the boolean, since the fixed part is read before any offset is checked.
    """
    ssz_test(
        case_id="flag_then_bytes/invalid/fixed_field_before_first_offset",
        type_name="SampleFlagThenBytes",
        value=FLAG_THEN_BYTES,
        raw_bytes="0x0200000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NOT_A_BIT,
            exact_message="flag: a boolean is 0 or 1, got 0x02",
        ),
    )


def test_budget_before_fixed_field(ssz_test: SSZTestFiller) -> None:
    """
    A budget too small for the fixed part is refused ahead of a broken fixed field.

    Given
    -----
    - a container of a boolean and then an offset, so its fixed part is five bytes.
    - the input bytes 0x02000000, one byte short of that fixed part.
    - the boolean byte is 0x02, which is no bit.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the budget, since it is settled before any field is read.
    """
    ssz_test(
        case_id="flag_then_bytes/invalid/budget_before_fixed_field",
        type_name="SampleFlagThenBytes",
        value=FLAG_THEN_BYTES,
        raw_bytes="0x02000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="SampleFlagThenBytes needs at least 5 bytes, and the budget is 4",
        ),
    )


def test_fixed_field_before_earlier_body(ssz_test: SSZTestFiller) -> None:
    """
    A broken fixed field is refused ahead of a broken body declared before it.

    Given
    -----
    - a container of an offset and then a boolean, so its fixed part is five bytes.
    - the input bytes 0x05000000020909.
    - the offset is five, which ends the fixed part.
    - the boolean byte is 0x02, which is no bit.
    - the body is two bytes, past the one-byte limit of its list.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the boolean, since every fixed field is read before any body.
    """
    ssz_test(
        case_id="bytes_then_flag/invalid/fixed_field_before_earlier_body",
        type_name="SampleBytesThenFlag",
        value=BYTES_THEN_FLAG,
        raw_bytes="0x05000000020909",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NOT_A_BIT,
            exact_message="flag: a boolean is 0 or 1, got 0x02",
        ),
    )


def test_progressive_fixed_field_before_first_offset(ssz_test: SSZTestFiller) -> None:
    """
    A progressive container refuses a broken fixed field ahead of a broken first offset.

    Given
    -----
    - a progressive container of a boolean and then an offset, so its fixed part is five bytes.
    - the input bytes 0x0200000000.
    - the boolean byte is 0x02, which is no bit.
    - the offset is zero, which does not end the fixed part.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the boolean, as for a container, since both encode alike.
    """
    ssz_test(
        case_id="progressive_flag_then_bytes/invalid/fixed_field_before_first_offset",
        type_name="SampleProgressiveFlagThenBytes",
        value=PROGRESSIVE_FLAG_THEN_BYTES,
        raw_bytes="0x0200000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NOT_A_BIT,
            exact_message="flag: a boolean is 0 or 1, got 0x02",
        ),
    )
