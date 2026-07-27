"""SSZ smoke test for the decode-failure fixture path."""

from typing import ClassVar

from ssz import Bitlist, Boolean
from ssz_testing import ExpectedRejection, RejectionReason, SSZTestFiller


class SmokeBitlist8(Bitlist):
    """Small bitlist with an 8-bit limit, used only by the decode-failure smoke test."""

    LIMIT: ClassVar[int] = 8


def test_ssz_decode_failure_bitlist_exceeds_limit(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a bitlist whose contents imply too many bits is rejected.

    Given
    -----
    - a bitlist type capped at eight bits.
    - the input bytes 0x0010, which place the sentinel at bit sixteen.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the implied bit-length exceeds the limit.
    """
    ssz_test(
        type_name="SmokeBitlist8",
        value=SmokeBitlist8(data=[Boolean(False)]),
        raw_bytes="0x0010",
        expected_rejection=ExpectedRejection(reason=RejectionReason.DECODE_ERROR),
    )
