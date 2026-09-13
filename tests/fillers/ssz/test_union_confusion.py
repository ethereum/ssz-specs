"""SSZ conformance test vectors for one union option's payload read under another's selector."""

from typing import ClassVar, Final

import pytest

from ssz import ByteList, CompatibleUnion, ProgressiveContainer, Uint8, Uint32
from ssz.roots import hash_tree_root
from ssz_testing import ExpectedRejection, SSZTestFiller, ValueFault

pytestmark = pytest.mark.tags("union")


class CrossBlob4(ByteList):
    """Byte string capped at four bytes, the variable-size field every option below reaches."""

    LIMIT: ClassVar[int] = 4


class CrossMemo(ProgressiveContainer):
    """Option whose fixed part is an offset and a tag, five bytes before any data."""

    ACTIVE_FIELDS = (1, 0, 0, 1)

    memo: CrossBlob4
    tag: Uint8


class CrossMarkedMemo(ProgressiveContainer):
    """Option sharing only the tag, whose extra byte pushes the fixed part to six."""

    ACTIVE_FIELDS = (0, 1, 1, 1)

    body: CrossBlob4
    mark: Uint8
    tag: Uint8


class CrossMemoChoice(CompatibleUnion):
    """Union over two options whose encodings overlap in width but not in offset."""

    OPTIONS = {1: CrossMemo, 2: CrossMarkedMemo}


class CrossPlainRecord(ProgressiveContainer):
    """First option of the three, one blob and the shared tag, a fixed part of five."""

    ACTIVE_FIELDS = (1, 0, 0, 0, 0, 1)

    note: CrossBlob4
    tag: Uint8


class CrossStampedRecord(ProgressiveContainer):
    """Second option, a blob and a stamp byte before the shared tag, a fixed part of six."""

    ACTIVE_FIELDS = (0, 1, 1, 0, 0, 1)

    mark: CrossBlob4
    stamp: Uint8
    tag: Uint8


class CrossPairedRecord(ProgressiveContainer):
    """Third option, two blobs and the shared tag, a fixed part of nine."""

    ACTIVE_FIELDS = (0, 0, 0, 1, 1, 1)

    left: CrossBlob4
    right: CrossBlob4
    tag: Uint8


class CrossRecordChoice(CompatibleUnion):
    """Union over the three, the third under the selector its own first offset spells."""

    OPTIONS = {1: CrossPlainRecord, 2: CrossStampedRecord, 9: CrossPairedRecord}


class CrossOffsetNote(ProgressiveContainer):
    """Variable-size option whose five-byte encoding opens with an offset word."""

    ACTIVE_FIELDS = (1, 0, 1)

    text: CrossBlob4
    tag: Uint8


class CrossWordNote(ProgressiveContainer):
    """Fixed-size option whose five-byte encoding opens with a four-byte integer."""

    ACTIVE_FIELDS = (0, 1, 1)

    word: Uint32
    tag: Uint8


class CrossNoteOrWord(CompatibleUnion):
    """Union whose two options admit one and the same payload, an offset word or data."""

    OPTIONS = {1: CrossOffsetNote, 2: CrossWordNote}


SHARED_NOTE_PAYLOAD: Final = bytes.fromhex("0500000007")
"""The payload both options encode to, an empty blob one way and the number 5 the other."""

OFFSET_NOTE: Final = CrossNoteOrWord(
    selector=Uint8(1), data=CrossOffsetNote(text=CrossBlob4(data=b""), tag=Uint8(7))
)
"""That payload under the selector naming the variable-size option."""

WORD_NOTE: Final = CrossNoteOrWord(
    selector=Uint8(2), data=CrossWordNote(word=Uint32(5), tag=Uint8(7))
)
"""The same payload under the selector naming the fixed-size option."""


def check_one_payload_two_roots() -> None:
    """Check the two options encode alike and root apart, so only the selector separates them."""
    assert OFFSET_NOTE.data.encode_bytes() == SHARED_NOTE_PAYLOAD
    assert WORD_NOTE.data.encode_bytes() == SHARED_NOTE_PAYLOAD
    assert hash_tree_root(OFFSET_NOTE) != hash_tree_root(WORD_NOTE)


def test_union_confusion_first_option_payload_under_the_second_selector(
    ssz_test: SSZTestFiller,
) -> None:
    """
    Decoding one option's payload under another option's selector is rejected.

    Given
    -----
    - a union whose first option holds a blob and a tag, and whose second holds a blob,
      a mark byte and the same tag.
    - the bytes 0x0500000007aabb, which encode the first option holding a two-byte blob.
    - the input bytes 0x020500000007aabb, the same payload behind selector 2.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the first offset, which spells the fixed part of the option that wrote
      it rather than the fixed part of the option reading it.
    - seven payload bytes is a length the second option admits, so nothing but the offset
      rule separates this input from a valid one.
    """
    ssz_test(
        case_id="confusion/invalid/memo_payload_under_the_marked_selector",
        type_name="CrossMemoChoice",
        value=CrossMemoChoice(
            selector=Uint8(1),
            data=CrossMemo(memo=CrossBlob4(data=b"\xaa\xbb"), tag=Uint8(7)),
        ),
        raw_bytes="0x020500000007aabb",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="[2]: the first offset is 5, and the fixed part ends at 6",
        ),
    )


def test_union_confusion_second_option_payload_under_the_first_selector(
    ssz_test: SSZTestFiller,
) -> None:
    """
    The confusion is rejected in the other direction too.

    Given
    -----
    - the same union.
    - the bytes 0x06000000ee07aa, which encode the second option holding a one-byte blob.
    - the input bytes 0x0106000000ee07aa, the same payload behind selector 1.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the offset the first option expects is smaller, not larger, so a decoder that only
      checked the offset against the budget would let this through.
    - both directions carry seven payload bytes, so neither is caught by a length check.
    """
    ssz_test(
        case_id="confusion/invalid/marked_payload_under_the_memo_selector",
        type_name="CrossMemoChoice",
        value=CrossMemoChoice(
            selector=Uint8(2),
            data=CrossMarkedMemo(body=CrossBlob4(data=b"\xaa"), mark=Uint8(0xEE), tag=Uint8(7)),
        ),
        raw_bytes="0x0106000000ee07aa",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="[1]: the first offset is 6, and the fixed part ends at 5",
        ),
    )


def test_union_confusion_third_option_payload_under_the_second_selector(
    ssz_test: SSZTestFiller,
) -> None:
    """
    A union of three options confuses a pair the same way.

    Given
    -----
    - a union of three options, whose fixed parts end at five, six and nine bytes.
    - the bytes 0x090000000900000007aa, which encode the third option holding an empty
      blob and a one-byte blob.
    - the input bytes 0x02090000000900000007aa, the same payload behind selector 2.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected on the first offset.
    - ten payload bytes is exactly what the second option spans holding a four-byte blob,
      so the confusion survives every check but the offset's.
    """
    ssz_test(
        case_id="confusion/invalid/paired_payload_under_the_stamped_selector",
        type_name="CrossRecordChoice",
        value=CrossRecordChoice(
            selector=Uint8(9),
            data=CrossPairedRecord(
                left=CrossBlob4(data=b""), right=CrossBlob4(data=b"\xaa"), tag=Uint8(7)
            ),
        ),
        raw_bytes="0x02090000000900000007aa",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="[2]: the first offset is 9, and the fixed part ends at 6",
        ),
    )


def test_union_confusion_second_option_payload_under_the_third_selector(
    ssz_test: SSZTestFiller,
) -> None:
    """
    That pair is refused in the other direction as well.

    Given
    -----
    - the same union of three.
    - the bytes 0x06000000ee07aabbccdd, which encode the second option holding a full
      four-byte blob.
    - the input bytes 0x0906000000ee07aabbccdd, the same payload behind selector 9.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected on the first offset.
    - ten payload bytes leaves the third option's own fixed part one data byte, so this
      input is the right length for the option it is read as.
    """
    ssz_test(
        case_id="confusion/invalid/stamped_payload_under_the_paired_selector",
        type_name="CrossRecordChoice",
        value=CrossRecordChoice(
            selector=Uint8(2),
            data=CrossStampedRecord(
                mark=CrossBlob4(data=b"\xaa\xbb\xcc\xdd"), stamp=Uint8(0xEE), tag=Uint8(7)
            ),
        ),
        raw_bytes="0x0906000000ee07aabbccdd",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="[9]: the first offset is 6, and the fixed part ends at 9",
        ),
    )


@pytest.mark.tags("empty", "element-minimum")
def test_union_confusion_selector_without_a_payload(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a selector byte carrying no payload at all is rejected.

    Given
    -----
    - the two-option union, whose first option spans at least five bytes.
    - the input bytes 0x01, a declared selector and nothing after it.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the option's own minimum width against an empty budget, so the refusal
      comes from the option and not from the union.
    - the union itself is satisfied, the selector byte being present and declared.
    """
    ssz_test(
        case_id="confusion/invalid/selector_without_a_payload",
        type_name="CrossMemoChoice",
        value=CrossMemoChoice(
            selector=Uint8(1),
            data=CrossMemo(memo=CrossBlob4(data=b""), tag=Uint8(7)),
        ),
        raw_bytes="0x01",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE_TOO_SMALL,
            exact_message="[1]: CrossMemo needs at least 5 bytes, and the budget is 0",
        ),
    )


def test_union_confusion_payload_without_its_selector(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a payload whose selector byte was dropped is rejected.

    Given
    -----
    - the union of three, whose third option is declared under selector 9 and whose fixed
      part also ends at nine bytes.
    - the input bytes 0x090000000900000007aa, that option's payload with no selector ahead
      of it.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - the low byte of the first offset is read as the selector, and it names the very
      option the payload belongs to, so the selector table does not catch the loss.
    - decoding is rejected one step later, the remaining bytes reading as an offset of
      150994944 against a fixed part ending at nine.
    - a union declaring a selector that a first offset can spell is what makes a dropped
      selector byte survive this far.
    """
    ssz_test(
        case_id="confusion/invalid/payload_without_its_selector",
        type_name="CrossRecordChoice",
        value=CrossRecordChoice(
            selector=Uint8(9),
            data=CrossPairedRecord(
                left=CrossBlob4(data=b""), right=CrossBlob4(data=b"\xaa"), tag=Uint8(7)
            ),
        ),
        raw_bytes="0x090000000900000007aa",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.FIRST_OFFSET,
            exact_message="[9]: the first offset is 150994944, and the fixed part ends at 9",
        ),
    )


def test_union_confusion_shared_payload_under_the_offset_selector(
    ssz_test: SSZTestFiller,
) -> None:
    """
    A payload both options admit is accepted under the first of them.

    Given
    -----
    - a union whose first option is variable-size, five bytes when its blob is empty, and
      whose second is fixed at five bytes.
    - a value holding the first option with an empty blob.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the payload is 0x0500000007, an offset of 5 followed by the tag.
    - those same five bytes are a valid encoding of the other option, so this is not a
      confusion a decoder can refuse.
    - the two readings root differently, which is what the selector byte is for.
    """
    check_one_payload_two_roots()
    ssz_test(
        case_id="confusion/shared_payload/offset_option",
        type_name="CrossNoteOrWord",
        value=OFFSET_NOTE,
    )


def test_union_confusion_shared_payload_under_the_word_selector(
    ssz_test: SSZTestFiller,
) -> None:
    """
    The same payload is accepted under the other option too.

    Given
    -----
    - the same union.
    - a value holding the second option, whose four-byte integer is 5.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the payload is 0x0500000007 again, the bytes the other option spends on an offset
      read here as data.
    - the root differs from the same payload under selector 1, so nothing is lost by both
      readings being legal.
    - only a decoder that ignored the selector could confuse the two.
    """
    check_one_payload_two_roots()
    ssz_test(
        case_id="confusion/shared_payload/word_option",
        type_name="CrossNoteOrWord",
        value=WORD_NOTE,
    )
