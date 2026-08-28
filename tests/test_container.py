"""Tests for the SSZ Container base class and the EIP-7495 progressive container."""

import io
from collections.abc import Sequence
from typing import Any, cast

import pytest
from hypothesis import given, strategies as st
from pydantic import ValidationError

import ssz
from ssz.bitfields import ProgressiveBitList
from ssz.boolean import Boolean
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import (
    MAX_ACTIVE_FIELDS,
    Container,
    ProgressiveContainer,
    _SSZContainer,
    active_fields,
)
from ssz.exceptions import (
    SSZActiveFieldsError,
    SSZDefaultError,
    SSZDefinitionError,
    SSZSerializationError,
    SSZTypeError,
    SSZTypeMismatch,
    SSZValueError,
)
from ssz.merkleization import ZERO_ROOT, hash_tree_root, merkleize_progressive, mix_in_active_fields
from ssz.ssz_base import SSZType
from ssz.uint import Uint8, Uint16, Uint32, Uint64
from ssz.union import CompatibleUnion


class Uint16List4(List[Uint16]):
    """A list with up to 4 Uint16 values for variable-field testing."""

    LIMIT = 4


class TwoUint64(Container):
    """Two fixed-size Uint64 fields, total width 16 bytes."""

    a: Uint64
    b: Uint64


class TwoVar(Container):
    """Two variable-size list fields, total width is dynamic."""

    a: Uint16List4
    b: Uint16List4


class Mixed(Container):
    """Interleaved fixed and variable fields covering the canonical mixed shape."""

    a: Uint64
    b: Uint16List4
    c: Uint32
    d: Uint16List4


class OneVar(Container):
    """Single variable-size field, exercises the single-offset branch."""

    a: Uint16List4


class InnerFixed(Container):
    """Inner fixed-size container nested inside another container."""

    x: Uint64
    y: Uint64


class OuterFixedNested(Container):
    """Outer fixed-size container that holds a fixed-size container as a field."""

    z: Uint64
    inner: InnerFixed


class InnerVar(Container):
    """Inner variable-size container with one variable field."""

    a: Uint64
    b: Uint16List4


class OuterVarNested(Container):
    """Outer container that holds a variable-size container as a field."""

    head: Uint64
    inner: InnerVar


class Attestation(Container):
    """Parent container with a fixed slot and a variable data list."""

    slot: Uint64
    data: Uint16List4


class SignedAttestation(Attestation):
    """Subclass appending a signature field after the parent fields."""

    signature: Uint64


class EmptyContainer(Container):
    """Zero-field container, exercises the all-fixed sum over an empty iterator."""


class OneByte(Container):
    """Smallest non-empty fixed container, used for hex helpers."""

    a: Uint8


class HoldsANothingField(Container):
    """A field of no width at all, between fields that have one and a field that has none."""

    a: Uint8
    nothing: EmptyContainer
    b: Uint16List4
    c: Uint8


class Uint16ProgressiveList(ProgressiveList[Uint16]):
    """Progressive list of Uint16, used as a variable-size progressive-container field."""


class Square(ProgressiveContainer):
    """EIP-7495's own example: a field at position 0, a gap, then a field at position 2."""

    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16
    color: Uint8


class Circle(ProgressiveContainer):
    """The other half of the example: a leading gap, then fields at positions 1 and 2."""

    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16
    color: Uint8


class OneFieldProgressive(ProgressiveContainer):
    """Narrowest legal layout: a single position, occupied."""

    ACTIVE_FIELDS = (1,)

    a: Uint16


class LeadingGapProgressive(ProgressiveContainer):
    """Two leading gaps, so the only field is merkleized at position two."""

    ACTIVE_FIELDS = (0, 0, 1)

    c: Uint32


class MultiGapProgressive(ProgressiveContainer):
    """Three fields separated by gaps of differing widths."""

    ACTIVE_FIELDS = (1, 0, 0, 1, 0, 1)

    a: Uint8
    b: Uint16
    c: Uint32


class FixedPairProgressive(ProgressiveContainer):
    """Fixed-size-only progressive container, so the whole shape has a byte length."""

    ACTIVE_FIELDS = (1, 1)

    a: Uint64
    b: Uint32


class TwoUint64Progressive(ProgressiveContainer):
    """The progressive twin of TwoUint64, field for field, for a wire-format comparison."""

    ACTIVE_FIELDS = (1, 1)

    a: Uint64
    b: Uint64


class WideProgressive(ProgressiveContainer):
    """Widest legal layout: 256 positions, of which only the last is occupied."""

    ACTIVE_FIELDS = (*([0] * 255), 1)

    tail: Uint8


class ListFieldProgressive(ProgressiveContainer):
    """Fixed field, a gap, then a bounded list, so the shape needs one offset."""

    ACTIVE_FIELDS = (1, 0, 1)

    head: Uint64
    body: Uint16List4


class ProgressiveFieldsProgressive(ProgressiveContainer):
    """Both EIP-7916 shapes as fields, so two offsets follow the fixed part."""

    ACTIVE_FIELDS = (1, 1, 1)

    head: Uint32
    numbers: Uint16ProgressiveList
    flags: ProgressiveBitList


class InnerProgressive(ProgressiveContainer):
    """Fixed-size progressive container nested inside another one."""

    ACTIVE_FIELDS = (1, 0, 1)

    x: Uint16
    y: Uint8


class OuterProgressive(ProgressiveContainer):
    """Progressive container holding a progressive container as a field."""

    ACTIVE_FIELDS = (1, 0, 1)

    head: Uint8
    inner: InnerProgressive


class BuiltSquare(ProgressiveContainer):
    """The interior-gap example, with its layout built from a width and one gap."""

    ACTIVE_FIELDS = active_fields(width=3, gaps=(1,))

    side: Uint16
    color: Uint8


class BuiltCircle(ProgressiveContainer):
    """The leading-gap example, built from a gap at the lowest position."""

    ACTIVE_FIELDS = active_fields(width=3, gaps=(0,))

    radius: Uint16
    color: Uint8


class BuiltTwoLeadingGaps(ProgressiveContainer):
    """Two adjacent gaps ahead of the only field, built from a consecutive pair."""

    ACTIVE_FIELDS = active_fields(width=3, gaps=(0, 1))

    c: Uint32


class BuiltMultiGap(ProgressiveContainer):
    """Three fields split by an adjacent pair of gaps and then a lone gap."""

    ACTIVE_FIELDS = active_fields(width=6, gaps=(1, 2, 4))

    a: Uint8
    b: Uint16
    c: Uint32


class FourFieldOriginal(ProgressiveContainer):
    """A four-position shape before any fork touches it, every position occupied."""

    ACTIVE_FIELDS = active_fields(width=4)

    a: Uint16
    b: Uint16
    c: Uint16
    d: Uint16


class FourFieldSecondDropped(ProgressiveContainer):
    """The same shape after a fork drops the second field and records the vacancy."""

    # The width stays at 4 while the field list shrinks to 3.
    # That is what holds the last two fields at positions 2 and 3.
    ACTIVE_FIELDS = active_fields(width=4, gaps=(1,))

    a: Uint16
    c: Uint16
    d: Uint16


class WideForkEvolvedState(ProgressiveContainer):
    """
    Thirty fields over thirty-two positions, two of them vacated by earlier forks.

    Field widths are uniform at eight bytes.
    The whole shape is therefore 240 bytes.
    """

    ACTIVE_FIELDS = active_fields(width=32, gaps=(4, 19))

    genesis_time: Uint64
    genesis_validators_root: Uint64
    slot: Uint64
    fork_epoch: Uint64
    # Position 4 was vacated by a fork.
    latest_block_header_slot: Uint64
    latest_block_header_proposer: Uint64
    latest_block_header_parent_root: Uint64
    latest_block_header_state_root: Uint64
    latest_block_header_body_root: Uint64
    block_roots_root: Uint64
    state_roots_root: Uint64
    historical_roots_count: Uint64
    eth1_deposit_count: Uint64
    eth1_deposit_root: Uint64
    eth1_block_hash: Uint64
    eth1_deposit_index: Uint64
    validator_count: Uint64
    balances_root: Uint64
    # Position 19 was vacated by a later fork.
    randao_mixes_root: Uint64
    slashings_root: Uint64
    previous_epoch_participation_root: Uint64
    current_epoch_participation_root: Uint64
    justification_bits: Uint64
    previous_justified_epoch: Uint64
    current_justified_epoch: Uint64
    finalized_epoch: Uint64
    inactivity_scores_root: Uint64
    current_sync_committee_root: Uint64
    next_sync_committee_root: Uint64
    execution_payload_block_number: Uint64


MisplacedGapState = cast(
    "type[ProgressiveContainer]",
    type(
        "MisplacedGapState",
        (ProgressiveContainer,),
        {
            "__doc__": "The same thirty fields, with the second gap written one position late.",
            "ACTIVE_FIELDS": active_fields(width=32, gaps=(4, 20)),
            "__annotations__": dict.fromkeys(WideForkEvolvedState.model_fields, Uint64),
        },
    ),
)
"""The shape a misplaced gap declares: the counts still agree, and the fields move.

Built by hand rather than written out, so the two shapes cannot drift apart in their
fields, which is the one thing this shape must hold constant against the one above."""


class SquareList4(List[Square]):
    """Bounded list of progressive containers, four at most."""

    LIMIT = 4


class SquareProgressiveList(ProgressiveList[Square]):
    """Progressive list of progressive containers."""


class ContainerWithProgressive(Container):
    """Ordinary container holding a fixed-size progressive container."""

    tag: Uint8
    shape: Square


class ContainerWithVariableProgressive(Container):
    """Ordinary container holding a variable-size progressive container."""

    tag: Uint8
    shape: ListFieldProgressive


class InnerFixedVector2(Vector[InnerFixed]):
    """Vector of two fixed-size containers, held as a single container field below."""

    LENGTH = 2


class ContainerWithVectorOfContainers(Container):
    """Container whose second field is a vector of containers, so defaults nest twice."""

    tag: Uint8
    items: InnerFixedVector2


class TagUnion(CompatibleUnion):
    """Union over a single option, a type the spec gives no default value."""

    OPTIONS = {1: Uint8}


class ContainerWithUnion(Container):
    """Container whose second field is a union, so the struct inherits the missing default."""

    tag: Uint8
    body: TagUnion


class TestFixedContainer:
    """Fixed-size container metadata, encoding, and roundtrip behavior."""

    def test_is_fixed_size_true(self) -> None:
        """A container of only fixed-size fields reports as fixed-size."""
        assert TwoUint64.is_fixed_size() is True

    def test_get_byte_length_sums_field_widths(self) -> None:
        """The fixed byte width is the sum of each field's byte width."""
        assert TwoUint64.get_byte_length() == 16

    def test_serialize_writes_little_endian_fields(self) -> None:
        """Encoding concatenates each field's little-endian bytes in order."""
        encoded = TwoUint64(a=Uint64(1), b=Uint64(2)).encode_bytes()
        assert encoded == b"\x01\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00"

    @pytest.mark.parametrize(
        ("a", "b"),
        [
            pytest.param(0, 0, id="edge_zero"),
            pytest.param(1, 2, id="small"),
            pytest.param(0xDEADBEEF, 0xCAFEBABE, id="medium"),
            pytest.param(2**64 - 1, 2**64 - 1, id="large"),
        ],
    )
    def test_roundtrip_preserves_value(self, a: int, b: int) -> None:
        """Encoding then decoding recovers the original fixed container exactly."""
        original = TwoUint64(a=Uint64(a), b=Uint64(b))
        assert TwoUint64.decode_bytes(original.encode_bytes()) == original

    def test_empty_container_has_zero_byte_length(self) -> None:
        """A container with no fields has a fixed byte length of zero."""
        assert EmptyContainer.is_fixed_size() is True
        assert EmptyContainer.get_byte_length() == 0
        assert EmptyContainer().encode_bytes() == b""


class TestVariableContainer:
    """All-variable container shape and metadata."""

    def test_is_fixed_size_false(self) -> None:
        """A container with only variable-size fields reports as not fixed-size."""
        assert TwoVar.is_fixed_size() is False

    def test_get_byte_length_raises(self) -> None:
        """A variable-size container has no fixed byte length and must raise."""
        with pytest.raises(SSZTypeError) as exc_info:
            TwoVar.get_byte_length()
        assert exc_info.value.args[0] == "TwoVar: variable-size container has no fixed byte length"

    def test_all_variable_roundtrip(self) -> None:
        """A container of two variable lists roundtrips through encode then decode."""
        original = TwoVar(
            a=Uint16List4(data=[Uint16(0x1234), Uint16(0x5678)]),
            b=Uint16List4(data=[Uint16(0x9ABC)]),
        )
        # Fixed-part width is 8 bytes for two Uint32 offsets.
        # First offset is 8, second offset is 12 because the first payload spans 4 bytes.
        expected_encoding = bytes.fromhex("080000000c00000034127856bc9a")
        assert original.encode_bytes() == expected_encoding
        assert TwoVar.decode_bytes(expected_encoding) == original


class TestOneVariableField:
    """Edge case where the variable-field list contains exactly one entry."""

    def test_one_variable_field_roundtrip(self) -> None:
        """A container with a single variable field encodes one offset and the payload."""
        original = OneVar(a=Uint16List4(data=[Uint16(0x1234)]))
        # Fixed part is one offset of 4 bytes pointing to 4, then the payload.
        assert original.encode_bytes() == bytes.fromhex("040000003412")
        assert OneVar.decode_bytes(bytes.fromhex("040000003412")) == original

    def test_one_variable_field_with_empty_payload(self) -> None:
        """An empty variable field exercises the start equals end span branch."""
        original = OneVar(a=Uint16List4(data=[]))
        # The offset still points to byte 4, and the payload is zero bytes long.
        encoded = original.encode_bytes()
        assert encoded == bytes.fromhex("04000000")
        assert OneVar.decode_bytes(encoded) == original


class TestMixedContainer:
    """Interleaved fixed and variable fields, the canonical wire layout."""

    def test_mixed_is_variable(self) -> None:
        """Any variable field forces the whole container to be variable-size."""
        assert Mixed.is_fixed_size() is False

    def test_mixed_get_byte_length_raises(self) -> None:
        """The mixed container has no fixed byte length and must raise."""
        with pytest.raises(SSZTypeError) as exc_info:
            Mixed.get_byte_length()
        assert exc_info.value.args[0] == "Mixed: variable-size container has no fixed byte length"

    def test_mixed_wire_layout(self) -> None:
        """The fixed slots and offsets land before the tail payloads in field order."""
        # Fixture state:
        #   a (Uint64) = 0xAABBCCDD       -> ddccbbaa00000000   (8 bytes)
        #   b offset   = 20               -> 14000000           (4 bytes)
        #   c (Uint32) = 0xEEFF           -> ffee0000           (4 bytes)
        #   d offset   = 24               -> 18000000           (4 bytes)
        #   b payload  = [1, 2] Uint16    -> 01000200           (4 bytes)
        #   d payload  = [3]   Uint16     -> 0300               (2 bytes)
        original = Mixed(
            a=Uint64(0xAABBCCDD),
            b=Uint16List4(data=[Uint16(1), Uint16(2)]),
            c=Uint32(0xEEFF),
            d=Uint16List4(data=[Uint16(3)]),
        )
        expected_encoding = bytes.fromhex("ddccbbaa0000000014000000ffee000018000000010002000300")
        assert original.encode_bytes() == expected_encoding
        assert Mixed.decode_bytes(expected_encoding) == original


class TestZeroWidthFixedField:
    """A fixed field of no width is a fixed field, and never an offset."""

    def test_a_field_of_no_width_occupies_no_slot_and_reads_back_as_itself(self) -> None:
        """Zero is a width a fixed field can have, and the only one that is also falsy."""
        # Fixed part: a (1) + nothing (0) + the offset for b (4) + c (1) = 6 bytes.
        # A decoder that read the zero-width field as an offset instead would spend four
        # bytes of the fixed part on it and reject the offset that follows.
        original = HoldsANothingField(
            a=Uint8(1), nothing=EmptyContainer(), b=Uint16List4(data=[Uint16(2)]), c=Uint8(3)
        )
        assert original.encode_bytes() == bytes.fromhex("0106000000030200")
        assert HoldsANothingField.decode_bytes(original.encode_bytes()) == original


class TestNestedContainer:
    """Containers nested as fields of other containers."""

    def test_fixed_inside_fixed_is_fixed(self) -> None:
        """A fixed container holding another fixed container stays fixed-size."""
        assert OuterFixedNested.is_fixed_size() is True
        # 8 bytes for z plus 16 bytes for the inner pair.
        assert OuterFixedNested.get_byte_length() == 24

    def test_fixed_inside_fixed_roundtrip(self) -> None:
        """Encoding lays out the outer field then the inner fields back to back."""
        original = OuterFixedNested(z=Uint64(7), inner=InnerFixed(x=Uint64(1), y=Uint64(2)))
        encoded = original.encode_bytes()
        assert encoded == bytes.fromhex("070000000000000001000000000000000200000000000000")
        assert OuterFixedNested.decode_bytes(encoded) == original

    def test_variable_inside_outer_is_variable(self) -> None:
        """A variable inner container forces the outer to be variable-size."""
        assert OuterVarNested.is_fixed_size() is False

    def test_variable_inside_outer_roundtrip(self) -> None:
        """The inner variable container is treated as a single variable field on the outer."""
        # Fixture state:
        #   head    = 99            -> 6300000000000000   (8 bytes fixed)
        #   inner offset = 12       -> 0c000000           (4 bytes)
        #   inner payload begins at byte 12:
        #     inner.a = 7           -> 0700000000000000   (8 bytes)
        #     inner.b offset = 12   -> 0c000000           (4 bytes)
        #     inner.b payload [1,2] -> 01000200           (4 bytes)
        original = OuterVarNested(
            head=Uint64(99),
            inner=InnerVar(a=Uint64(7), b=Uint16List4(data=[Uint16(1), Uint16(2)])),
        )
        expected_encoding = bytes.fromhex(
            "63000000000000000c00000007000000000000000c00000001000200"
        )
        assert original.encode_bytes() == expected_encoding
        assert OuterVarNested.decode_bytes(expected_encoding) == original


class TestSubclassInheritance:
    """Pydantic merges parent and child fields in declaration order."""

    def test_subclass_field_order_preserved(self) -> None:
        """The subclass exposes parent fields first then its own fields."""
        assert list(SignedAttestation.model_fields.keys()) == ["slot", "data", "signature"]

    def test_subclass_roundtrip(self) -> None:
        """A subclass that adds a fixed field after a variable field roundtrips correctly."""
        original = SignedAttestation(
            slot=Uint64(5),
            data=Uint16List4(data=[Uint16(1)]),
            signature=Uint64(99),
        )
        # Fixed part is slot (8) plus data offset (4) plus signature (8) for 20 bytes.
        # Data offset value is therefore 20 and the payload is [1] as Uint16.
        expected_encoding = bytes.fromhex("05000000000000001400000063000000000000000100")
        assert original.encode_bytes() == expected_encoding
        assert SignedAttestation.decode_bytes(expected_encoding) == original


class TestSerialize:
    """Stream-level behavior of the serialize method."""

    def test_serialize_returns_total_bytes_written(self) -> None:
        """Serialize returns the total byte count including the variable tail."""
        original = OneVar(a=Uint16List4(data=[Uint16(1), Uint16(2), Uint16(3)]))
        stream = io.BytesIO()
        # Fixed part is 4 bytes for the single offset.
        # The payload is 6 bytes for three Uint16 elements.
        assert original.serialize(stream) == 10
        assert stream.getvalue() == bytes.fromhex("04000000010002000300")


class TestDeserialize:
    """Stream-level behavior of the deserialize method."""

    def test_deserialize_with_scope_reads_full_value(self) -> None:
        """Reading from a stream with a matching scope reconstructs the value."""
        original = Mixed(
            a=Uint64(1),
            b=Uint16List4(data=[Uint16(7)]),
            c=Uint32(2),
            d=Uint16List4(data=[Uint16(8), Uint16(9)]),
        )
        encoded = original.encode_bytes()
        stream = io.BytesIO(encoded)
        assert Mixed.deserialize(stream, len(encoded)) == original


class TestErrors:
    """Spec-compliance error paths for malformed inputs."""

    @pytest.mark.parametrize(
        ("bad_offset", "expected_message"),
        [
            pytest.param(11, "Mixed: first offset 11 != fixed-part end 20", id="below_fixed_end"),
            pytest.param(21, "Mixed: first offset 21 != fixed-part end 20", id="above_fixed_end"),
        ],
    )
    def test_first_offset_must_match_fixed_part_end(
        self, bad_offset: int, expected_message: str
    ) -> None:
        """The first variable offset must equal the end of the fixed part."""
        # Fixed part of Mixed is 8 + 4 + 4 + 4 = 20 bytes.
        # The payload deviates by one byte in either direction from the canonical offset.
        encoded_bytes = (
            (1).to_bytes(8, "little")
            + bad_offset.to_bytes(4, "little")
            + (2).to_bytes(4, "little")
            + (24).to_bytes(4, "little")
            + bytes.fromhex("01000200")
            + bytes.fromhex("0300")
        )
        with pytest.raises(SSZSerializationError) as exc_info:
            Mixed.decode_bytes(encoded_bytes)
        assert exc_info.value.args[0] == expected_message

    def test_non_monotonic_offsets_raise(self) -> None:
        """A second offset below the first triggers a non-monotonic offsets error."""
        # Fixed part is 8 bytes for two Uint32 offsets.
        # First offset is 8 (valid), second offset is 5 (decreasing).
        encoded_bytes = (8).to_bytes(4, "little") + (5).to_bytes(4, "little") + b"\x34\x12"
        with pytest.raises(SSZSerializationError) as exc_info:
            TwoVar.decode_bytes(encoded_bytes)
        assert exc_info.value.args[0] == "TwoVar.a: non-monotonic offsets (8 > 5)"

    def test_short_input_on_fixed_field_raises(self) -> None:
        """A truncated stream on a fixed field surfaces the field type's own error."""
        # 15 bytes is one short of the 16-byte fixed width.
        with pytest.raises(SSZSerializationError) as exc_info:
            TwoUint64.decode_bytes(b"\x00" * 15)
        assert exc_info.value.args[0] == "Uint64: expected 8 bytes, got 7"

    def test_trailing_bytes_raises(self) -> None:
        """An input one byte longer than the canonical encoding is rejected."""
        with pytest.raises(SSZSerializationError) as exc_info:
            TwoUint64.decode_bytes(b"\x00" * 17)
        assert exc_info.value.args[0] == "TwoUint64: 1 trailing byte(s) after decode"


class TestFromHex:
    """Hex-string entry point for container decoding."""

    @pytest.mark.parametrize(
        "hex_input",
        [
            pytest.param("0xab", id="with_prefix"),
            pytest.param("ab", id="without_prefix"),
            pytest.param("0xAB", id="uppercase_with_prefix"),
        ],
    )
    def test_from_hex_accepts_prefix_and_case(self, hex_input: str) -> None:
        """Hex parsing tolerates the 0x prefix and mixed case alike."""
        assert OneByte.from_hex(hex_input) == OneByte(a=Uint8(0xAB))

    @pytest.mark.parametrize(
        "hex_input",
        [
            pytest.param("", id="empty"),
            pytest.param("0x", id="prefix_only"),
        ],
    )
    def test_from_hex_empty_string_decodes_empty_container(self, hex_input: str) -> None:
        """An empty hex string decodes to a zero-field container."""
        assert EmptyContainer.from_hex(hex_input) == EmptyContainer()

    def test_from_hex_bad_hex_raises_value_error(self) -> None:
        """Non-hex characters surface a ValueError from the underlying parser."""
        with pytest.raises(ValueError) as exception_info:
            OneByte.from_hex("zz")
        assert (
            str(exception_info.value)
            == "non-hexadecimal number found in fromhex() arg at position 0"
        )


class TestHexStringValidator:
    """Pydantic validation accepts hex strings via the wrap validator."""

    @pytest.mark.parametrize(
        "hex_input",
        [
            pytest.param("0xab", id="with_prefix"),
            pytest.param("ab", id="without_prefix"),
            pytest.param("0xAB", id="uppercase_with_prefix"),
        ],
    )
    def test_validates_hex_string(self, hex_input: str) -> None:
        """Pydantic validation tolerates the 0x prefix and mixed case alike."""
        assert OneByte.model_validate(hex_input) == OneByte(a=Uint8(0xAB))

    def test_validates_empty_string_as_empty_container(self) -> None:
        """An empty hex string validates to a zero-field container."""
        assert EmptyContainer.model_validate("") == EmptyContainer()

    def test_dict_input_routes_to_field_validation(self) -> None:
        """A dict input goes through field-by-field validation, not hex decoding."""
        assert OneByte.model_validate({"a": Uint8(0xAB)}) == OneByte(a=Uint8(0xAB))

    def test_instance_input_passes_through(self) -> None:
        """An existing instance input is returned unchanged."""
        instance = OneByte(a=Uint8(0xAB))
        assert OneByte.model_validate(instance) == instance

    def test_wrong_length_hex_raises_with_class_name(self) -> None:
        """Hex with too many bytes raises a validation error tagged by the class name."""
        # 2 hex bytes ("abcd") cannot fit a 1-byte container; trailing bytes trigger the error.
        #
        # The trailing docs URL embeds the installed pydantic version, so it is anchored
        # with a regex that pins every stable character and generalizes only the version.
        with pytest.raises(
            ValidationError,
            match=(
                r"(?s)^1 validation error for OneByte\n"
                + r"  Value error, invalid OneByte hex: "
                + r"OneByte: 1 trailing byte\(s\) after decode "
                + r"\[type=value_error, input_value='abcd', input_type=str\]\n"
                + r"    For further information visit "
                + r"https://errors\.pydantic\.dev/[^/]+/v/value_error\Z"
            ),
        ):
            OneByte.model_validate("abcd")

    def test_nested_container_field_accepts_hex_string(self) -> None:
        """A nested container field accepts a hex string for its own SSZ encoding."""
        # Fixture state:
        #   inner.x (Uint64) = 1, inner.y (Uint64) = 2 -> 16 little-endian bytes
        outer = OuterFixedNested.model_validate(
            {
                "z": Uint64(7),
                "inner": "01000000000000000200000000000000",
            }
        )
        assert outer == OuterFixedNested(z=Uint64(7), inner=InnerFixed(x=Uint64(1), y=Uint64(2)))


class TestProgressiveContainerLayoutRules:
    """The four layout rules EIP-7495 states, plus the widest legal layout."""

    def test_empty_layout_rejected(self) -> None:
        """A layout with no positions admits no field and is rejected outright."""
        # A container with no field serializes to nothing, which would leave the
        # element count of a list of them unrecoverable from the wire bytes.
        with pytest.raises(
            SSZActiveFieldsError,
            match=r"^EmptyLayout: invalid active fields, the layout is empty$",
        ):

            class EmptyLayout(ProgressiveContainer):
                ACTIVE_FIELDS = ()

    @pytest.mark.parametrize(
        "active_fields",
        [
            pytest.param([0], id="single_gap"),
            pytest.param([0, 0], id="two_gaps"),
            pytest.param([1, 0], id="field_then_gap"),
            pytest.param([1, 0, 1, 0], id="trailing_gap_after_fields"),
        ],
    )
    def test_layout_ending_in_a_gap_rejected(self, active_fields: Sequence[int]) -> None:
        """A trailing gap is a second spelling of one layout, so it is illegal."""
        # The mixed-in word ignores a high zero bit, and at some widths the leaf tree
        # ignores the extra position too, which would give two layouts one root.
        with pytest.raises(
            SSZActiveFieldsError,
            match=r"^Gapped: invalid active fields, the layout ends in a gap$",
        ):
            type("Gapped", (ProgressiveContainer,), {"ACTIVE_FIELDS": tuple(active_fields)})

    @pytest.mark.parametrize(
        "position_count",
        [
            pytest.param(257, id="one_over_the_limit"),
            pytest.param(300, id="well_over_the_limit"),
        ],
    )
    def test_layout_wider_than_the_word_rejected(self, position_count: int) -> None:
        """The layout is mixed in as one 32-byte word, so 256 positions is the ceiling."""
        active_fields = (*([0] * (position_count - 1)), 1)
        with pytest.raises(
            SSZActiveFieldsError,
            match=(
                r"^TooWide: invalid active fields, the layout holds "
                + rf"{position_count} positions, over the limit of 256$"
            ),
        ):
            type("TooWide", (ProgressiveContainer,), {"ACTIVE_FIELDS": active_fields})

    def test_layout_of_exactly_256_positions_is_legal(self) -> None:
        """A 256-position layout fills the mixed-in word exactly and is accepted."""
        assert MAX_ACTIVE_FIELDS == 256
        assert len(WideProgressive.ACTIVE_FIELDS) == 256
        # Only the last position is occupied, so the shape carries a single field.
        assert list(WideProgressive.model_fields) == ["tail"]

    def test_shape_declared_without_a_layout_rejected(self) -> None:
        """A struct that skips the factory has no layout, so it cannot be merkleized."""
        # Every layout comes from the factory. Inheriting the base alone leaves none,
        # and a struct with no layout has no position to merkleize its fields at.
        with pytest.raises(
            SSZDefinitionError,
            match=r"^NoLayout must define ACTIVE_FIELDS$",
        ):

            class NoLayout(ProgressiveContainer):
                side: Uint16

    def test_field_count_below_the_set_bit_count_rejected(self) -> None:
        """A layout that sets more positions than the struct declares fields is rejected."""
        with pytest.raises(
            SSZActiveFieldsError,
            match=(
                r"^TooFewFields: invalid active fields, "
                + r"the layout sets 2 positions, and the struct declares 1$"
            ),
        ):

            class TooFewFields(ProgressiveContainer):
                ACTIVE_FIELDS = (1, 1)

                only: Uint8

    def test_field_count_above_the_set_bit_count_rejected(self) -> None:
        """A layout that sets fewer positions than the struct declares fields is rejected."""
        with pytest.raises(
            SSZActiveFieldsError,
            match=(
                r"^TooManyFields: invalid active fields, "
                + r"the layout sets 1 positions, and the struct declares 2$"
            ),
        ):

            class TooManyFields(ProgressiveContainer):
                ACTIVE_FIELDS = (0, 1)

                first: Uint8
                second: Uint8

    def test_no_fields_at_all_rejected(self) -> None:
        """The field-count rule is what catches a progressive container with no field."""
        # The layout itself is legal here; the struct simply declares nothing to fill it.
        with pytest.raises(
            SSZActiveFieldsError,
            match=(
                r"^NoFields: invalid active fields, "
                + r"the layout sets 1 positions, and the struct declares 0$"
            ),
        ):

            class NoFields(ProgressiveContainer):
                ACTIVE_FIELDS = (1,)

                pass

    def test_subclass_of_a_progressive_container_rechecks_the_layout(self) -> None:
        """Appending a field to a concrete shape breaks the layout it inherited."""
        with pytest.raises(
            SSZActiveFieldsError,
            match=(
                r"^BiggerSquare: invalid active fields, "
                + r"the layout sets 2 positions, and the struct declares 3$"
            ),
        ):

            class BiggerSquare(Square):
                extra: Uint8

    def test_layout_error_is_a_type_error_carrying_its_reason(self) -> None:
        """The failure is an SSZ type error and keeps both operands machine-readable."""
        with pytest.raises(SSZActiveFieldsError) as exception_info:
            type("GapTail", (ProgressiveContainer,), {"ACTIVE_FIELDS": (1, 0)})
        assert isinstance(exception_info.value, SSZTypeError)
        assert exception_info.value.type_name == "GapTail"
        assert exception_info.value.active_fields == (1, 0)
        assert exception_info.value.reason == "the layout ends in a gap"


class TestProgressiveContainerLayoutMetadata:
    """The layout a factory-built base carries, and the field order it implies."""

    def test_layout_accepts_booleans_as_bits(self) -> None:
        """A boolean equals the bit it stands for, so a layout may spell positions that way."""

        class BooleanLayout(ProgressiveContainer):
            ACTIVE_FIELDS = (True, False, True)

            first: Uint8
            third: Uint8

        # Two set positions, so two fields, at positions 0 and 2.
        assert sum(BooleanLayout.ACTIVE_FIELDS) == 2
        assert list(BooleanLayout.model_fields) == ["first", "third"]

    @pytest.mark.parametrize(
        "layout, case_id",
        [
            pytest.param((1, 5, 1), "arbitrary_int", id="arbitrary_int"),
            pytest.param("101", "string", id="string_layout"),
            pytest.param((1, -1, 1), "negative", id="negative_int"),
        ],
    )
    def test_layout_holding_something_other_than_bits_rejected(
        self, layout: object, case_id: str
    ) -> None:
        """A layout is bits, so any other value is a typo rather than a value to coerce."""
        # A layout written as the string "101" would otherwise read as three set
        # positions, since every character of it is truthy.
        with pytest.raises(
            SSZActiveFieldsError,
            match=r"^BadBits: invalid active fields, a position holds neither 0 nor 1$",
        ):
            type("BadBits", (ProgressiveContainer,), {"ACTIVE_FIELDS": layout})

    @pytest.mark.parametrize(
        "container_type, expected_layout, expected_field_names",
        [
            pytest.param(Square, (1, 0, 1), ["side", "color"], id="interior_gap"),
            pytest.param(Circle, (0, 1, 1), ["radius", "color"], id="leading_gap"),
            pytest.param(OneFieldProgressive, (1,), ["a"], id="single_position"),
            pytest.param(LeadingGapProgressive, (0, 0, 1), ["c"], id="two_leading_gaps"),
            pytest.param(
                MultiGapProgressive, (1, 0, 0, 1, 0, 1), ["a", "b", "c"], id="multiple_gaps"
            ),
        ],
    )
    def test_fields_are_declared_in_set_bit_order(
        self,
        container_type: type[ProgressiveContainer],
        expected_layout: tuple[int, ...],
        expected_field_names: list[str],
    ) -> None:
        """One field per set bit, declared in the order the set bits appear."""
        assert container_type.ACTIVE_FIELDS == expected_layout
        assert list(container_type.model_fields) == expected_field_names
        assert sum(container_type.ACTIVE_FIELDS) == len(expected_field_names)

    @pytest.mark.parametrize(
        "container_type, expected_byte_length",
        [
            pytest.param(Square, 3, id="interior_gap"),
            pytest.param(Circle, 3, id="leading_gap"),
            pytest.param(OneFieldProgressive, 2, id="single_position"),
            pytest.param(LeadingGapProgressive, 4, id="two_leading_gaps"),
            pytest.param(MultiGapProgressive, 7, id="multiple_gaps"),
            pytest.param(FixedPairProgressive, 12, id="fixed_pair"),
            pytest.param(WideProgressive, 1, id="two_hundred_fifty_six_positions"),
            pytest.param(InnerProgressive, 3, id="nested_inner"),
            pytest.param(OuterProgressive, 4, id="nested_outer"),
        ],
    )
    def test_gaps_cost_no_bytes(
        self, container_type: type[ProgressiveContainer], expected_byte_length: int
    ) -> None:
        """A fixed-size shape sums only its declared fields; a gap adds nothing."""
        assert container_type.is_fixed_size() is True
        assert container_type.get_byte_length() == expected_byte_length

    @pytest.mark.parametrize(
        "container_type, expected_message",
        [
            pytest.param(
                ListFieldProgressive,
                "ListFieldProgressive: variable-size container has no fixed byte length",
                id="bounded_list_field",
            ),
            pytest.param(
                ProgressiveFieldsProgressive,
                "ProgressiveFieldsProgressive: variable-size container has no fixed byte length",
                id="progressive_fields",
            ),
        ],
    )
    def test_variable_size_shapes_have_no_byte_length(
        self, container_type: type[ProgressiveContainer], expected_message: str
    ) -> None:
        """One variable-size field makes the whole shape variable-size, as for a container."""
        assert container_type.is_fixed_size() is False
        with pytest.raises(SSZTypeError) as exception_info:
            container_type.get_byte_length()
        assert exception_info.value.args[0] == expected_message


class TestLayoutBuilderShapes:
    """The bits a width and a set of vacant positions produce."""

    @pytest.mark.parametrize(
        "width, gaps, expected_layout",
        [
            pytest.param(1, (), (1,), id="narrowest"),
            pytest.param(4, (), (1, 1, 1, 1), id="no_gaps"),
            pytest.param(3, (1,), (1, 0, 1), id="interior_gap"),
            pytest.param(3, (0,), (0, 1, 1), id="leading_gap"),
            pytest.param(3, (0, 1), (0, 0, 1), id="adjacent_leading_gaps"),
            pytest.param(6, (1, 2, 4), (1, 0, 0, 1, 0, 1), id="adjacent_pair_then_lone_gap"),
        ],
    )
    def test_every_position_is_occupied_unless_it_is_named_vacant(
        self, width: int, gaps: tuple[int, ...], expected_layout: tuple[int, ...]
    ) -> None:
        """The result is one bit per position, cleared exactly at the positions given."""
        # Worked example, the third case:
        #
        #     width 3, vacant at 1
        #     position :   0    1    2
        #     bit      :   1    0    1
        assert active_fields(width=width, gaps=gaps) == expected_layout

    def test_the_bits_are_plain_integers(self) -> None:
        """The result holds integers, which is what the declaration rules accept."""
        # Bits written by hand may be booleans instead.
        # Both spellings sum alike, which is all the field-count check reads.
        # Producing plain integers keeps the built form the narrower of the two.
        assert {type(bit) for bit in active_fields(width=3, gaps=(1,))} == {int}

    @pytest.mark.parametrize(
        "width, gaps, expected_message",
        [
            pytest.param(
                0, (), "a layout holds at least one position, got a width of 0", id="zero_width"
            ),
            pytest.param(
                -1,
                (),
                "a layout holds at least one position, got a width of -1",
                id="negative_width",
            ),
            pytest.param(
                3, (3,), "gap 3 falls outside a layout of 3 positions", id="vacancy_at_the_width"
            ),
            pytest.param(
                3, (5,), "gap 5 falls outside a layout of 3 positions", id="vacancy_past_the_width"
            ),
            pytest.param(
                3, (-1,), "gap -1 falls outside a layout of 3 positions", id="negative_vacancy"
            ),
            pytest.param(3, (2, 1), "gaps (2, 1) are not in ascending order", id="descending"),
            pytest.param(3, (1, 1), "gaps (1, 1) are not in ascending order", id="repeated"),
        ],
    )
    def test_a_layout_that_cannot_exist_is_refused(
        self, width: int, gaps: tuple[int, ...], expected_message: str
    ) -> None:
        """A width below one, an out-of-range vacancy, and unordered vacancies all fail."""
        # A vacancy outside the width would simply vanish.
        # The caller would get back a layout with one fewer hole than they wrote:
        #
        #     width 3, vacant at 5   ->   (1, 1, 1)   and the 5 is nowhere
        #
        # A repeat vanishes the same way.
        # Two vacancies at one position leave one hole, against the two that were counted.
        with pytest.raises(SSZValueError) as exception_info:
            active_fields(width=width, gaps=gaps)
        assert exception_info.value.args[0] == expected_message

    @pytest.mark.parametrize(
        "width, gaps, expected_message",
        [
            pytest.param(True, (), "Expected an integer width, got bool", id="boolean_width"),
            pytest.param(3.0, (), "Expected an integer width, got float", id="fractional_width"),
            pytest.param(
                3, (True,), "Expected an integer position, got bool", id="boolean_vacancy"
            ),
            pytest.param(
                3, (1.0,), "Expected an integer position, got float", id="fractional_vacancy"
            ),
        ],
    )
    def test_a_width_or_a_position_that_is_not_a_plain_integer_is_refused(
        self, width: Any, gaps: tuple[Any, ...], expected_message: str
    ) -> None:
        """Only a plain integer counts positions: a boolean and a fraction are both out."""
        # A boolean is an integer in this language.
        # Nothing in the language itself stops one reaching a count:
        #
        #     width True   ->   would silently mean a one-position layout
        #
        # This library already refuses one wherever a count is wanted.
        # The phrasing here is the same phrasing used at those two places:
        #
        #     a declared list capacity of True   ->   Expected an integer count ..., got bool
        #     a uint built from True             ->   Expected int, got bool
        #
        # A boolean written as a bit is a different matter, and stays legal.
        # There a boolean is the value 0 or 1, not a count of positions.
        with pytest.raises(SSZTypeMismatch) as exception_info:
            active_fields(width=width, gaps=gaps)
        assert exception_info.value.args[0] == expected_message

    def test_the_package_exports_the_builder(self) -> None:
        """The export list is what a star import and the documentation tooling read."""
        # Importing the name at the top of this module proves it is reachable.
        # Only the export list proves it is public.
        assert "active_fields" in ssz.__all__


class TestABuiltLayoutMatchesASpelledOutOne:
    """A built layout and the same bits written out are one and the same declaration."""

    @pytest.mark.parametrize(
        "spelled_out, built",
        [
            pytest.param(
                Square(side=Uint16(0x1234), color=Uint8(0x56)),
                BuiltSquare(side=Uint16(0x1234), color=Uint8(0x56)),
                id="interior_gap",
            ),
            pytest.param(
                Circle(radius=Uint16(0x1234), color=Uint8(0x56)),
                BuiltCircle(radius=Uint16(0x1234), color=Uint8(0x56)),
                id="leading_gap",
            ),
            pytest.param(
                LeadingGapProgressive(c=Uint32(0x11223344)),
                BuiltTwoLeadingGaps(c=Uint32(0x11223344)),
                id="adjacent_leading_gaps",
            ),
            pytest.param(
                MultiGapProgressive(a=Uint8(1), b=Uint16(0x0203), c=Uint32(0x04050607)),
                BuiltMultiGap(a=Uint8(1), b=Uint16(0x0203), c=Uint32(0x04050607)),
                id="adjacent_pair_then_lone_gap",
            ),
        ],
    )
    def test_the_two_spellings_place_encode_and_hash_alike(
        self, spelled_out: ProgressiveContainer, built: ProgressiveContainer
    ) -> None:
        """Identical bits, identical bytes, and an identical root."""
        # The root is the strongest of the three assertions.
        # The layout is mixed into it.
        # One bit out of place therefore separates two roots.
        # The bytes alone would not: a vacancy costs no bytes at all.
        assert type(built).ACTIVE_FIELDS == type(spelled_out).ACTIVE_FIELDS
        assert built.encode_bytes() == spelled_out.encode_bytes()
        assert hash_tree_root(built) == hash_tree_root(spelled_out)


class TestTheWidthIsStatedRatherThanCounted:
    """Why a layout names its width instead of deriving it from the fields and the gaps."""

    def test_a_dropped_field_recorded_as_a_vacancy_holds_the_later_fields_in_place(self) -> None:
        """Recording the vacancy keeps the width, holding every later field in place."""
        # Before the fork, four fields over four positions:
        #
        #     position :   0    1    2    3
        #     field    :   a    b    c    d
        #
        # After the fork drops the second field and records the vacancy:
        #
        #     position :   0    1    2    3
        #     field    :   a    -    c    d
        #
        # The last two fields never move, which is the whole point of this container shape.
        assert FourFieldOriginal.ACTIVE_FIELDS == (1, 1, 1, 1)
        assert FourFieldSecondDropped.ACTIVE_FIELDS == (1, 0, 1, 1)

        before = [index for index, bit in enumerate(FourFieldOriginal.ACTIVE_FIELDS) if bit]
        after = [index for index, bit in enumerate(FourFieldSecondDropped.ACTIVE_FIELDS) if bit]
        assert before == [0, 1, 2, 3]
        assert after == [0, 2, 3]

    def test_a_dropped_field_recorded_nowhere_is_refused(self) -> None:
        """A width of four beside three fields is a disagreement the declaration refuses."""
        # This is the case the stated width exists to catch.
        #
        # A derived width would be three fields plus zero vacancies, that is 3.
        # The declaration below would then have been accepted, as:
        #
        #     position :   0    1    2
        #     field    :   a    c    d
        #
        # Both surviving fields would have slid one position down.
        # Nothing in the declaration would have changed to say so.
        # Every proof and every root against the four-position shape would stop matching.
        #
        # A stated width keeps the two counts independent.
        # The disagreement then has nowhere to hide.
        with pytest.raises(
            SSZActiveFieldsError,
            match=(
                r"^Forgot: invalid active fields, "
                + r"the layout sets 4 positions, and the struct declares 3$"
            ),
        ):

            class Forgot(ProgressiveContainer):
                ACTIVE_FIELDS = active_fields(width=4)

                a: Uint16
                c: Uint16
                d: Uint16


class TestRulesLeftWithTheDeclaration:
    """Two layout rules stay where the shape is declared rather than moving to the builder."""

    def test_a_trailing_vacancy_is_reported_against_the_shape(self) -> None:
        """The builder hands back the bits; rejecting them is the declaration's job."""
        # Split of responsibility:
        #
        #     builder      : sees a width and some numbers
        #                    can name neither the shape nor its fields
        #     declaration  : knows the type name and the field list
        #                    its message can say which shape broke which rule
        #
        # A trailing vacancy is a property of the finished layout, not of the arguments.
        # The rule earns its keep only when the message names the shape that broke it.
        assert active_fields(width=3, gaps=(2,)) == (1, 1, 0)

        with pytest.raises(
            SSZActiveFieldsError,
            match=r"^TrailingGap: invalid active fields, the layout ends in a gap$",
        ):
            type(
                "TrailingGap",
                (ProgressiveContainer,),
                {"ACTIVE_FIELDS": active_fields(width=3, gaps=(2,))},
            )

    def test_the_width_ceiling_is_reported_against_the_shape(self) -> None:
        """The builder counts to any width; capping it at 256 is the declaration's job."""
        # The ceiling comes from the 32-byte word the layout is mixed into.
        # That word holds 256 bits, so 256 positions is the most one can carry.
        # It belongs to merkleization, not to the arithmetic that turns a width into bits.
        assert len(active_fields(width=MAX_ACTIVE_FIELDS)) == 256
        assert len(active_fields(width=MAX_ACTIVE_FIELDS + 1)) == 257

        with pytest.raises(
            SSZActiveFieldsError,
            match=(
                r"^TooWideBuilt: invalid active fields, "
                + r"the layout holds 257 positions, over the limit of 256$"
            ),
        ):
            type(
                "TooWideBuilt",
                (ProgressiveContainer,),
                {"ACTIVE_FIELDS": active_fields(width=MAX_ACTIVE_FIELDS + 1)},
            )


class TestAWideLayout:
    """The width the builder exists for: too many positions to read as a row of bits."""

    def test_a_wide_layout_is_the_same_layout_written_out(self) -> None:
        """Thirty-two positions with two vacancies, spelled both ways, are equal."""
        # This is the readability claim made concrete.
        # The row below carries exactly two pieces of information, at index 4 and index 19.
        # Finding them means counting thirty-two entries by eye.
        spelled_out = (
            # positions 0 to 4
            1, 1, 1, 1, 0,
            # positions 5 to 18
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            # position 19
            0,
            # positions 20 to 31
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        )  # fmt: skip
        assert WideForkEvolvedState.ACTIVE_FIELDS == spelled_out

    def test_the_wide_shape_places_thirty_fields_over_thirty_two_positions(self) -> None:
        """Thirty set positions, thirty fields, and eight bytes apiece."""
        assert len(WideForkEvolvedState.ACTIVE_FIELDS) == 32
        assert sum(WideForkEvolvedState.ACTIVE_FIELDS) == 30
        assert len(WideForkEvolvedState.model_fields) == 30
        # A vacancy costs no bytes.
        # 30 fields of 8 bytes therefore give 240.
        assert WideForkEvolvedState.get_byte_length() == 240

    def test_the_wide_shape_round_trips(self) -> None:
        """A wide layout serializes and merkleizes like any other."""
        value = WideForkEvolvedState.default()
        assert value.encode_bytes() == b"\x00" * 240
        assert WideForkEvolvedState.decode_bytes(value.encode_bytes()) == value
        # Both values here are all zeros on the wire, over 240 bytes and 8 bytes.
        # The layout is mixed into the root, so two widths cannot collide on it.
        assert hash_tree_root(value) != hash_tree_root(FourFieldOriginal.default())

    def test_the_wide_shape_hashes_each_field_at_its_own_position(self) -> None:
        """Thirty fields land on the thirty set positions, and the two gaps hold zero."""
        # Every field takes a distinct value, so a field hashed one position off
        # changes the root instead of colliding with its neighbour.
        value = WideForkEvolvedState(
            **{name: Uint64(n) for n, name in enumerate(WideForkEvolvedState.model_fields, 1)}
        )

        # The expected leaves are laid out by position, not by declaration index:
        # a field root where the layout sets a bit, and a zero chunk at each gap.
        fields = iter(WideForkEvolvedState.model_fields)
        leaves = [
            hash_tree_root(getattr(value, next(fields))) if bit else ZERO_ROOT
            for bit in WideForkEvolvedState.ACTIVE_FIELDS
        ]
        assert leaves[4] == ZERO_ROOT
        assert leaves[19] == ZERO_ROOT

        expected = mix_in_active_fields(
            merkleize_progressive(leaves), WideForkEvolvedState.ACTIVE_FIELDS
        )
        assert hash_tree_root(value) == expected

    def test_a_gap_written_at_the_wrong_position_is_a_different_shape(self) -> None:
        """A misplaced gap keeps every count agreeing, and moves the fields under it."""
        # This is the mistake the declaration rules cannot catch.
        # Thirty-two positions and thirty fields hold either way, so the shape is
        # accepted, and only the root says the two are not the same type.
        misplaced = MisplacedGapState.ACTIVE_FIELDS
        intended = WideForkEvolvedState.ACTIVE_FIELDS
        assert len(misplaced) == len(intended)
        assert sum(misplaced) == sum(intended)
        assert len(MisplacedGapState.model_fields) == len(WideForkEvolvedState.model_fields)
        assert misplaced != intended

        # The wire format reads a gap as no bytes at all, so both encode identically.
        assert MisplacedGapState.default().encode_bytes() == b"\x00" * 240
        # The layout word separates them, and so does the field that moved under the gap.
        assert hash_tree_root(MisplacedGapState.default()) != hash_tree_root(
            WideForkEvolvedState.default()
        )


class TestALayoutWrittenWithTypedNumbers:
    """
    A width and a position may be written with a fixed-width unsigned integer.
    """

    def test_a_typed_width_and_position_give_the_plain_layout(self) -> None:
        """The type a position was written at leaves no trace on the layout."""
        assert active_fields(width=Uint64(4), gaps=(Uint8(1),)) == active_fields(width=4, gaps=(1,))
        # Every bit is a plain integer, whatever the arguments were written at.
        assert {type(bit) for bit in active_fields(width=Uint64(4))} == {int}

    def test_a_typed_position_still_opens_its_vacancy(self) -> None:
        """A position counts as the plain number it names, not as a value of its own type."""
        # A typed position hashes and compares as the number it holds, so the membership
        # test that decides the vacancy finds it.
        assert Uint8(1) in frozenset({1})
        assert active_fields(width=3, gaps=(Uint8(1),)) == (1, 0, 1)

    def test_a_typed_position_out_of_range_is_reported_as_a_plain_number(self) -> None:
        """A refusal names the position, not the spelling it arrived in."""
        with pytest.raises(SSZValueError, match=r"^gap 5 falls outside a layout of 3 positions$"):
            active_fields(width=3, gaps=(Uint64(5),))


class TestProgressiveContainerSerialization:
    """Wire format of a progressive container: that of a container, gaps costing nothing."""

    def test_square_and_circle_share_an_encoding(self) -> None:
        """The EIP's two shapes encode to the very same three bytes."""
        # Only the tree tells them apart; the bytes carry no layout information at all.
        square = Square(side=Uint16(0x1234), color=Uint8(0x56))
        circle = Circle(radius=Uint16(0x1234), color=Uint8(0x56))
        assert square.encode_bytes() == bytes.fromhex("341256")
        assert circle.encode_bytes() == bytes.fromhex("341256")

    @pytest.mark.parametrize(
        "value, expected_hex",
        [
            # A gap occupies no byte, so each encoding is the concatenated fields.
            pytest.param(
                Square(side=Uint16(0x1234), color=Uint8(0x56)), "341256", id="interior_gap"
            ),
            pytest.param(
                Circle(radius=Uint16(0x1234), color=Uint8(0x56)), "341256", id="leading_gap"
            ),
            pytest.param(OneFieldProgressive(a=Uint16(0xBEEF)), "efbe", id="single_position"),
            pytest.param(
                LeadingGapProgressive(c=Uint32(0x11223344)), "44332211", id="two_leading_gaps"
            ),
            pytest.param(
                MultiGapProgressive(a=Uint8(1), b=Uint16(0x0203), c=Uint32(0x04050607)),
                "01030207060504",
                id="multiple_gaps",
            ),
            pytest.param(
                FixedPairProgressive(a=Uint64(1), b=Uint32(2)),
                "010000000000000002000000",
                id="fixed_pair",
            ),
            pytest.param(WideProgressive(tail=Uint8(0xAB)), "ab", id="widest_layout"),
        ],
    )
    def test_fixed_size_encodings_round_trip(
        self, value: ProgressiveContainer, expected_hex: str
    ) -> None:
        """Fixed-size shapes lay their fields out back to back and decode back unchanged."""
        encoded = value.encode_bytes()
        assert encoded.hex() == expected_hex
        assert type(value).decode_bytes(encoded) == value

    def test_bounded_list_field_encoding(self) -> None:
        """A bounded list field is reached through an offset, as in an ordinary container."""
        # Fixture state:
        #   head (Uint64) = 7   -> 0700000000000000   (8 bytes)
        #   body offset   = 12  -> 0c000000           (4 bytes)
        #   body payload [1, 2] -> 01000200           (4 bytes)
        value = ListFieldProgressive(head=Uint64(7), body=Uint16List4(data=[Uint16(1), Uint16(2)]))
        expected_encoding = bytes.fromhex("07000000000000000c00000001000200")
        assert value.encode_bytes() == expected_encoding
        assert ListFieldProgressive.decode_bytes(expected_encoding) == value

    def test_empty_bounded_list_field_encoding(self) -> None:
        """An empty variable-size field leaves its offset pointing at the end of the input."""
        value = ListFieldProgressive(head=Uint64(7), body=Uint16List4(data=[]))
        expected_encoding = bytes.fromhex("07000000000000000c000000")
        assert value.encode_bytes() == expected_encoding
        assert ListFieldProgressive.decode_bytes(expected_encoding) == value

    def test_progressive_shape_fields_encoding(self) -> None:
        """Progressive list and bitlist fields each take one offset, in field order."""
        # Fixture state:
        #   head (Uint32)   = 0x11223344 -> 44332211   (4 bytes)
        #   numbers offset  = 12         -> 0c000000   (4 bytes)
        #   flags offset    = 16         -> 10000000   (4 bytes)
        #   numbers [1, 2]               -> 01000200   (4 bytes)
        #   flags [1, 0, 1]              -> 0d         (3 bits plus the delimiter)
        value = ProgressiveFieldsProgressive(
            head=Uint32(0x11223344),
            numbers=Uint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
            flags=ProgressiveBitList(data=[Boolean(True), Boolean(False), Boolean(True)]),
        )
        expected_encoding = bytes.fromhex("443322110c00000010000000010002000d")
        assert value.encode_bytes() == expected_encoding
        assert ProgressiveFieldsProgressive.decode_bytes(expected_encoding) == value

    def test_serialize_returns_total_bytes_written(self) -> None:
        """Serialize reports the fixed part plus the variable tail it appended."""
        value = ListFieldProgressive(
            head=Uint64(7), body=Uint16List4(data=[Uint16(1), Uint16(2), Uint16(3)])
        )
        stream = io.BytesIO()
        # Fixed part is 8 bytes for head plus 4 for the offset, then a 6-byte payload.
        assert value.serialize(stream) == 18
        assert stream.getvalue() == bytes.fromhex("07000000000000000c000000010002000300")

    def test_deserialize_with_scope_reads_full_value(self) -> None:
        """Reading from a stream with a matching scope reconstructs the value."""
        value = ProgressiveFieldsProgressive(
            head=Uint32(1),
            numbers=Uint16ProgressiveList(data=[Uint16(2)]),
            flags=ProgressiveBitList(data=[Boolean(True)]),
        )
        encoded = value.encode_bytes()
        stream = io.BytesIO(encoded)
        assert ProgressiveFieldsProgressive.deserialize(stream, len(encoded)) == value

    def test_from_hex_and_validation_accept_a_hex_payload(self) -> None:
        """The hex entry points work on a progressive container as on any container."""
        expected = Square(side=Uint16(0x1234), color=Uint8(0x56))
        assert Square.from_hex("0x341256") == expected
        assert Square.model_validate("341256") == expected

    def test_bad_hex_reports_the_shape_name(self) -> None:
        """A malformed hex payload surfaces a validation error tagged by the class name."""
        with pytest.raises(ValidationError, match=r"invalid Square hex: "):
            Square.model_validate("34125600")


class TestProgressiveContainerNesting:
    """Progressive containers as fields and as elements of the collection types."""

    def test_progressive_container_inside_a_progressive_container(self) -> None:
        """A fixed-size progressive field inlines, and the outer shape stays fixed-size."""
        value = OuterProgressive(
            head=Uint8(1), inner=InnerProgressive(x=Uint16(0x0203), y=Uint8(4))
        )
        expected_encoding = bytes.fromhex("01030204")
        assert value.encode_bytes() == expected_encoding
        assert OuterProgressive.decode_bytes(expected_encoding) == value

    def test_bounded_list_of_progressive_containers(self) -> None:
        """Fixed-size elements need no offset table, so the bodies sit back to back."""
        value = SquareList4(
            data=[
                Square(side=Uint16(1), color=Uint8(2)),
                Square(side=Uint16(3), color=Uint8(4)),
            ]
        )
        expected_encoding = bytes.fromhex("010002030004")
        assert value.encode_bytes() == expected_encoding
        assert SquareList4.decode_bytes(expected_encoding) == value

    def test_progressive_list_of_progressive_containers(self) -> None:
        """The progressive list shape carries the same fixed-size element bodies."""
        value = SquareProgressiveList(
            data=[
                Square(side=Uint16(1), color=Uint8(2)),
                Square(side=Uint16(3), color=Uint8(4)),
            ]
        )
        expected_encoding = bytes.fromhex("010002030004")
        assert value.encode_bytes() == expected_encoding
        assert SquareProgressiveList.decode_bytes(expected_encoding) == value

    def test_container_holding_a_fixed_size_progressive_container(self) -> None:
        """An ordinary container inlines a fixed-size progressive field."""
        value = ContainerWithProgressive(
            tag=Uint8(0xFF), shape=Square(side=Uint16(0x1234), color=Uint8(0x56))
        )
        assert ContainerWithProgressive.is_fixed_size() is True
        assert ContainerWithProgressive.get_byte_length() == 4
        expected_encoding = bytes.fromhex("ff341256")
        assert value.encode_bytes() == expected_encoding
        assert ContainerWithProgressive.decode_bytes(expected_encoding) == value

    def test_container_holding_a_variable_size_progressive_container(self) -> None:
        """A variable-size progressive field is reached through an offset like any other."""
        # Fixture state:
        #   tag          = 0xFF -> ff         (1 byte)
        #   shape offset = 5    -> 05000000   (4 bytes)
        #   shape body   : head = 7, body offset = 12, body payload [1]
        value = ContainerWithVariableProgressive(
            tag=Uint8(0xFF),
            shape=ListFieldProgressive(head=Uint64(7), body=Uint16List4(data=[Uint16(1)])),
        )
        assert ContainerWithVariableProgressive.is_fixed_size() is False
        expected_encoding = bytes.fromhex("ff0500000007000000000000000c0000000100")
        assert value.encode_bytes() == expected_encoding
        assert ContainerWithVariableProgressive.decode_bytes(expected_encoding) == value


class TestProgressiveContainerDecodeErrors:
    """Malformed inputs a progressive-container decoder has to reject."""

    def test_short_input_on_a_fixed_field_raises(self) -> None:
        """A truncated stream on a fixed field surfaces the field type's own error."""
        # Two bytes feed side and leave nothing for color.
        with pytest.raises(SSZSerializationError) as exception_info:
            Square.decode_bytes(bytes.fromhex("3412"))
        assert exception_info.value.args[0] == "Uint8: expected 1 bytes, got 0"

    def test_trailing_bytes_raise(self) -> None:
        """An input one byte longer than the canonical encoding is rejected."""
        with pytest.raises(SSZSerializationError) as exception_info:
            Square.decode_bytes(bytes.fromhex("34125600"))
        assert exception_info.value.args[0] == "Square: 1 trailing byte(s) after decode"

    @pytest.mark.parametrize(
        "bad_offset",
        [
            pytest.param(11, id="below_fixed_end"),
            pytest.param(13, id="above_fixed_end"),
        ],
    )
    def test_first_offset_must_match_the_fixed_part_end(self, bad_offset: int) -> None:
        """The first offset must equal the end of the fixed part, here 12 bytes in."""
        encoded_bytes = (7).to_bytes(8, "little") + bad_offset.to_bytes(4, "little")
        with pytest.raises(SSZSerializationError) as exception_info:
            ListFieldProgressive.decode_bytes(encoded_bytes)
        assert exception_info.value.args[0] == (
            f"ListFieldProgressive: first offset {bad_offset} != fixed-part end 12"
        )

    def test_non_monotonic_offsets_raise(self) -> None:
        """A second offset below the first triggers a non-monotonic offsets error."""
        # Fixed part is 4 bytes for head plus two 4-byte offsets, so it ends at byte 12.
        encoded_bytes = (
            (1).to_bytes(4, "little") + (12).to_bytes(4, "little") + (11).to_bytes(4, "little")
        )
        with pytest.raises(SSZSerializationError) as exception_info:
            ProgressiveFieldsProgressive.decode_bytes(encoded_bytes)
        assert exception_info.value.args[0] == (
            "ProgressiveFieldsProgressive.numbers: non-monotonic offsets (12 > 11)"
        )

    def test_scope_shorter_than_the_fixed_part_raises(self) -> None:
        """A scope that cannot even cover the offsets is rejected by the field decoder."""
        stream = io.BytesIO(bytes.fromhex("0700000000000000"))
        with pytest.raises(SSZSerializationError) as exception_info:
            ListFieldProgressive.deserialize(stream, 8)
        assert exception_info.value.args[0] == "Uint32: expected 4 bytes, got 0"


class TestContainerUnaffectedByTheSharedBase:
    """The refactor onto a shared base leaves the bounded container exactly as it was."""

    def test_both_shapes_build_on_the_shared_base(self) -> None:
        """Container and the progressive base are siblings, not one another's subclass."""
        assert issubclass(Container, _SSZContainer)
        assert issubclass(ProgressiveContainer, _SSZContainer)
        assert not issubclass(Container, ProgressiveContainer)
        assert not issubclass(ProgressiveContainer, Container)

    def test_a_bounded_container_carries_no_layout(self) -> None:
        """Only the progressive shape declares a field layout."""
        assert not hasattr(TwoUint64, "ACTIVE_FIELDS")
        assert Square.ACTIVE_FIELDS == (1, 0, 1)

    def test_the_two_shapes_share_one_wire_format(self) -> None:
        """The same two fields encode to the same bytes whichever shape declares them."""
        bounded = TwoUint64(a=Uint64(1), b=Uint64(2))
        progressive = TwoUint64Progressive(a=Uint64(1), b=Uint64(2))
        # Neither shape writes any layout information: the bytes are the fields alone.
        assert bounded.encode_bytes() == progressive.encode_bytes()
        assert TwoUint64.get_byte_length() == TwoUint64Progressive.get_byte_length() == 16


class TestContainerDefaults:
    """
    One field default per field, filled whether every field was left out or only some.

    Both struct shapes take their defaults from the shared base, so each case is
    checked on the bounded shape and on the progressive one alike.
    """

    def test_a_struct_built_from_nothing_takes_every_field_default(self) -> None:
        """The spec gives a struct the default of one field default per field."""
        assert TwoUint64.default() == TwoUint64(a=Uint64(0), b=Uint64(0))

    def test_a_partly_named_struct_fills_the_fields_left_out(self) -> None:
        """Naming one field leaves every other at its own default rather than failing."""
        # A type checker reads the declared field list, not the defaults this library
        # attaches to it, so it reports the fields left out as missing arguments.
        value = TwoUint64(a=Uint64(3))  # ty: ignore[missing-argument]
        assert value.a == Uint64(3)
        assert value.b == Uint64(0)

    def test_a_partly_named_progressive_container_fills_the_fields_left_out(self) -> None:
        """The progressive shape fills a missing field on exactly the same terms."""
        assert Square(side=Uint16(1)) == Square(side=Uint16(1), color=Uint8(0))  # ty: ignore[missing-argument]

    @pytest.mark.parametrize(
        "container_type, expected_field_names",
        [
            pytest.param(TwoUint64, ["a", "b"], id="fixed_container"),
            pytest.param(Mixed, ["a", "b", "c", "d"], id="mixed_container"),
            pytest.param(Square, ["side", "color"], id="progressive_container"),
        ],
    )
    def test_no_field_is_reported_as_required(
        self, container_type: type[_SSZContainer], expected_field_names: list[str]
    ) -> None:
        """Every field carries a default, so Pydantic itself reports none of them required."""
        assert list(container_type.model_fields) == expected_field_names
        assert all(not field.is_required() for field in container_type.model_fields.values())

    def test_a_variable_size_field_defaults_to_its_empty_value(self) -> None:
        """A list field contributes the empty list, which is that shape's own default."""
        assert Mixed.default() == Mixed(
            a=Uint64(0), b=Uint16List4(data=[]), c=Uint32(0), d=Uint16List4(data=[])
        )

    def test_a_nested_container_field_defaults_field_by_field(self) -> None:
        """A container field contributes its own default, built from its own field defaults."""
        assert OuterFixedNested.default() == OuterFixedNested(
            z=Uint64(0), inner=InnerFixed(x=Uint64(0), y=Uint64(0))
        )

    def test_a_vector_of_containers_field_defaults_position_by_position(self) -> None:
        """Two levels of nesting: the vector fills each position with the element default."""
        zero_inner = InnerFixed(x=Uint64(0), y=Uint64(0))
        assert ContainerWithVectorOfContainers.default() == ContainerWithVectorOfContainers(
            tag=Uint8(0), items=InnerFixedVector2(data=[zero_inner, zero_inner])
        )

    def test_a_progressive_container_with_gaps_defaults_its_declared_fields(self) -> None:
        """A gap holds no field, so only the three declared fields take a default."""
        assert MultiGapProgressive.ACTIVE_FIELDS == (1, 0, 0, 1, 0, 1)
        assert MultiGapProgressive.default() == MultiGapProgressive(
            a=Uint8(0), b=Uint16(0), c=Uint32(0)
        )
        # Six positions, three fields, and 1 + 2 + 4 = 7 bytes: a gap still costs nothing.
        assert MultiGapProgressive.default().encode_bytes() == b"\x00" * 7

    def test_each_field_default_is_built_on_its_own(self) -> None:
        """Values are mutable, so two structs must never share one field value."""
        first = OuterFixedNested.default()
        assert first.inner is not OuterFixedNested.default().inner
        first.inner.x = Uint64(9)
        # The next default is unaffected by the mutation applied to the first one.
        assert OuterFixedNested.default().inner.x == Uint64(0)

    def test_each_default_element_of_a_vector_field_is_built_on_its_own(self) -> None:
        """Within one struct the two vector positions hold two distinct container values."""
        value = ContainerWithVectorOfContainers.default()
        assert value.items.data[0] is not value.items.data[1]
        value.items.data[0].x = Uint64(9)
        assert value.items.data[1].x == Uint64(0)

    @pytest.mark.parametrize(
        "default_value, non_default_value",
        [
            pytest.param(TwoUint64.default(), TwoUint64(a=Uint64(1)), id="fixed_container"),  # ty: ignore[missing-argument]
            # A single element in a list field is enough to move away from the default.
            pytest.param(
                Mixed.default(),
                Mixed(b=Uint16List4(data=[Uint16(0)])),  # ty: ignore[missing-argument]
                id="mixed_container",
            ),
            pytest.param(Square.default(), Square(color=Uint8(1)), id="progressive_container"),  # ty: ignore[missing-argument]
        ],
    )
    def test_is_zero_holds_only_for_the_default(
        self, default_value: _SSZContainer, non_default_value: _SSZContainer
    ) -> None:
        """A default reads as zeroed and any other value of the same type does not."""
        assert default_value.is_zero() is True
        assert non_default_value.is_zero() is False

    def test_a_struct_with_no_field_at_all_is_zeroed(self) -> None:
        """A zero-field struct has one value, which is therefore its default."""
        assert EmptyContainer().is_zero() is True

    @pytest.mark.parametrize(
        "default_value, expected_hex",
        [
            # Two zero Uint64 give sixteen zero bytes.
            pytest.param(TwoUint64.default(), "00" * 16, id="fixed_container"),
            # Fixed part of 20 bytes, both offsets pointing at 20, and no tail payload.
            pytest.param(
                Mixed.default(),
                "0000000000000000" + "14000000" + "00000000" + "14000000",
                id="mixed_container",
            ),
            # Two bytes for side and one for color: a gap costs nothing.
            pytest.param(Square.default(), "000000", id="progressive_container"),
            pytest.param(OuterFixedNested.default(), "00" * 24, id="nested_container"),
        ],
    )
    def test_the_default_round_trips(self, default_value: SSZType, expected_hex: str) -> None:
        """Each default encodes to known bytes and decodes back unchanged."""
        assert default_value.encode_bytes().hex() == expected_hex
        assert type(default_value).decode_bytes(default_value.encode_bytes()) == default_value

    def test_a_struct_holding_a_union_has_no_default(self) -> None:
        """A union has no default, and the struct inherits that absence through the field."""
        with pytest.raises(SSZDefaultError, match=r"^TagUnion has no default value$"):
            ContainerWithUnion.default()

    def test_a_struct_holding_a_union_still_builds_when_the_union_is_given(self) -> None:
        """Only the absent union fails: naming it leaves every other field at its default."""
        value = ContainerWithUnion(body=TagUnion(selector=Uint8(1), data=Uint8(7)))  # ty: ignore[missing-argument]
        assert value.tag == Uint8(0)
        assert value.body == TagUnion(selector=Uint8(1), data=Uint8(7))


class TestProgressiveContainerMutation:
    """
    The progressive shape mutates on the terms the shared base sets.

    Field assignment, coercion, and root-based hashing live on that base, so
    the progressive shape carries them without declaring anything itself.
    """

    def test_field_assignment_revalidates(self) -> None:
        """Assigning a field replaces the value through full revalidation."""
        square = Square(side=Uint16(0x1234), color=Uint8(0x42))
        square.side = Uint16(0x5678)
        assert square == Square(side=Uint16(0x5678), color=Uint8(0x42))

    def test_field_assignment_coerces_a_raw_value(self) -> None:
        """A raw integer coerces into the declared field type, exactly as at construction."""
        square = Square(side=Uint16(0x1234), color=Uint8(0x42))
        square.color = 0x99  # ty: ignore[invalid-assignment]
        assert square == Square(side=Uint16(0x1234), color=Uint8(0x99))

    def test_field_assignment_rejects_an_out_of_range_value(self) -> None:
        """A value the field type cannot hold is rejected, leaving the field unchanged."""
        square = Square(side=Uint16(0x1234), color=Uint8(0x42))
        with pytest.raises((SSZTypeError, ValidationError)):
            square.color = 256  # ty: ignore[invalid-assignment]
        assert square.color == Uint8(0x42)

    def test_mutation_moves_the_encoding_and_the_root(self) -> None:
        """A mutated value encodes and merkleizes as the value it now holds."""
        mutated = Square(side=Uint16(0x1234), color=Uint8(0x42))
        mutated.color = Uint8(0x99)
        rebuilt = Square(side=Uint16(0x1234), color=Uint8(0x99))
        assert mutated.encode_bytes() == rebuilt.encode_bytes()
        assert hash_tree_root(mutated) == hash_tree_root(rebuilt)

    def test_hashes_by_tree_root(self) -> None:
        """Equal progressive containers hash equally, so they work as dict keys."""
        first = Square(side=Uint16(0x1234), color=Uint8(0x42))
        second = Square(side=Uint16(0x1234), color=Uint8(0x42))
        assert hash(first) == hash(second)
        assert {first: "found"}[second] == "found"

    def test_two_layouts_holding_the_same_fields_hash_apart(self) -> None:
        """The layout is mixed into the root, so it separates two otherwise equal values."""
        square = Square(side=Uint16(0x1234), color=Uint8(0x42))
        circle = Circle(radius=Uint16(0x1234), color=Uint8(0x42))
        # The same three bytes on the wire, and two different roots, so two different hashes.
        assert square.encode_bytes() == circle.encode_bytes()
        assert hash(square) != hash(circle)

    def test_a_progressive_field_mutates_in_place(self) -> None:
        """A progressive collection held as a field grows through the field itself."""
        instance = ProgressiveFieldsProgressive(
            head=Uint32(1),
            numbers=Uint16ProgressiveList(data=[Uint16(1)]),
            flags=ProgressiveBitList(data=[Boolean(True)]),
        )
        instance.numbers.append(Uint16(2))
        instance.flags.append(Boolean(False))
        assert instance == ProgressiveFieldsProgressive(
            head=Uint32(1),
            numbers=Uint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
            flags=ProgressiveBitList(data=[Boolean(True), Boolean(False)]),
        )


@given(
    a=st.integers(min_value=0, max_value=2**64 - 1),
    b=st.lists(st.integers(min_value=0, max_value=2**16 - 1), max_size=4),
    c=st.integers(min_value=0, max_value=2**32 - 1),
    d=st.lists(st.integers(min_value=0, max_value=2**16 - 1), max_size=4),
)
def test_mixed_container_round_trip_random_values(
    a: int, b: list[int], c: int, d: list[int]
) -> None:
    """Any mix of fixed and variable field values round-trips unchanged."""
    instance = Mixed(
        a=Uint64(a),
        b=Uint16List4(data=[Uint16(value) for value in b]),
        c=Uint32(c),
        d=Uint16List4(data=[Uint16(value) for value in d]),
    )
    assert Mixed.decode_bytes(instance.encode_bytes()) == instance


@given(
    head=st.integers(min_value=0, max_value=2**32 - 1),
    numbers=st.lists(st.integers(min_value=0, max_value=2**16 - 1), max_size=6),
    flags=st.lists(st.booleans(), max_size=9),
)
def test_progressive_container_round_trip_random_values(
    head: int, numbers: list[int], flags: list[bool]
) -> None:
    """Any mix of fixed and progressive field values round-trips unchanged."""
    instance = ProgressiveFieldsProgressive(
        head=Uint32(head),
        numbers=Uint16ProgressiveList(data=[Uint16(value) for value in numbers]),
        flags=ProgressiveBitList(data=[Boolean(bit) for bit in flags]),
    )
    assert ProgressiveFieldsProgressive.decode_bytes(instance.encode_bytes()) == instance
