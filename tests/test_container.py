"""Tests for the SSZ Container base class and the EIP-7495 progressive container."""

import io
from collections.abc import Sequence

import pytest
from hypothesis import given, strategies as st
from pydantic import ValidationError

from ssz.bitfields import ProgressiveBitlist
from ssz.boolean import Boolean
from ssz.collections import List, ProgressiveList
from ssz.container import (
    MAX_ACTIVE_FIELDS,
    Container,
    ProgressiveContainer,
    _SSZContainer,
)
from ssz.exceptions import (
    SSZActiveFieldsError,
    SSZDefinitionError,
    SSZSerializationError,
    SSZTypeError,
)
from ssz.uint import Uint8, Uint16, Uint32, Uint64


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
    flags: ProgressiveBitlist


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
                r"  Value error, invalid OneByte hex: "
                r"OneByte: 1 trailing byte\(s\) after decode "
                r"\[type=value_error, input_value='abcd', input_type=str\]\n"
                r"    For further information visit "
                r"https://errors\.pydantic\.dev/[^/]+/v/value_error\Z"
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
                rf"^TooWide: invalid active fields, the layout holds "
                rf"{position_count} positions, over the limit of 256$"
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
                r"the layout sets 2 positions, and the struct declares 1$"
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
                r"the layout sets 1 positions, and the struct declares 2$"
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
                r"the layout sets 1 positions, and the struct declares 0$"
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
                r"the layout sets 2 positions, and the struct declares 3$"
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
            flags=ProgressiveBitlist(data=[Boolean(True), Boolean(False), Boolean(True)]),
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
            flags=ProgressiveBitlist(data=[Boolean(True)]),
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
        # Two bytes feed `side` and leave nothing for `color`.
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
        flags=ProgressiveBitlist(data=[Boolean(bit) for bit in flags]),
    )
    assert ProgressiveFieldsProgressive.decode_bytes(instance.encode_bytes()) == instance
