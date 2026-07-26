"""Tests for the Bitvector and Bitlist types."""

import io
from typing import Any

import pytest
from hypothesis import given, strategies as st
from pydantic import BaseModel, ValidationError

from ssz.bitfields import BaseBitlist, BaseBitvector, ProgressiveBitlist
from ssz.boolean import Boolean
from ssz.exceptions import SSZSerializationError, SSZTypeError, SSZValueError

# Errors that may be raised either directly or wrapped by Pydantic at construction time.
ValueOrValidationError = (SSZValueError, ValidationError)


class Bitvector4(BaseBitvector):
    """A bitvector of exactly 4 bits."""

    LENGTH = 4


class Bitvector4Model(BaseModel):
    """Model for testing Pydantic validation of Bitvector4."""

    value: Bitvector4


class Bitlist8(BaseBitlist):
    """A bitlist with up to 8 bits."""

    LIMIT = 8


class Bitlist8Model(BaseModel):
    """Model for testing Pydantic validation of Bitlist8."""

    value: Bitlist8


class ProgressiveBitlistModel(BaseModel):
    """Model for testing Pydantic validation of ProgressiveBitlist."""

    value: ProgressiveBitlist


def bits_of(*values: int) -> tuple[Boolean, ...]:
    """Build a typed boolean tuple from 0/1 integers."""
    return tuple(Boolean(bool(bit)) for bit in values)


class TestBitvector:
    """Tests for the fixed-length Bitvector type."""

    def test_class_creates_specialized_type(self) -> None:
        """Concrete Bitvector classes carry the declared length."""

        class Bitvector8(BaseBitvector):
            LENGTH = 8

        class Bitvector16(BaseBitvector):
            LENGTH = 16

        assert Bitvector8.LENGTH == 8
        assert Bitvector16.LENGTH == 16
        assert "Bitvector8" in repr(Bitvector8)

    def test_instantiate_raw_type_raises_error(self) -> None:
        """Direct instantiation of the abstract base raises SSZTypeError."""
        with pytest.raises(SSZTypeError) as exception_info:
            BaseBitvector(data=[])
        assert str(exception_info.value) == "BaseBitvector must define LENGTH"

    def test_instantiation_success(self) -> None:
        """Instantiation succeeds with exactly LENGTH boolean items."""
        instance = Bitvector4(data=[Boolean(True), Boolean(False), Boolean(1), Boolean(0)])
        assert len(instance) == 4
        assert instance == Bitvector4(
            data=[Boolean(True), Boolean(False), Boolean(True), Boolean(False)]
        )

    def test_instantiation_from_generator(self) -> None:
        """Fixed-length type materializes a generator into a tuple before validation."""
        bit_generator = (Boolean(bit) for bit in [True, False, True, False])
        instance = Bitvector4(data=bit_generator)  # type: ignore[arg-type]
        assert len(instance) == 4

    @pytest.mark.parametrize(
        "bits, expected_element_count",
        [
            ([Boolean(True), Boolean(False), Boolean(True)], 3),
            (
                [Boolean(True), Boolean(False), Boolean(True), Boolean(False), Boolean(True)],
                5,
            ),
        ],
    )
    def test_instantiation_with_wrong_length_raises_error(
        self, bits: list[Boolean], expected_element_count: int
    ) -> None:
        """Wrong-length input raises with the exact element count in the message."""
        with pytest.raises(ValueOrValidationError) as exception_info:
            Bitvector4(data=bits)
        assert (
            str(exception_info.value)
            == f"Bitvector4 requires exactly 4 elements, got {expected_element_count}"
        )

    def test_pydantic_validation_accepts_valid_list(self) -> None:
        """Pydantic validation accepts a valid list of booleans."""
        bits = [Boolean(True), Boolean(False), Boolean(True), Boolean(False)]
        instance = Bitvector4Model(value={"data": bits})  # type: ignore[arg-type]
        assert isinstance(instance.value, Bitvector4)
        assert instance.value == Bitvector4(data=bits)

    @pytest.mark.parametrize(
        "invalid_value",
        [
            {"data": [Boolean(True), Boolean(False), Boolean(True)]},
            {"data": [Boolean(bit) for bit in [True, False, True, False, True]]},
        ],
    )
    def test_pydantic_validation_rejects_wrong_length(self, invalid_value: Any) -> None:
        """Pydantic validation rejects lists of the wrong length."""
        with pytest.raises(ValueOrValidationError):
            Bitvector4Model(value=invalid_value)

    def test_bitvector_item_assignment_revalidates(self) -> None:
        """Item assignment replaces the bit through full revalidation."""

        class Bitvector2(BaseBitvector):
            LENGTH = 2

        vec = Bitvector2(data=[Boolean(True), Boolean(False)])
        vec[0] = Boolean(False)
        assert vec == Bitvector2(data=[Boolean(False), Boolean(False)])


class TestBitlist:
    """Tests for the variable-length Bitlist type."""

    def test_class_creates_specialized_type(self) -> None:
        """Concrete Bitlist classes carry the declared limit."""

        class Bitlist8(BaseBitlist):
            LIMIT = 8

        class Bitlist16(BaseBitlist):
            LIMIT = 16

        assert Bitlist8.LIMIT == 8
        assert Bitlist16.LIMIT == 16
        assert "Bitlist8" in repr(Bitlist8)

    def test_instantiate_raw_type_raises_error(self) -> None:
        """Direct instantiation of the abstract base raises SSZTypeError."""
        with pytest.raises(SSZTypeError) as exception_info:
            BaseBitlist(data=[])
        assert str(exception_info.value) == "BaseBitlist must define LIMIT"

    def test_instantiation_success(self) -> None:
        """Instantiation succeeds with any number of items up to LIMIT."""
        instance = Bitlist8(data=[Boolean(True), Boolean(False), Boolean(1), Boolean(0)])
        assert len(instance) == 4
        expected_bitlist = Bitlist8(
            data=[Boolean(True), Boolean(False), Boolean(True), Boolean(False)]
        )
        assert instance == expected_bitlist

    def test_instantiation_from_generator(self) -> None:
        """Variable-length type materializes a generator into a list before validation."""
        bit_generator = (Boolean(bit) for bit in [True, False, True])
        instance = Bitlist8(data=bit_generator)  # type: ignore[arg-type]
        assert len(instance) == 3

    @pytest.mark.parametrize(
        "non_iterable, type_name",
        [
            (42, "int"),
            (None, "NoneType"),
            (1.5, "float"),
        ],
    )
    def test_instantiation_from_non_iterable_raises(
        self, non_iterable: Any, type_name: str
    ) -> None:
        """Non-iterable input raises SSZTypeError naming the offending type."""
        with pytest.raises((SSZTypeError, ValidationError)) as exception_info:
            Bitlist8(data=non_iterable)
        assert str(exception_info.value) == f"Expected iterable, got {type_name}"

    @pytest.mark.parametrize("rejected", ["0101", b"\x00\x01"])
    def test_instantiation_from_str_or_bytes_raises(self, rejected: Any) -> None:
        """str and bytes are iterable but explicitly rejected — their elements are not booleans."""
        type_name = type(rejected).__name__
        with pytest.raises((SSZTypeError, ValidationError)) as exception_info:
            Bitlist8(data=rejected)
        assert str(exception_info.value) == f"Expected iterable, got {type_name}"

    def test_instantiation_over_limit_raises_error(self) -> None:
        """Input exceeding LIMIT raises with the exact size in the message."""

        class Bitlist4(BaseBitlist):
            LIMIT = 4

        with pytest.raises(ValueOrValidationError) as exception_info:
            Bitlist4(data=[Boolean(bit) for bit in [True, False, True, False, True]])
        assert str(exception_info.value) == "Bitlist4 exceeds limit of 4, got 5"

    def test_pydantic_validation_accepts_valid_list(self) -> None:
        """Pydantic validation accepts a valid list of booleans."""
        bits = [Boolean(True), Boolean(False), Boolean(True), Boolean(False)]
        instance = Bitlist8Model(value={"data": bits})  # type: ignore[arg-type]
        assert isinstance(instance.value, Bitlist8)
        assert len(instance.value) == 4

    def test_pydantic_validation_rejects_oversized_list(self) -> None:
        """Pydantic validation rejects lists exceeding the limit."""
        invalid_value = {"data": [Boolean(True)] * 9}
        with pytest.raises(ValueOrValidationError):
            Bitlist8Model(value=invalid_value)  # type: ignore[arg-type]

    def test_get_item_int(self) -> None:
        """Indexing by int returns the Boolean at that position."""
        bitlist = Bitlist8(data=[Boolean(True), Boolean(False), Boolean(True)])
        assert bitlist[0] == Boolean(True)
        assert bitlist[1] == Boolean(False)
        assert bitlist[2] == Boolean(True)

    def test_get_item_slice(self) -> None:
        """Indexing by slice returns a list of Booleans."""
        bitlist = Bitlist8(data=[Boolean(True), Boolean(False), Boolean(True), Boolean(False)])
        sliced_bits = bitlist[1:3]
        assert sliced_bits == [Boolean(False), Boolean(True)]
        assert isinstance(sliced_bits, list)

    def test_add_with_list(self) -> None:
        """Concatenating a Bitlist with a list returns a new instance."""
        bitlist = Bitlist8(data=[Boolean(True), Boolean(False), Boolean(True)])
        concatenated = bitlist + [Boolean(False), Boolean(True)]
        assert len(concatenated) == 5
        assert list(concatenated.data) == [
            Boolean(True),
            Boolean(False),
            Boolean(True),
            Boolean(False),
            Boolean(True),
        ]
        assert isinstance(concatenated, Bitlist8)

    def test_add_with_bitlist(self) -> None:
        """Concatenating two Bitlists of the same type returns a new instance."""
        bitlist1 = Bitlist8(data=[Boolean(True), Boolean(False)])
        bitlist2 = Bitlist8(data=[Boolean(True), Boolean(True)])
        concatenated = bitlist1 + bitlist2
        assert len(concatenated) == 4
        assert list(concatenated.data) == [
            Boolean(True),
            Boolean(False),
            Boolean(True),
            Boolean(True),
        ]
        assert isinstance(concatenated, Bitlist8)

    def test_add_with_unsupported_type_raises(self) -> None:
        """Adding an unsupported type returns NotImplemented and Python raises TypeError."""
        bitlist = Bitlist8(data=[Boolean(True)])
        with pytest.raises(TypeError):
            _ = bitlist + 42

    def test_add_exceeding_limit_raises_error(self) -> None:
        """Concatenation beyond LIMIT raises with the exact size in the message."""

        class Bitlist4(BaseBitlist):
            LIMIT = 4

        bitlist = Bitlist4(data=[Boolean(True), Boolean(False), Boolean(True)])
        with pytest.raises(ValueOrValidationError) as exception_info:
            _ = bitlist + [Boolean(False), Boolean(True)]
        assert str(exception_info.value) == "Bitlist4 exceeds limit of 4, got 5"


class TestProgressiveBitlist:
    """Tests for the uncapped ProgressiveBitlist type."""

    def test_instantiation_success(self) -> None:
        """Instantiation succeeds with any number of bit-like items."""
        instance = ProgressiveBitlist(data=[Boolean(True), Boolean(False), Boolean(1), Boolean(0)])

        assert len(instance) == 4
        assert instance == ProgressiveBitlist(data=bits_of(1, 0, 1, 0))

    def test_default_value_is_empty(self) -> None:
        """The default value is the empty bitlist."""
        assert len(ProgressiveBitlist()) == 0
        assert ProgressiveBitlist() == ProgressiveBitlist(data=())

    def test_instantiation_from_generator(self) -> None:
        """A generator is materialized into a list before validation."""
        bit_generator = (Boolean(bit) for bit in [True, False, True])
        instance = ProgressiveBitlist(data=bit_generator)  # type: ignore[arg-type]

        assert len(instance) == 3

    def test_no_bit_count_is_ever_rejected(self) -> None:
        """No capacity is declared, so any bit count validates."""
        instance = ProgressiveBitlist(data=[Boolean(True)] * 4096)

        assert len(instance) == 4096

    def test_no_limit_is_declared(self) -> None:
        """The shape carries no capacity attribute at all."""
        assert not hasattr(ProgressiveBitlist, "LIMIT")

    @pytest.mark.parametrize(
        "non_iterable, type_name",
        [
            (42, "int"),
            (None, "NoneType"),
            (1.5, "float"),
        ],
    )
    def test_instantiation_from_non_iterable_raises(
        self, non_iterable: Any, type_name: str
    ) -> None:
        """Non-iterable input raises SSZTypeError naming the offending type."""
        with pytest.raises((SSZTypeError, ValidationError)) as exception_info:
            ProgressiveBitlist(data=non_iterable)
        assert str(exception_info.value) == f"Expected iterable, got {type_name}"

    @pytest.mark.parametrize("rejected", ["0101", b"\x00\x01"])
    def test_instantiation_from_str_or_bytes_raises(self, rejected: Any) -> None:
        """str and bytes are iterable but explicitly rejected — their elements are not booleans."""
        type_name = type(rejected).__name__
        with pytest.raises((SSZTypeError, ValidationError)) as exception_info:
            ProgressiveBitlist(data=rejected)
        assert str(exception_info.value) == f"Expected iterable, got {type_name}"

    def test_pydantic_validation_accepts_any_bit_count(self) -> None:
        """Pydantic validation accepts a bit list of any width."""
        instance = ProgressiveBitlistModel(value={"data": [Boolean(True)] * 300})  # type: ignore[arg-type]

        assert isinstance(instance.value, ProgressiveBitlist)
        assert len(instance.value) == 300

    def test_get_item_int(self) -> None:
        """Indexing by int returns the Boolean at that position."""
        bitlist = ProgressiveBitlist(data=bits_of(1, 0, 1))

        assert bitlist[0] == Boolean(True)
        assert bitlist[1] == Boolean(False)
        assert bitlist[-1] == Boolean(True)

    def test_get_item_slice(self) -> None:
        """Indexing by slice returns a list of Booleans."""
        bitlist = ProgressiveBitlist(data=bits_of(1, 0, 1, 0))
        sliced_bits = bitlist[1:3]

        assert sliced_bits == [Boolean(False), Boolean(True)]
        assert isinstance(sliced_bits, list)

    def test_add_with_list(self) -> None:
        """Concatenating with a plain list coerces the right-hand values."""
        concatenated = ProgressiveBitlist(data=bits_of(1, 0, 1)) + [Boolean(False), Boolean(True)]

        assert concatenated == ProgressiveBitlist(data=bits_of(1, 0, 1, 0, 1))
        assert isinstance(concatenated, ProgressiveBitlist)

    def test_add_with_progressive_bitlist(self) -> None:
        """Concatenating two progressive bitlists yields a fresh instance of the same type."""
        concatenated = ProgressiveBitlist(data=bits_of(1, 0)) + ProgressiveBitlist(
            data=bits_of(1, 1)
        )

        assert concatenated == ProgressiveBitlist(data=bits_of(1, 0, 1, 1))

    def test_add_with_bounded_bitlist_keeps_the_left_shape(self) -> None:
        """Both bitlist shapes share the concatenation hook; the left operand's type wins."""
        concatenated = ProgressiveBitlist(data=bits_of(1)) + Bitlist8(data=bits_of(0, 1))

        assert concatenated == ProgressiveBitlist(data=bits_of(1, 0, 1))
        assert isinstance(concatenated, ProgressiveBitlist)

    def test_add_with_unsupported_type_raises(self) -> None:
        """Adding an unsupported type returns NotImplemented and Python raises TypeError."""
        bitlist = ProgressiveBitlist(data=bits_of(1))

        with pytest.raises(TypeError):
            _ = bitlist + 42

    def test_add_never_overflows_a_capacity(self) -> None:
        """Concatenation has no capacity to overflow, so it always revalidates cleanly."""
        base = ProgressiveBitlist(data=[Boolean(True)] * 500)

        assert len(base + base) == 1000

    def test_progressive_bitlist_item_assignment_revalidates(self) -> None:
        """Item assignment replaces the bit through full revalidation."""
        bitlist = ProgressiveBitlist(data=bits_of(1, 0))
        bitlist[0] = Boolean(False)
        assert bitlist == ProgressiveBitlist(data=bits_of(0, 0))

    def test_progressive_bitlist_grows_without_a_capacity(self) -> None:
        """Append and pop work, and no capacity bounds the growth."""
        bitlist = ProgressiveBitlist(data=bits_of(1))
        bitlist.append(Boolean(False))
        assert bitlist == ProgressiveBitlist(data=bits_of(1, 0))
        assert bitlist.pop() == Boolean(False)
        assert bitlist == ProgressiveBitlist(data=bits_of(1))

    def test_progressive_bitlist_appends_past_a_bounded_limit(self) -> None:
        """Growth runs past the bit count a bounded bitlist of the same shape refuses."""
        bounded = Bitlist8(data=bits_of(1, 1, 1, 1, 1, 1, 1, 1))
        with pytest.raises(ValueOrValidationError):
            bounded.append(Boolean(True))

        # The same shape with no capacity keeps going, well past that limit.
        bitlist = ProgressiveBitlist(data=())
        for _ in range(100):
            bitlist.append(Boolean(True))
        assert len(bitlist) == 100
        assert bitlist == ProgressiveBitlist(data=[Boolean(True)] * 100)

    def test_progressive_bitlist_slice_assignment_resizes(self) -> None:
        """Slice assignment replaces a range, and may change the bit count either way."""
        bitlist = ProgressiveBitlist(data=bits_of(1, 1, 1))
        bitlist[1:] = bits_of(0)
        assert bitlist == ProgressiveBitlist(data=bits_of(1, 0))
        bitlist[0:1] = bits_of(0, 1, 1)
        assert bitlist == ProgressiveBitlist(data=bits_of(0, 1, 1, 0))

    def test_progressive_bitlist_mutation_coerces_raw_bits(self) -> None:
        """Mutation wraps a raw bool in Boolean, exactly as construction does."""
        bitlist = ProgressiveBitlist(data=bits_of(1))
        bitlist.append(False)  # ty: ignore[invalid-argument-type]
        bitlist[0] = False  # ty: ignore[invalid-assignment]
        assert bitlist == ProgressiveBitlist(data=bits_of(0, 0))
        assert all(type(bit) is Boolean for bit in bitlist.data)

    def test_progressive_bitlist_mutation_rejects_a_non_bit(self) -> None:
        """A value outside 0 and 1 is refused, leaving the stored bits untouched."""
        bitlist = ProgressiveBitlist(data=bits_of(1))
        with pytest.raises(SSZValueError):
            bitlist.append(2)  # ty: ignore[invalid-argument-type]
        assert bitlist == ProgressiveBitlist(data=bits_of(1))

    def test_progressive_bitlist_mutation_moves_the_encoding(self) -> None:
        """A mutated bitlist encodes as the bits it now holds, delimiter included."""
        bitlist = ProgressiveBitlist(data=bits_of(1, 0, 1))
        bitlist.append(Boolean(True))
        assert bitlist.encode_bytes() == ProgressiveBitlist(data=bits_of(1, 0, 1, 1)).encode_bytes()
        assert ProgressiveBitlist.decode_bytes(bitlist.encode_bytes()) == bitlist

    def test_is_variable_size_with_no_fixed_byte_length(self) -> None:
        """The shape reports variable-size and refuses to name a byte width."""
        assert ProgressiveBitlist.is_fixed_size() is False
        with pytest.raises(SSZTypeError) as exception_info:
            ProgressiveBitlist.get_byte_length()
        assert (
            str(exception_info.value)
            == "ProgressiveBitlist: variable-size bitlist has no fixed byte length"
        )

    @pytest.mark.parametrize(
        "bits, expected_hex",
        [
            # Empty: the delimiter alone still costs one byte.
            ((), "01"),
            ((1,), "03"),
            ((0, 1, 0), "0a"),
            ((1, 1, 0, 1, 0, 1, 0, 0), "2b01"),
            ((1, 0, 1, 0, 0, 0, 1, 1, 0, 1), "c506"),
            # 255 data bits leave exactly one free bit for the delimiter.
            (tuple([1] * 255), "ff" * 32),
            # 256 data bits push the delimiter into a fresh byte.
            (tuple([1] * 256), ("ff" * 32) + "01"),
            # 257 data bits put one data bit and the delimiter in the final byte.
            (tuple([1] * 257), ("ff" * 32) + "03"),
        ],
    )
    def test_round_trip(self, bits: tuple[int, ...], expected_hex: str) -> None:
        """Encoding matches the delimited layout and decoding recovers the bits."""
        instance = ProgressiveBitlist(data=bits_of(*bits))

        encoded = instance.encode_bytes()
        assert encoded.hex() == expected_hex

        assert ProgressiveBitlist.decode_bytes(encoded) == instance

        stream = io.BytesIO()
        written = instance.serialize(stream)
        assert written == len(encoded)
        stream.seek(0)
        assert ProgressiveBitlist.deserialize(stream, scope=written) == instance

    def test_decode_accepts_any_bit_count(self) -> None:
        """A bit count a bounded bitlist would reject decodes without complaint."""
        # Bytes [0xFF, 0xFF, 0x01] mean 16 data bits with the delimiter at bit 16.
        assert ProgressiveBitlist.decode_bytes(b"\xff\xff\x01") == ProgressiveBitlist(
            data=[Boolean(True)] * 16
        )

    def test_decode_empty_bytes(self) -> None:
        """Decoding rejects an empty byte sequence — the empty bitlist still costs a byte."""
        with pytest.raises(SSZSerializationError) as exception_info:
            ProgressiveBitlist.decode_bytes(b"")
        assert str(exception_info.value) == "ProgressiveBitlist: cannot decode empty bytes"

    def test_decode_all_zero_bytes(self) -> None:
        """Decoding rejects input with no 1 bits — there is no delimiter to locate."""
        with pytest.raises(SSZSerializationError) as exception_info:
            ProgressiveBitlist.decode_bytes(b"\x00")
        assert str(exception_info.value) == "ProgressiveBitlist: no delimiter bit found"

    def test_decode_rejects_non_canonical_trailing_zero_byte(self) -> None:
        """Decoding rejects a trailing zero byte after the delimiter byte."""
        with pytest.raises(SSZSerializationError) as exception_info:
            ProgressiveBitlist.decode_bytes(b"\x0d\x00")
        assert (
            str(exception_info.value)
            == "ProgressiveBitlist: non-canonical trailing zero bytes after delimiter"
        )

    def test_deserialize_premature_end(self) -> None:
        """Deserializing rejects a stream that ends before the declared scope."""
        stream = io.BytesIO(b"\xff")
        with pytest.raises(SSZSerializationError) as exception_info:
            ProgressiveBitlist.deserialize(stream, scope=2)
        assert str(exception_info.value) == "ProgressiveBitlist: expected 2 bytes, got 1"

    def test_bytes_match_the_bounded_bitlist_encoding(self) -> None:
        """The wire format matches a bounded bitlist of the same bits, delimiter included."""
        bits = bits_of(1, 0, 1)
        progressive = ProgressiveBitlist(data=bits)
        bounded = Bitlist8(data=bits)

        assert progressive.encode_bytes() == bounded.encode_bytes()
        # The same bytes therefore decode under either shape.
        assert Bitlist8.decode_bytes(progressive.encode_bytes()) == bounded
        assert ProgressiveBitlist.decode_bytes(bounded.encode_bytes()) == progressive


class TestBitfieldSSZ:
    """SSZ interface methods and end-to-end serialization round-trips."""

    def test_bitvector_is_fixed_size(self) -> None:
        """Bitvector reports fixed-size and computes byte length via ceil(LENGTH / 8)."""

        class Bitvector10(BaseBitvector):
            LENGTH = 10

        assert Bitvector10.is_fixed_size() is True
        assert Bitvector10.get_byte_length() == 2

    def test_bitlist_is_variable_size(self) -> None:
        """Bitlist reports variable-size and get_byte_length raises."""

        class Bitlist10(BaseBitlist):
            LIMIT = 10

        assert Bitlist10.is_fixed_size() is False
        with pytest.raises(SSZTypeError) as exception_info:
            Bitlist10.get_byte_length()
        assert (
            str(exception_info.value) == "Bitlist10: variable-size bitlist has no fixed byte length"
        )

    @pytest.mark.parametrize(
        "length, bits, expected_hex",
        [
            (8, (1, 1, 0, 1, 0, 1, 0, 0), "2b"),
            (4, (0, 1, 0, 1), "0a"),
            (3, (0, 1, 0), "02"),
            (10, (1, 0, 1, 0, 0, 0, 1, 1, 0, 1), "c502"),
            (16, (1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1), "c5c2"),
            (512, tuple([1] * 512), "ff" * 64),
            (513, tuple([1] * 513), ("ff" * 64) + "01"),
        ],
    )
    def test_bitvector_round_trip(
        self, length: int, bits: tuple[int, ...], expected_hex: str
    ) -> None:
        """Bitvector round-trips through encode_bytes, decode_bytes, and stream serialization."""

        class TestBitvector(BaseBitvector):
            LENGTH = length

        boolean_bits = tuple(Boolean(bit) for bit in bits)
        instance = TestBitvector(data=boolean_bits)

        encoded = instance.encode_bytes()
        assert encoded.hex() == expected_hex

        decoded = TestBitvector.decode_bytes(encoded)
        assert decoded == instance

        stream = io.BytesIO()
        written = instance.serialize(stream)
        assert written == TestBitvector.get_byte_length()
        stream.seek(0)
        decoded2 = TestBitvector.deserialize(stream, scope=written)
        assert decoded2 == instance

    @pytest.mark.parametrize(
        "limit, bits, expected_hex",
        [
            (8, (), "01"),
            (8, (1, 1, 0, 1, 0, 1, 0, 0), "2b01"),
            (4, (0, 1, 0, 1), "1a"),
            (3, (0, 1, 0), "0a"),
            (16, (1, 0, 1, 0, 0, 0, 1, 1, 0, 1), "c506"),
            (512, (1,), "03"),
            (512, tuple([1] * 512), ("ff" * 64) + "01"),
            (513, tuple([1] * 513), ("ff" * 64) + "03"),
        ],
    )
    def test_bitlist_round_trip(self, limit: int, bits: tuple[int, ...], expected_hex: str) -> None:
        """Bitlist round-trips through encode_bytes, decode_bytes, and stream serialization."""

        class TestBitlist(BaseBitlist):
            LIMIT = limit

        boolean_bits = tuple(Boolean(bit) for bit in bits)
        instance = TestBitlist(data=boolean_bits)

        encoded = instance.encode_bytes()
        assert encoded.hex() == expected_hex

        decoded = TestBitlist.decode_bytes(encoded)
        assert decoded == instance

        stream = io.BytesIO()
        written = instance.serialize(stream)
        assert written == len(encoded)
        stream.seek(0)
        decoded2 = TestBitlist.deserialize(stream, scope=written)
        assert decoded2 == instance

    def test_bitvector_decode_invalid_length(self) -> None:
        """Bitvector.decode_bytes rejects inputs whose byte count is wrong."""

        class Bitvector8(BaseBitvector):
            LENGTH = 8

        with pytest.raises(SSZValueError) as exception_info:
            Bitvector8.decode_bytes(b"\x01\x02")
        assert str(exception_info.value) == "Bitvector8: expected 1 bytes, got 2"

    def test_bitvector_decode_rejects_non_zero_padding_bits(self) -> None:
        """Bitvector.decode_bytes rejects a final byte with set bits above the data bits."""

        class Bitvector5(BaseBitvector):
            LENGTH = 5

        # Bits 5, 6, 7 are padding above the 5 data bits and must be zero.
        # 0b11111111 sets them, so it is a non-canonical encoding of [1] * 5.
        with pytest.raises(SSZValueError) as exception_info:
            Bitvector5.decode_bytes(b"\xff")
        assert str(exception_info.value) == "Bitvector5: non-zero padding bits in final byte 0xff"

    def test_bitvector_decode_canonical_with_zero_padding_bits(self) -> None:
        """Bitvector.decode_bytes accepts the canonical encoding with zero padding bits."""

        class Bitvector5(BaseBitvector):
            LENGTH = 5

        # 0b00011111 holds 5 data bits all set with zero padding above them.
        assert Bitvector5.decode_bytes(b"\x1f") == Bitvector5(data=[Boolean(True)] * 5)

    def test_bitvector_deserialize_invalid_scope(self) -> None:
        """Bitvector.deserialize rejects a scope mismatching the type's byte length."""

        class Bitvector8(BaseBitvector):
            LENGTH = 8

        stream = io.BytesIO(b"\xff")
        with pytest.raises(SSZSerializationError) as exception_info:
            Bitvector8.deserialize(stream, scope=2)
        assert str(exception_info.value) == "Bitvector8: expected 1 bytes, got 2"

    def test_bitvector_deserialize_premature_end(self) -> None:
        """Bitvector.deserialize rejects a stream that ends before the declared scope."""

        class Bitvector16(BaseBitvector):
            LENGTH = 16

        stream = io.BytesIO(b"\xff")
        with pytest.raises(SSZSerializationError) as exception_info:
            Bitvector16.deserialize(stream, scope=2)
        assert str(exception_info.value) == "Bitvector16: expected 2 bytes, got 1"

    def test_bitlist_decode_empty_bytes(self) -> None:
        """Bitlist.decode_bytes rejects an empty byte sequence."""

        class Bitlist8(BaseBitlist):
            LIMIT = 8

        with pytest.raises(SSZSerializationError) as exception_info:
            Bitlist8.decode_bytes(b"")
        assert str(exception_info.value) == "Bitlist8: cannot decode empty bytes"

    def test_bitlist_decode_all_zero_bytes(self) -> None:
        """Bitlist.decode_bytes rejects non-empty input with no 1 bits — no delimiter to locate."""

        class Bitlist8(BaseBitlist):
            LIMIT = 8

        with pytest.raises(SSZSerializationError) as exception_info:
            Bitlist8.decode_bytes(b"\x00")
        assert str(exception_info.value) == "Bitlist8: no delimiter bit found"

    def test_bitlist_decode_rejects_non_canonical_trailing_zero_byte(self) -> None:
        """Bitlist.decode_bytes rejects a trailing zero byte after the delimiter byte."""

        class Bitlist8(BaseBitlist):
            LIMIT = 8

        # Byte 0x0d encodes bits [1, 0, 1] with the delimiter at bit 3.
        # Appending a zero byte leaves the delimiter in byte 0, not the final byte.
        with pytest.raises(SSZSerializationError) as exception_info:
            Bitlist8.decode_bytes(b"\x0d\x00")
        assert (
            str(exception_info.value)
            == "Bitlist8: non-canonical trailing zero bytes after delimiter"
        )

    def test_bitlist_decode_canonical_encoding_round_trips(self) -> None:
        """Bitlist.decode_bytes accepts the canonical single-byte encoding of bits [1, 0, 1]."""

        class Bitlist8(BaseBitlist):
            LIMIT = 8

        assert Bitlist8.decode_bytes(b"\x0d") == Bitlist8(
            data=(Boolean(True), Boolean(False), Boolean(True))
        )

    def test_bitlist_decode_exceeds_limit(self) -> None:
        """Bitlist.decode_bytes rejects encodings whose recovered bit count exceeds LIMIT."""

        class Bitlist8(BaseBitlist):
            LIMIT = 8

        # Bytes [0xFF, 0xFF, 0x01] mean 16 data bits + delimiter at bit 16 — > LIMIT=8.
        with pytest.raises(SSZValueError) as exception_info:
            Bitlist8.decode_bytes(b"\xff\xff\x01")
        assert str(exception_info.value) == "Bitlist8 exceeds limit of 8, got 16"

    def test_bitlist_deserialize_premature_end(self) -> None:
        """Bitlist.deserialize rejects a stream that ends before the declared scope."""

        class Bitlist16(BaseBitlist):
            LIMIT = 16

        stream = io.BytesIO(b"\xff")
        with pytest.raises(SSZSerializationError) as exception_info:
            Bitlist16.deserialize(stream, scope=2)
        assert str(exception_info.value) == "Bitlist16: expected 2 bytes, got 1"


@given(bits=st.lists(st.booleans(), max_size=8))
def test_bitlist_round_trip_random_bits(bits: list[bool]) -> None:
    """Any bit pattern up to the limit, including empty, round-trips unchanged."""
    instance = Bitlist8(data=tuple(Boolean(bit) for bit in bits))
    assert Bitlist8.decode_bytes(instance.encode_bytes()) == instance


@given(bits=st.lists(st.booleans(), min_size=4, max_size=4))
def test_bitvector_round_trip_random_bits(bits: list[bool]) -> None:
    """Any fixed-length bit pattern round-trips unchanged."""
    instance = Bitvector4(data=tuple(Boolean(bit) for bit in bits))
    assert Bitvector4.decode_bytes(instance.encode_bytes()) == instance


@given(bits=st.lists(st.booleans(), max_size=300))
def test_progressive_bitlist_round_trip_random_bits(bits: list[bool]) -> None:
    """Any bit pattern round-trips unchanged, at any width and across chunk boundaries."""
    instance = ProgressiveBitlist(data=tuple(Boolean(bit) for bit in bits))
    assert ProgressiveBitlist.decode_bytes(instance.encode_bytes()) == instance


@given(bits=st.lists(st.booleans(), max_size=8))
def test_progressive_and_bounded_bitlist_encode_identically(bits: list[bool]) -> None:
    """The two bitlist shapes agree bit for bit on every pattern they both hold."""
    typed_bits = tuple(Boolean(bit) for bit in bits)
    progressive_bytes = ProgressiveBitlist(data=typed_bits).encode_bytes()

    assert progressive_bytes == Bitlist8(data=typed_bits).encode_bytes()
