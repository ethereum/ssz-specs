"""Tests for the BitVector and BitList types."""

import io
from typing import Any

import pytest
from hypothesis import given, strategies as st
from pydantic import BaseModel, ValidationError

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.exceptions import SSZSerializationError, SSZTypeError, SSZValueError

# Errors that may be raised either directly or wrapped by Pydantic at construction time.
ValueOrValidationError = (SSZValueError, ValidationError)


class BitVector4(BitVector):
    """A bitvector of exactly 4 bits."""

    LENGTH = 4


class BitVector4Model(BaseModel):
    """Model for testing Pydantic validation of BitVector4."""

    value: BitVector4


class BitList8(BitList):
    """A bitlist with up to 8 bits."""

    LIMIT = 8


class BitList8Model(BaseModel):
    """Model for testing Pydantic validation of BitList8."""

    value: BitList8


class ProgressiveBitListModel(BaseModel):
    """Model for testing Pydantic validation of ProgressiveBitList."""

    value: ProgressiveBitList


class LengthlessBitVector(BitVector):
    """A bitvector subclass that never declared its bit count, so it has no default."""


def bits_of(*values: int) -> tuple[Boolean, ...]:
    """Build a typed boolean tuple from 0/1 integers."""
    return tuple(Boolean(bool(bit)) for bit in values)


class TestBitVector:
    """Tests for the fixed-length BitVector type."""

    def test_class_creates_specialized_type(self) -> None:
        """Concrete BitVector classes carry the declared length."""

        class BitVector8(BitVector):
            LENGTH = 8

        class BitVector16(BitVector):
            LENGTH = 16

        assert BitVector8.LENGTH == 8
        assert BitVector16.LENGTH == 16
        assert "BitVector8" in repr(BitVector8)

    def test_instantiate_raw_type_raises_error(self) -> None:
        """Direct instantiation of the abstract base raises SSZTypeError."""
        with pytest.raises(SSZTypeError) as exception_info:
            BitVector(data=[])
        assert str(exception_info.value) == "BitVector must define LENGTH"

    def test_instantiation_success(self) -> None:
        """Instantiation succeeds with exactly LENGTH boolean items."""
        instance = BitVector4(data=[Boolean(True), Boolean(False), Boolean(1), Boolean(0)])
        assert len(instance) == 4
        assert instance == BitVector4(
            data=[Boolean(True), Boolean(False), Boolean(True), Boolean(False)]
        )

    def test_instantiation_from_generator(self) -> None:
        """Fixed-length type materializes a generator into a tuple before validation."""
        bit_generator = (Boolean(bit) for bit in [True, False, True, False])
        instance = BitVector4(data=bit_generator)  # type: ignore[arg-type]
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
            BitVector4(data=bits)
        assert (
            str(exception_info.value)
            == f"BitVector4 requires exactly 4 elements, got {expected_element_count}"
        )

    def test_pydantic_validation_accepts_valid_list(self) -> None:
        """Pydantic validation accepts a valid list of booleans."""
        bits = [Boolean(True), Boolean(False), Boolean(True), Boolean(False)]
        instance = BitVector4Model(value={"data": bits})  # type: ignore[arg-type]
        assert isinstance(instance.value, BitVector4)
        assert instance.value == BitVector4(data=bits)

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
            BitVector4Model(value=invalid_value)

    def test_bitvector_item_assignment_revalidates(self) -> None:
        """Item assignment replaces the bit through full revalidation."""

        class BitVector2(BitVector):
            LENGTH = 2

        vec = BitVector2(data=[Boolean(True), Boolean(False)])
        vec[0] = Boolean(False)
        assert vec == BitVector2(data=[Boolean(False), Boolean(False)])

    def test_bitvector_reads_by_position_from_either_end(self) -> None:
        """A bitvector answers by position, counted from either end."""
        vec = BitVector4(data=bits_of(1, 0, 1, 0))

        #     position from the start:   0  1  2  3
        #     bits:                      1  0  1  0
        #     position from the end:    -4 -3 -2 -1
        assert vec[0] == Boolean(True)
        assert vec[-1] == Boolean(False)
        assert vec[-3] == Boolean(False)

        # A trailing range answers as a list of the bits it spans.
        assert vec[-2:] == [Boolean(True), Boolean(False)]

        # Answering by position and by length is all the host language needs to walk a
        # sequence backwards.
        # A bitvector is therefore reversible without declaring anything further.
        assert list(reversed(vec)) == list(bits_of(0, 1, 0, 1))


class TestBitList:
    """Tests for the variable-length BitList type."""

    def test_class_creates_specialized_type(self) -> None:
        """Concrete BitList classes carry the declared limit."""

        class BitList8(BitList):
            LIMIT = 8

        class BitList16(BitList):
            LIMIT = 16

        assert BitList8.LIMIT == 8
        assert BitList16.LIMIT == 16
        assert "BitList8" in repr(BitList8)

    def test_instantiate_raw_type_raises_error(self) -> None:
        """Direct instantiation of the abstract base raises SSZTypeError."""
        with pytest.raises(SSZTypeError) as exception_info:
            BitList(data=[])
        assert str(exception_info.value) == "BitList must define LIMIT"

    def test_instantiation_success(self) -> None:
        """Instantiation succeeds with any number of items up to LIMIT."""
        instance = BitList8(data=[Boolean(True), Boolean(False), Boolean(1), Boolean(0)])
        assert len(instance) == 4
        expected_bitlist = BitList8(
            data=[Boolean(True), Boolean(False), Boolean(True), Boolean(False)]
        )
        assert instance == expected_bitlist

    def test_instantiation_from_generator(self) -> None:
        """Variable-length type materializes a generator into a list before validation."""
        bit_generator = (Boolean(bit) for bit in [True, False, True])
        instance = BitList8(data=bit_generator)  # type: ignore[arg-type]
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
            BitList8(data=non_iterable)
        assert str(exception_info.value) == f"Expected iterable, got {type_name}"

    @pytest.mark.parametrize("rejected", ["0101", b"\x00\x01"])
    def test_instantiation_from_str_or_bytes_raises(self, rejected: Any) -> None:
        """str and bytes are iterable but explicitly rejected — their elements are not booleans."""
        type_name = type(rejected).__name__
        with pytest.raises((SSZTypeError, ValidationError)) as exception_info:
            BitList8(data=rejected)
        assert str(exception_info.value) == f"Expected iterable, got {type_name}"

    def test_instantiation_over_limit_raises_error(self) -> None:
        """Input exceeding LIMIT raises with the exact size in the message."""

        class BitList4(BitList):
            LIMIT = 4

        with pytest.raises(ValueOrValidationError) as exception_info:
            BitList4(data=[Boolean(bit) for bit in [True, False, True, False, True]])
        assert str(exception_info.value) == "BitList4 exceeds limit of 4, got 5"

    def test_pydantic_validation_accepts_valid_list(self) -> None:
        """Pydantic validation accepts a valid list of booleans."""
        bits = [Boolean(True), Boolean(False), Boolean(True), Boolean(False)]
        instance = BitList8Model(value={"data": bits})  # type: ignore[arg-type]
        assert isinstance(instance.value, BitList8)
        assert len(instance.value) == 4

    def test_pydantic_validation_rejects_oversized_list(self) -> None:
        """Pydantic validation rejects lists exceeding the limit."""
        invalid_value = {"data": [Boolean(True)] * 9}
        with pytest.raises(ValueOrValidationError):
            BitList8Model(value=invalid_value)  # type: ignore[arg-type]

    def test_get_item_int(self) -> None:
        """Indexing by int returns the Boolean at that position."""
        bitlist = BitList8(data=[Boolean(True), Boolean(False), Boolean(True)])
        assert bitlist[0] == Boolean(True)
        assert bitlist[1] == Boolean(False)
        assert bitlist[2] == Boolean(True)

    def test_get_item_slice(self) -> None:
        """Indexing by slice returns a list of Booleans."""
        bitlist = BitList8(data=[Boolean(True), Boolean(False), Boolean(True), Boolean(False)])
        sliced_bits = bitlist[1:3]
        assert sliced_bits == [Boolean(False), Boolean(True)]
        assert isinstance(sliced_bits, list)

    def test_a_partial_fill_resolves_positions_against_the_bits_held(self) -> None:
        """A position counted from the end measures the bits held, not the capacity."""
        bitlist = BitList8(data=bits_of(1, 0, 1))

        # 3 bits held under a capacity of 8:
        #
        #     position from the start:   0  1  2
        #     bits:                      1  0  1
        #     position from the end:    -3 -2 -1
        assert bitlist[-1] == Boolean(True)
        assert bitlist[-3] == Boolean(True)

        # The five further bits the capacity allows for are not part of the value.
        # They appear only as padding inside the Merkle tree.
        # Neither the position just past the last bit nor the one just before the first
        # therefore addresses anything.
        with pytest.raises(IndexError):
            _ = bitlist[3]
        with pytest.raises(IndexError):
            _ = bitlist[-4]

    def test_add_with_list(self) -> None:
        """Concatenating a BitList with a list returns a new instance."""
        bitlist = BitList8(data=[Boolean(True), Boolean(False), Boolean(True)])
        concatenated = bitlist + [Boolean(False), Boolean(True)]
        assert len(concatenated) == 5
        assert list(concatenated.data) == [
            Boolean(True),
            Boolean(False),
            Boolean(True),
            Boolean(False),
            Boolean(True),
        ]
        assert isinstance(concatenated, BitList8)

    def test_add_with_bitlist(self) -> None:
        """Concatenating two BitLists of the same type returns a new instance."""
        bitlist1 = BitList8(data=[Boolean(True), Boolean(False)])
        bitlist2 = BitList8(data=[Boolean(True), Boolean(True)])
        concatenated = bitlist1 + bitlist2
        assert len(concatenated) == 4
        assert list(concatenated.data) == [
            Boolean(True),
            Boolean(False),
            Boolean(True),
            Boolean(True),
        ]
        assert isinstance(concatenated, BitList8)

    def test_add_with_unsupported_type_raises(self) -> None:
        """Adding an unsupported type returns NotImplemented and Python raises TypeError."""
        bitlist = BitList8(data=[Boolean(True)])
        with pytest.raises(TypeError):
            _ = bitlist + 42

    def test_add_exceeding_limit_raises_error(self) -> None:
        """Concatenation beyond LIMIT raises with the exact size in the message."""

        class BitList4(BitList):
            LIMIT = 4

        bitlist = BitList4(data=[Boolean(True), Boolean(False), Boolean(True)])
        with pytest.raises(ValueOrValidationError) as exception_info:
            _ = bitlist + [Boolean(False), Boolean(True)]
        assert str(exception_info.value) == "BitList4 exceeds limit of 4, got 5"


class TestProgressiveBitList:
    """Tests for the uncapped ProgressiveBitList type."""

    def test_instantiation_success(self) -> None:
        """Instantiation succeeds with any number of bit-like items."""
        instance = ProgressiveBitList(data=[Boolean(True), Boolean(False), Boolean(1), Boolean(0)])

        assert len(instance) == 4
        assert instance == ProgressiveBitList(data=bits_of(1, 0, 1, 0))

    def test_default_value_is_empty(self) -> None:
        """The default value is the empty bitlist."""
        assert len(ProgressiveBitList()) == 0
        assert ProgressiveBitList() == ProgressiveBitList(data=())

    def test_instantiation_from_generator(self) -> None:
        """A generator is materialized into a list before validation."""
        bit_generator = (Boolean(bit) for bit in [True, False, True])
        instance = ProgressiveBitList(data=bit_generator)  # type: ignore[arg-type]

        assert len(instance) == 3

    def test_no_bit_count_is_ever_rejected(self) -> None:
        """No capacity is declared, so any bit count validates."""
        instance = ProgressiveBitList(data=[Boolean(True)] * 4096)

        assert len(instance) == 4096

    def test_no_limit_is_declared(self) -> None:
        """The shape carries no capacity attribute at all."""
        assert not hasattr(ProgressiveBitList, "LIMIT")

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
            ProgressiveBitList(data=non_iterable)
        assert str(exception_info.value) == f"Expected iterable, got {type_name}"

    @pytest.mark.parametrize("rejected", ["0101", b"\x00\x01"])
    def test_instantiation_from_str_or_bytes_raises(self, rejected: Any) -> None:
        """str and bytes are iterable but explicitly rejected — their elements are not booleans."""
        type_name = type(rejected).__name__
        with pytest.raises((SSZTypeError, ValidationError)) as exception_info:
            ProgressiveBitList(data=rejected)
        assert str(exception_info.value) == f"Expected iterable, got {type_name}"

    def test_pydantic_validation_accepts_any_bit_count(self) -> None:
        """Pydantic validation accepts a bit list of any width."""
        instance = ProgressiveBitListModel(value={"data": [Boolean(True)] * 300})  # type: ignore[arg-type]

        assert isinstance(instance.value, ProgressiveBitList)
        assert len(instance.value) == 300

    def test_get_item_int(self) -> None:
        """Indexing by int returns the Boolean at that position."""
        bitlist = ProgressiveBitList(data=bits_of(1, 0, 1))

        assert bitlist[0] == Boolean(True)
        assert bitlist[1] == Boolean(False)
        assert bitlist[-1] == Boolean(True)

    def test_get_item_slice(self) -> None:
        """Indexing by slice returns a list of Booleans."""
        bitlist = ProgressiveBitList(data=bits_of(1, 0, 1, 0))
        sliced_bits = bitlist[1:3]

        assert sliced_bits == [Boolean(False), Boolean(True)]
        assert isinstance(sliced_bits, list)

    def test_add_with_list(self) -> None:
        """Concatenating with a plain list coerces the right-hand values."""
        concatenated = ProgressiveBitList(data=bits_of(1, 0, 1)) + [Boolean(False), Boolean(True)]

        assert concatenated == ProgressiveBitList(data=bits_of(1, 0, 1, 0, 1))
        assert isinstance(concatenated, ProgressiveBitList)

    def test_add_with_progressive_bitlist(self) -> None:
        """Concatenating two progressive bitlists yields a fresh instance of the same type."""
        concatenated = ProgressiveBitList(data=bits_of(1, 0)) + ProgressiveBitList(
            data=bits_of(1, 1)
        )

        assert concatenated == ProgressiveBitList(data=bits_of(1, 0, 1, 1))

    def test_add_with_bounded_bitlist_keeps_the_left_shape(self) -> None:
        """Both bitlist shapes share the concatenation hook; the left operand's type wins."""
        concatenated = ProgressiveBitList(data=bits_of(1)) + BitList8(data=bits_of(0, 1))

        assert concatenated == ProgressiveBitList(data=bits_of(1, 0, 1))
        assert isinstance(concatenated, ProgressiveBitList)

    def test_add_with_unsupported_type_raises(self) -> None:
        """Adding an unsupported type returns NotImplemented and Python raises TypeError."""
        bitlist = ProgressiveBitList(data=bits_of(1))

        with pytest.raises(TypeError):
            _ = bitlist + 42

    def test_add_never_overflows_a_capacity(self) -> None:
        """Concatenation has no capacity to overflow, so it always revalidates cleanly."""
        base = ProgressiveBitList(data=[Boolean(True)] * 500)

        assert len(base + base) == 1000

    def test_progressive_bitlist_item_assignment_revalidates(self) -> None:
        """Item assignment replaces the bit through full revalidation."""
        bitlist = ProgressiveBitList(data=bits_of(1, 0))
        bitlist[0] = Boolean(False)
        assert bitlist == ProgressiveBitList(data=bits_of(0, 0))

    def test_progressive_bitlist_grows_without_a_capacity(self) -> None:
        """Append and pop work, and no capacity bounds the growth."""
        bitlist = ProgressiveBitList(data=bits_of(1))
        bitlist.append(Boolean(False))
        assert bitlist == ProgressiveBitList(data=bits_of(1, 0))
        assert bitlist.pop() == Boolean(False)
        assert bitlist == ProgressiveBitList(data=bits_of(1))

    def test_progressive_bitlist_appends_past_a_bounded_limit(self) -> None:
        """Growth runs past the bit count a bounded bitlist of the same shape refuses."""
        bounded = BitList8(data=bits_of(1, 1, 1, 1, 1, 1, 1, 1))
        with pytest.raises(ValueOrValidationError):
            bounded.append(Boolean(True))

        # The same shape with no capacity keeps going, well past that limit.
        bitlist = ProgressiveBitList(data=())
        for _ in range(100):
            bitlist.append(Boolean(True))
        assert len(bitlist) == 100
        assert bitlist == ProgressiveBitList(data=[Boolean(True)] * 100)

    def test_progressive_bitlist_slice_assignment_resizes(self) -> None:
        """Slice assignment replaces a range, and may change the bit count either way."""
        bitlist = ProgressiveBitList(data=bits_of(1, 1, 1))
        bitlist[1:] = bits_of(0)
        assert bitlist == ProgressiveBitList(data=bits_of(1, 0))
        bitlist[0:1] = bits_of(0, 1, 1)
        assert bitlist == ProgressiveBitList(data=bits_of(0, 1, 1, 0))

    def test_progressive_bitlist_mutation_coerces_raw_bits(self) -> None:
        """Mutation wraps a raw bool in Boolean, exactly as construction does."""
        bitlist = ProgressiveBitList(data=bits_of(1))
        bitlist.append(False)  # ty: ignore[invalid-argument-type]
        bitlist[0] = False  # ty: ignore[invalid-assignment]
        assert bitlist == ProgressiveBitList(data=bits_of(0, 0))
        assert all(type(bit) is Boolean for bit in bitlist.data)

    def test_progressive_bitlist_mutation_rejects_a_non_bit(self) -> None:
        """A value outside 0 and 1 is refused, leaving the stored bits untouched."""
        bitlist = ProgressiveBitList(data=bits_of(1))
        with pytest.raises(SSZValueError):
            bitlist.append(2)  # ty: ignore[invalid-argument-type]
        assert bitlist == ProgressiveBitList(data=bits_of(1))

    def test_progressive_bitlist_mutation_moves_the_encoding(self) -> None:
        """A mutated bitlist encodes as the bits it now holds, delimiter included."""
        bitlist = ProgressiveBitList(data=bits_of(1, 0, 1))
        bitlist.append(Boolean(True))
        assert bitlist.encode_bytes() == ProgressiveBitList(data=bits_of(1, 0, 1, 1)).encode_bytes()
        assert ProgressiveBitList.decode_bytes(bitlist.encode_bytes()) == bitlist

    def test_is_variable_size_with_no_fixed_byte_length(self) -> None:
        """The shape reports variable-size and refuses to name a byte width."""
        assert ProgressiveBitList.is_fixed_size() is False
        with pytest.raises(SSZTypeError) as exception_info:
            ProgressiveBitList.get_byte_length()
        assert (
            str(exception_info.value)
            == "ProgressiveBitList: variable-size bitlist has no fixed byte length"
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
        instance = ProgressiveBitList(data=bits_of(*bits))

        encoded = instance.encode_bytes()
        assert encoded.hex() == expected_hex

        assert ProgressiveBitList.decode_bytes(encoded) == instance

        stream = io.BytesIO()
        written = instance.serialize(stream)
        assert written == len(encoded)
        stream.seek(0)
        assert ProgressiveBitList.deserialize(stream, scope=written) == instance

    def test_decode_accepts_any_bit_count(self) -> None:
        """A bit count a bounded bitlist would reject decodes without complaint."""
        # Bytes [0xFF, 0xFF, 0x01] mean 16 data bits with the delimiter at bit 16.
        assert ProgressiveBitList.decode_bytes(b"\xff\xff\x01") == ProgressiveBitList(
            data=[Boolean(True)] * 16
        )

    def test_decode_empty_bytes(self) -> None:
        """Decoding rejects an empty byte sequence — the empty bitlist still costs a byte."""
        with pytest.raises(SSZSerializationError) as exception_info:
            ProgressiveBitList.decode_bytes(b"")
        assert str(exception_info.value) == "ProgressiveBitList: cannot decode empty bytes"

    def test_decode_all_zero_bytes(self) -> None:
        """Decoding rejects input with no 1 bits — there is no delimiter to locate."""
        with pytest.raises(SSZSerializationError) as exception_info:
            ProgressiveBitList.decode_bytes(b"\x00")
        assert str(exception_info.value) == "ProgressiveBitList: no delimiter bit found"

    def test_decode_rejects_non_canonical_trailing_zero_byte(self) -> None:
        """Decoding rejects a trailing zero byte after the delimiter byte."""
        with pytest.raises(SSZSerializationError) as exception_info:
            ProgressiveBitList.decode_bytes(b"\x0d\x00")
        assert (
            str(exception_info.value)
            == "ProgressiveBitList: non-canonical trailing zero bytes after delimiter"
        )

    def test_deserialize_premature_end(self) -> None:
        """Deserializing rejects a stream that ends before the declared scope."""
        stream = io.BytesIO(b"\xff")
        with pytest.raises(SSZSerializationError) as exception_info:
            ProgressiveBitList.deserialize(stream, scope=2)
        assert str(exception_info.value) == "ProgressiveBitList: expected 2 bytes, got 1"

    def test_bytes_match_the_bounded_bitlist_encoding(self) -> None:
        """The wire format matches a bounded bitlist of the same bits, delimiter included."""
        bits = bits_of(1, 0, 1)
        progressive = ProgressiveBitList(data=bits)
        bounded = BitList8(data=bits)

        assert progressive.encode_bytes() == bounded.encode_bytes()
        # The same bytes therefore decode under either shape.
        assert BitList8.decode_bytes(progressive.encode_bytes()) == bounded
        assert ProgressiveBitList.decode_bytes(bounded.encode_bytes()) == progressive


class TestBitfieldSSZ:
    """SSZ interface methods and end-to-end serialization round-trips."""

    def test_bitvector_is_fixed_size(self) -> None:
        """BitVector reports fixed-size and computes byte length via ceil(LENGTH / 8)."""

        class BitVector10(BitVector):
            LENGTH = 10

        assert BitVector10.is_fixed_size() is True
        assert BitVector10.get_byte_length() == 2

    def test_bitlist_is_variable_size(self) -> None:
        """BitList reports variable-size and get_byte_length raises."""

        class BitList10(BitList):
            LIMIT = 10

        assert BitList10.is_fixed_size() is False
        with pytest.raises(SSZTypeError) as exception_info:
            BitList10.get_byte_length()
        assert (
            str(exception_info.value) == "BitList10: variable-size bitlist has no fixed byte length"
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
        """BitVector round-trips through encode_bytes, decode_bytes, and stream serialization."""

        class TestBitVector(BitVector):
            LENGTH = length

        boolean_bits = tuple(Boolean(bit) for bit in bits)
        instance = TestBitVector(data=boolean_bits)

        encoded = instance.encode_bytes()
        assert encoded.hex() == expected_hex

        decoded = TestBitVector.decode_bytes(encoded)
        assert decoded == instance

        stream = io.BytesIO()
        written = instance.serialize(stream)
        assert written == TestBitVector.get_byte_length()
        stream.seek(0)
        decoded2 = TestBitVector.deserialize(stream, scope=written)
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
        """BitList round-trips through encode_bytes, decode_bytes, and stream serialization."""

        class TestBitList(BitList):
            LIMIT = limit

        boolean_bits = tuple(Boolean(bit) for bit in bits)
        instance = TestBitList(data=boolean_bits)

        encoded = instance.encode_bytes()
        assert encoded.hex() == expected_hex

        decoded = TestBitList.decode_bytes(encoded)
        assert decoded == instance

        stream = io.BytesIO()
        written = instance.serialize(stream)
        assert written == len(encoded)
        stream.seek(0)
        decoded2 = TestBitList.deserialize(stream, scope=written)
        assert decoded2 == instance

    def test_bitvector_decode_invalid_length(self) -> None:
        """BitVector.decode_bytes rejects inputs whose byte count is wrong."""

        class BitVector8(BitVector):
            LENGTH = 8

        with pytest.raises(SSZValueError) as exception_info:
            BitVector8.decode_bytes(b"\x01\x02")
        assert str(exception_info.value) == "BitVector8: expected 1 bytes, got 2"

    def test_bitvector_decode_rejects_non_zero_padding_bits(self) -> None:
        """BitVector.decode_bytes rejects a final byte with set bits above the data bits."""

        class BitVector5(BitVector):
            LENGTH = 5

        # Bits 5, 6, 7 are padding above the 5 data bits and must be zero.
        # 0b11111111 sets them, so it is a non-canonical encoding of [1] * 5.
        with pytest.raises(SSZValueError) as exception_info:
            BitVector5.decode_bytes(b"\xff")
        assert str(exception_info.value) == "BitVector5: non-zero padding bits in final byte 0xff"

    def test_bitvector_decode_canonical_with_zero_padding_bits(self) -> None:
        """BitVector.decode_bytes accepts the canonical encoding with zero padding bits."""

        class BitVector5(BitVector):
            LENGTH = 5

        # 0b00011111 holds 5 data bits all set with zero padding above them.
        assert BitVector5.decode_bytes(b"\x1f") == BitVector5(data=[Boolean(True)] * 5)

    def test_bitvector_deserialize_invalid_scope(self) -> None:
        """BitVector.deserialize rejects a scope mismatching the type's byte length."""

        class BitVector8(BitVector):
            LENGTH = 8

        stream = io.BytesIO(b"\xff")
        with pytest.raises(SSZSerializationError) as exception_info:
            BitVector8.deserialize(stream, scope=2)
        assert str(exception_info.value) == "BitVector8: expected 1 bytes, got 2"

    def test_bitvector_deserialize_premature_end(self) -> None:
        """BitVector.deserialize rejects a stream that ends before the declared scope."""

        class BitVector16(BitVector):
            LENGTH = 16

        stream = io.BytesIO(b"\xff")
        with pytest.raises(SSZSerializationError) as exception_info:
            BitVector16.deserialize(stream, scope=2)
        assert str(exception_info.value) == "BitVector16: expected 2 bytes, got 1"

    def test_bitlist_decode_empty_bytes(self) -> None:
        """BitList.decode_bytes rejects an empty byte sequence."""

        class BitList8(BitList):
            LIMIT = 8

        with pytest.raises(SSZSerializationError) as exception_info:
            BitList8.decode_bytes(b"")
        assert str(exception_info.value) == "BitList8: cannot decode empty bytes"

    def test_bitlist_decode_all_zero_bytes(self) -> None:
        """BitList.decode_bytes rejects non-empty input with no 1 bits — no delimiter to locate."""

        class BitList8(BitList):
            LIMIT = 8

        with pytest.raises(SSZSerializationError) as exception_info:
            BitList8.decode_bytes(b"\x00")
        assert str(exception_info.value) == "BitList8: no delimiter bit found"

    def test_bitlist_decode_rejects_non_canonical_trailing_zero_byte(self) -> None:
        """BitList.decode_bytes rejects a trailing zero byte after the delimiter byte."""

        class BitList8(BitList):
            LIMIT = 8

        # Byte 0x0d encodes bits [1, 0, 1] with the delimiter at bit 3.
        # Appending a zero byte leaves the delimiter in byte 0, not the final byte.
        with pytest.raises(SSZSerializationError) as exception_info:
            BitList8.decode_bytes(b"\x0d\x00")
        assert (
            str(exception_info.value)
            == "BitList8: non-canonical trailing zero bytes after delimiter"
        )

    def test_bitlist_decode_canonical_encoding_round_trips(self) -> None:
        """BitList.decode_bytes accepts the canonical single-byte encoding of bits [1, 0, 1]."""

        class BitList8(BitList):
            LIMIT = 8

        assert BitList8.decode_bytes(b"\x0d") == BitList8(
            data=(Boolean(True), Boolean(False), Boolean(True))
        )

    def test_bitlist_decode_exceeds_limit(self) -> None:
        """BitList.decode_bytes rejects encodings whose recovered bit count exceeds LIMIT."""

        class BitList8(BitList):
            LIMIT = 8

        # Bytes [0xFF, 0xFF, 0x01] mean 16 data bits + delimiter at bit 16 — > LIMIT=8.
        with pytest.raises(SSZValueError) as exception_info:
            BitList8.decode_bytes(b"\xff\xff\x01")
        assert str(exception_info.value) == "BitList8 exceeds limit of 8, got 16"

    def test_bitlist_deserialize_premature_end(self) -> None:
        """BitList.deserialize rejects a stream that ends before the declared scope."""

        class BitList16(BitList):
            LIMIT = 16

        stream = io.BytesIO(b"\xff")
        with pytest.raises(SSZSerializationError) as exception_info:
            BitList16.deserialize(stream, scope=2)
        assert str(exception_info.value) == "BitList16: expected 2 bytes, got 1"


class TestBitfieldDefaults:
    """The default value of each of the three bitfield shapes, and the zeroed check over it."""

    def test_bitvector_default_clears_every_bit(self) -> None:
        """The spec gives a bitvector the default of LENGTH clear bits."""
        assert BitVector4() == BitVector4(data=bits_of(0, 0, 0, 0))
        assert len(BitVector4()) == 4

    def test_bitvector_empty_input_stays_a_length_error(self) -> None:
        """Zero bits is a count mismatch against LENGTH, never a request for the default."""
        with pytest.raises(ValueOrValidationError) as exception_info:
            BitVector4(data=[])
        assert str(exception_info.value) == "BitVector4 requires exactly 4 elements, got 0"

    def test_bitvector_data_is_no_longer_a_required_field(self) -> None:
        """The bits carry a default, so Pydantic itself reports them as optional."""
        assert BitVector4.model_fields["data"].is_required() is False

    @pytest.mark.parametrize(
        "bitvector_type, expected_message",
        [
            pytest.param(BitVector, "BitVector must define LENGTH", id="the_base_itself"),
            pytest.param(
                LengthlessBitVector, "LengthlessBitVector must define LENGTH", id="a_subclass"
            ),
        ],
    )
    def test_a_bitvector_without_a_length_reports_its_own_declaration_error(
        self, bitvector_type: type[BitVector], expected_message: str
    ) -> None:
        """No bit count means no bits to clear, so the declaration error comes first."""
        # The default is injected only once a length is declared, so a shape without one
        # keeps the inherited empty default and trips its own check on the way through.
        with pytest.raises(SSZTypeError) as exception_info:
            bitvector_type()
        assert str(exception_info.value) == expected_message

    def test_each_bitvector_default_holds_its_own_bit_sequence(self) -> None:
        """Bitfields mutate in place, so two defaults must not share one sequence."""
        first = BitVector4()
        first[0] = Boolean(True)
        # The bits themselves are immutable, so only the sequence holding them can alias.
        assert first == BitVector4(data=bits_of(1, 0, 0, 0))
        assert BitVector4() == BitVector4(data=bits_of(0, 0, 0, 0))

    def test_bitlist_default_is_empty(self) -> None:
        """A variable-size shape defaults to its empty value, so it holds no bit at all."""
        assert BitList8() == BitList8(data=())
        assert len(BitList8()) == 0

    def test_progressive_bitlist_default_is_empty(self) -> None:
        """The unbounded shape defaults to empty on the same terms."""
        assert ProgressiveBitList() == ProgressiveBitList(data=())
        assert len(ProgressiveBitList()) == 0

    def test_each_bitlist_default_holds_its_own_bit_sequence(self) -> None:
        """Appending to one empty default leaves the next one empty."""
        first = BitList8()
        first.append(Boolean(True))
        assert first == BitList8(data=bits_of(1))
        assert BitList8() == BitList8(data=())

    @pytest.mark.parametrize(
        "default_value, non_default_value",
        [
            # A cleared bit is the default; setting bit 0 moves away from it.
            pytest.param(BitVector4(), BitVector4(data=bits_of(1, 0, 0, 0)), id="bitvector"),
            # An empty bitlist is the default; one clear bit is a different value of length 1.
            pytest.param(BitList8(), BitList8(data=bits_of(0)), id="bitlist"),
            pytest.param(
                ProgressiveBitList(), ProgressiveBitList(data=bits_of(0)), id="progressive_bitlist"
            ),
        ],
    )
    def test_is_zero_holds_only_for_the_default(
        self, default_value: Any, non_default_value: Any
    ) -> None:
        """A default reads as zeroed and any other value of the same type does not."""
        assert default_value.is_zero() is True
        assert non_default_value.is_zero() is False

    @pytest.mark.parametrize(
        "default_value, expected_encoding",
        [
            # Four clear bits pack into one byte of zeros.
            pytest.param(BitVector4(), b"\x00", id="bitvector"),
            # An empty bitlist is the delimiter bit alone.
            pytest.param(BitList8(), b"\x01", id="bitlist"),
            pytest.param(ProgressiveBitList(), b"\x01", id="progressive_bitlist"),
        ],
    )
    def test_the_default_round_trips(self, default_value: Any, expected_encoding: bytes) -> None:
        """Each default encodes to a known byte and decodes back unchanged."""
        assert default_value.encode_bytes() == expected_encoding
        assert type(default_value).decode_bytes(expected_encoding) == default_value


@given(bits=st.lists(st.booleans(), max_size=8))
def test_bitlist_round_trip_random_bits(bits: list[bool]) -> None:
    """Any bit pattern up to the limit, including empty, round-trips unchanged."""
    instance = BitList8(data=tuple(Boolean(bit) for bit in bits))
    assert BitList8.decode_bytes(instance.encode_bytes()) == instance


@given(bits=st.lists(st.booleans(), min_size=4, max_size=4))
def test_bitvector_round_trip_random_bits(bits: list[bool]) -> None:
    """Any fixed-length bit pattern round-trips unchanged."""
    instance = BitVector4(data=tuple(Boolean(bit) for bit in bits))
    assert BitVector4.decode_bytes(instance.encode_bytes()) == instance


@given(bits=st.lists(st.booleans(), max_size=300))
def test_progressive_bitlist_round_trip_random_bits(bits: list[bool]) -> None:
    """Any bit pattern round-trips unchanged, at any width and across chunk boundaries."""
    instance = ProgressiveBitList(data=tuple(Boolean(bit) for bit in bits))
    assert ProgressiveBitList.decode_bytes(instance.encode_bytes()) == instance


@given(bits=st.lists(st.booleans(), max_size=8))
def test_progressive_and_bounded_bitlist_encode_identically(bits: list[bool]) -> None:
    """The two bitlist shapes agree bit for bit on every pattern they both hold."""
    typed_bits = tuple(Boolean(bit) for bit in bits)
    progressive_bytes = ProgressiveBitList(data=typed_bits).encode_bytes()

    assert progressive_bytes == BitList8(data=typed_bits).encode_bytes()
